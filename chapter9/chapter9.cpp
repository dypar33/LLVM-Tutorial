#include "../include/KaleidoscopeJIT.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/Analysis/BasicAliasAnalysis.h"
#include "llvm/Analysis/Passes.h"
#include "llvm/IR/DIBuilder.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/Host.h"
#include "llvm/Transforms/Scalar.h"
#include <cctype>
#include <cstdio>
#include <map>
#include <string>
#include <vector>

using namespace llvm;
using namespace llvm::orc;
using namespace llvm::sys;

enum Token 
{
    TOK_EOF = -1,
    TOK_DEF = -2,
    TOK_EXTERN = -3,
    TOK_IDENTIFIER = -4,
    TOK_NUMBER = -5,
    TOK_IF = -6,
    TOK_THEN = -7,
    TOK_ELSE = -8,
    TOK_FOR = -9,
    TOK_IN = -10,
    TOK_BINARY = -11,
    TOK_UNARY = -12,
    TOK_VAR = -13
};

std::string get_tok_name(int Tok) 
{
  switch (Tok) 
  {
    case Token::TOK_EOF:
        return "eof";
    case Token::TOK_DEF:
        return "def";
    case Token::TOK_EXTERN:
        return "extern";
    case Token::TOK_IDENTIFIER:
        return "identifier";
    case Token::TOK_NUMBER:
        return "number";
    case Token::TOK_IF:
        return "if";
    case Token::TOK_THEN:
        return "then";
    case Token::TOK_ELSE:
        return "else";
    case Token::TOK_FOR:
        return "for";
    case Token::TOK_IN:
        return "in";
    case Token::TOK_BINARY:
        return "binary";
    case Token::TOK_UNARY:
        return "unary";
    case Token::TOK_VAR:
        return "var";
  }

  return std::string(1, (char)Tok);
}

namespace 
{
    class PrototypeAST;
    class ExprAST;
}

struct DebugInfo 
{
    DICompileUnit *the_cu;
    DIType *dblty;
    std::vector<DIScope *> lexical_blocks;

    void emit_location(ExprAST *ast);
    DIType *get_double_ty();
} ks_dbg_info;

struct SourceLocation 
{
    int line;
    int col;
};

static SourceLocation cur_loc;
static SourceLocation lex_loc = {1, 0};

static int advance() 
{
    int last_char = getchar();

    if (last_char == '\n' || last_char == '\r') 
    {
        lex_loc.line++;
        lex_loc.col = 0;
    } 
    else
        lex_loc.col++;
            
    return last_char;
}

static std::string identifier_str;
static double num_val;

static int get_tok()
{
    static int last_char = ' ';

    while(isspace(last_char))
        last_char = getchar();

    if(isalpha(last_char))
    {
        identifier_str = last_char;

        while(isalnum((last_char = getchar())))
            identifier_str += last_char;

        if(identifier_str == "def")
            return Token::TOK_DEF;
        if(identifier_str == "extern")
            return Token::TOK_EXTERN;
        if(identifier_str == "if")
            return Token::TOK_IF;
        if(identifier_str == "then")
            return Token::TOK_THEN;
        if(identifier_str == "else")
            return Token::TOK_ELSE;
        if(identifier_str == "for")
            return Token::TOK_FOR;
        if(identifier_str == "in")
            return Token::TOK_IN;
        if(identifier_str == "binary")
            return Token::TOK_BINARY;
        if(identifier_str == "unary")
            return Token::TOK_UNARY;
        if(identifier_str == "var")
            return Token::TOK_VAR;

        return Token::TOK_IDENTIFIER;
    }

    if(isdigit(last_char) || last_char == '.')
    {
        std::string num_str;

        do
        {
            num_str += last_char;
            last_char = getchar();
        } while (isdigit(last_char) || last_char == '.');
        
        num_val = strtod(num_str.c_str(), nullptr);

        return Token::TOK_NUMBER;
    }

    if(last_char == '#')
    {
        do
        {
            last_char = getchar();
        } while (last_char != EOF && last_char != '\n' && last_char != '\r');
        
        if(last_char != EOF)
            return get_tok();
    }

    if(last_char == EOF)
        return Token::TOK_EOF;

    int this_char = last_char;

    last_char = getchar();

    return this_char;
}

namespace 
{
    raw_ostream &indent(raw_ostream &O, int size) 
    {
        return O << std::string(size, ' ');
    }

    class ExprAST
    {
        SourceLocation loc;

        public:
            ExprAST(SourceLocation loc = cur_loc) : loc(loc) {}
            virtual ~ExprAST() = default;

            virtual Value *codegen() = 0;
            int get_line() const { return loc.line; }
            int get_col() const { return loc.col; }
            virtual raw_ostream &dump(raw_ostream &out, int ind) 
            {
                return out << ':' << get_line() << ':' << get_col() << '\n';
            }
    };

    class NumberExprAST : public ExprAST
    {
        double val;

        public:
            NumberExprAST(double val) : val(val) {}

            Value *codegen() override;
            raw_ostream &dump(raw_ostream &out, int ind) override 
            {
                return ExprAST::dump(out << val, ind);
            }
    };

    class VariableExprAST : public ExprAST 
    {
        std::string name;

        public:
            VariableExprAST(const std::string &name) : name(name) {}

            Value *codegen() override;
            const std::string &get_name() const { return name; }
            raw_ostream &dump(raw_ostream &out, int ind) override 
            {
                return ExprAST::dump(out << name, ind);
            }
    };

    class UnaryExprAST : public ExprAST 
    {
        char opcode;
        std::unique_ptr<ExprAST> operand;

        public:
            UnaryExprAST(char opcode, std::unique_ptr<ExprAST> operand) : opcode(opcode), operand(std::move(operand)) {}

            Value *codegen() override;
            raw_ostream &dump(raw_ostream &out, int ind) override 
            {
                ExprAST::dump(out << "unary" << opcode, ind);

                operand->dump(out, ind + 1);

                return out;
            }
    };

    class BinaryExprAST : public ExprAST 
    {
        char op;
        std::unique_ptr<ExprAST> lhs, rhs;

        public:
            BinaryExprAST(SourceLocation loc, char op, std::unique_ptr<ExprAST> lhs, std::unique_ptr<ExprAST> rhs)
                : ExprAST(loc), op(op), lhs(std::move(lhs)), rhs(std::move(rhs)) {}

            Value *codegen() override;
            raw_ostream &dump(raw_ostream &out, int ind) override 
            {
                ExprAST::dump(out << "binary" << op, ind);

                lhs->dump(indent(out, ind) << "LHS:", ind + 1);
                rhs->dump(indent(out, ind) << "RHS:", ind + 1);

                return out;
            }
    };

    class CallExprAST : public ExprAST 
    {
        std::string callee;
        std::vector<std::unique_ptr<ExprAST>> args;

        public:
            CallExprAST(SourceLocation loc, const std::string &callee, std::vector<std::unique_ptr<ExprAST>> args)
                : ExprAST(loc), callee(callee), args(std::move(args)) {}

            Value *codegen() override;

            raw_ostream &dump(raw_ostream &out, int ind) override 
            {
                ExprAST::dump(out << "call " << callee, ind);

                for (const auto &arg : args)
                    arg->dump(indent(out, ind + 1), ind + 1);

                return out;
            }
    };

    class IfExprAST : public ExprAST
    {
        std::unique_ptr<ExprAST> cond, then, _else;

        public:
            IfExprAST(SourceLocation loc, std::unique_ptr<ExprAST> cond, std::unique_ptr<ExprAST> then, std::unique_ptr<ExprAST> _else)
                : ExprAST(loc), cond(std::move(cond)), then(std::move(then)), _else(std::move(_else)) {}

            Value *codegen() override; 
            raw_ostream &dump(raw_ostream &out, int ind) override 
            {
                ExprAST::dump(out << "if", ind);

                cond->dump(indent(out, ind) << "Cond:", ind + 1);
                then->dump(indent(out, ind) << "Then:", ind + 1);
                _else->dump(indent(out, ind) << "Else:", ind + 1);

                return out;
            }
            
    };

    class ForExprAST : public ExprAST
    {
        std::string var_name;
        std::unique_ptr<ExprAST> start, end, step, body;

        public:
            ForExprAST(const std::string &var_name, std::unique_ptr<ExprAST> start, std::unique_ptr<ExprAST> end, 
            std::unique_ptr<ExprAST> step, std::unique_ptr<ExprAST> body)
                : var_name(var_name), start(std::move(start)), end(std::move(end)), step(std::move(step)), body(std::move(body)) {}

            Value *codegen() override; 
            raw_ostream &dump(raw_ostream &out, int ind) override 
            {
                ExprAST::dump(out << "for", ind);

                start->dump(indent(out, ind) << "Cond:", ind + 1);
                end->dump(indent(out, ind) << "End:", ind + 1);
                step->dump(indent(out, ind) << "Step:", ind + 1);
                body->dump(indent(out, ind) << "Body:", ind + 1);

                return out;
            }
    };

    class VarExprAST : public ExprAST
    {
        std::vector<std::pair<std::string, std::unique_ptr<ExprAST>>> var_names;
        std::unique_ptr<ExprAST> body;

        public:
            VarExprAST(std::vector<std::pair<std::string, std::unique_ptr<ExprAST>>> var_names, std::unique_ptr<ExprAST> body)
                : var_names(std::move(var_names)), body(std::move(body)) {}

            Value *codegen() override;
            raw_ostream &dump(raw_ostream &out, int ind) override 
            {
                ExprAST::dump(out << "var", ind);

                for (const auto &named_var : var_names)
                    named_var.second->dump(indent(out, ind) << named_var.first << ':', ind + 1);

                body->dump(indent(out, ind) << "Body:", ind + 1);

                return out;
            }
    };

    class PrototypeAST 
    {
        std::string name;
        std::vector<std::string> args;

        bool is_operator;
        unsigned precedence;
        int line;

        public:
            PrototypeAST(SourceLocation loc, const std::string &name, std::vector<std::string> args, bool is_operator=false, unsigned precedence=0)
                : name(name), args(std::move(args)), is_operator(is_operator), precedence(precedence), line(loc.line) {}

            Function *codegen();
            const std::string &getName() const { return name; }

            bool is_unary_op() const { return is_operator && args.size() == 1; }
            bool is_binary_op() const { return is_operator && args.size() == 2; }
            unsigned get_binary_precedence() const { return precedence; }

            char get_operator_name() const 
            {
                assert(is_unary_op() || is_binary_op());

                return name[name.size() - 1];
            }

            int get_line() const { return line; } 
    };

    class FunctionAST 
    {
        std::unique_ptr<PrototypeAST> proto;
        std::unique_ptr<ExprAST> body;

        public:
            FunctionAST(std::unique_ptr<PrototypeAST> proto, std::unique_ptr<ExprAST> body)
                : proto(std::move(proto)), body(std::move(body)) {}
            
            Function *codegen();
            raw_ostream &dump(raw_ostream &out, int ind) 
            {
                indent(out, ind) << "FunctionAST\n";
                ++ind;
                indent(out, ind) << "Body:";

                return body ? body->dump(out, ind) : out << "null\n";
            }
    };
}

static int cur_tok;
static int get_next_token() { return cur_tok = get_tok(); }

static std::map<char, int> binop_precedence;

static int get_tok_precedence()
{
    if(!isascii(cur_tok))
        return -1;

    int tok_prec = binop_precedence[cur_tok];
    if(tok_prec <= 0)
        return -1;
    
    return tok_prec;
}

std::unique_ptr<ExprAST> log_error(const char *message)
{
    fprintf(stderr, "Error: %s\n", message);
    
    return nullptr;
}

std::unique_ptr<PrototypeAST> log_error_p(const char *message)
{
    log_error(message);

    return nullptr;
}

static std::unique_ptr<ExprAST> parse_expression();

static std::unique_ptr<ExprAST> parse_number_expr()
{
    auto result = std::make_unique<NumberExprAST>(num_val);
    get_next_token();

    return std::move(result);
}

static std::unique_ptr<ExprAST> parse_paren_expr()
{
    get_next_token();

    auto v = parse_expression();
    if(!v)
        return nullptr;

    if(cur_tok != ')')
        return log_error("expected ')");
    
    get_next_token();

    return v;
}

static std::unique_ptr<ExprAST> parse_identifier_expr()
{
    std::string id_name = identifier_str;
    
    SourceLocation lit_loc = cur_loc;

    get_next_token();

    if(cur_tok != '(')
        return std::make_unique<VariableExprAST>(id_name);

    get_next_token();

    std::vector<std::unique_ptr<ExprAST>> args;

    if(cur_tok != ')')
    {
        while(true)
        {
            if(auto arg = parse_expression())
                args.push_back(std::move(arg));
            else
                return nullptr;

            if(cur_tok == ')')
                break;
            
            if(cur_tok != ',')
                return log_error("expected ')' or ',' in argument list");
            
            get_next_token();
        }
    }

    get_next_token();

    return std::make_unique<CallExprAST>(lit_loc, id_name, std::move(args));
}

static std::unique_ptr<ExprAST> parse_if_expr()
{
    SourceLocation if_loc = cur_loc;

    get_next_token();

    auto cond = parse_expression();
    if(!cond)
        return nullptr;

    if(cur_tok != Token::TOK_THEN)
        return log_error("expected then");
    get_next_token();

    auto then = parse_expression();
    if(!then)
        return nullptr;

    if(cur_tok != Token::TOK_ELSE)
        return log_error("expected else");

    get_next_token();

    auto _else = parse_expression();
    if(!_else)
        return nullptr;

    return std::make_unique<IfExprAST>(if_loc, std::move(cond), std::move(then), std::move(_else));
}

static std::unique_ptr<ExprAST> parse_for_expr()
{
    get_next_token();

    if (cur_tok != Token::TOK_IDENTIFIER)
        return log_error("expected identifier after for");

    std::string id_name = identifier_str;
    get_next_token();

    if (cur_tok != '=')
        return log_error("expected '=' after for");

    get_next_token();

    auto start = parse_expression();
    if (!start)
        return nullptr;

    if (cur_tok != ',')
        return log_error("expected ',' after for start value");

    get_next_token();

    auto end = parse_expression();
    if (!end)
        return nullptr;

    std::unique_ptr<ExprAST> step;
    if (cur_tok == ',') {
        get_next_token();

        step = parse_expression();
        if (!step)
            return nullptr;
    }

    if (cur_tok != Token::TOK_IN)
        return log_error("expected 'in' after for");

    get_next_token();

    auto body = parse_expression();
    if (!body)
        return nullptr;

    return std::make_unique<ForExprAST>(id_name, std::move(start), std::move(end), std::move(step), std::move(body));
}

static std::unique_ptr<ExprAST> parse_var_expr() 
{
    get_next_token();

    std::vector<std::pair<std::string, std::unique_ptr<ExprAST>>> var_names;

    if (cur_tok != Token::TOK_IDENTIFIER)
        return log_error("expected identifier after var");

    while (true) 
    {
        std::string name = identifier_str;
        get_next_token();

        std::unique_ptr<ExprAST> init = nullptr;
        if (cur_tok == '=') {
            get_next_token(); // eat the '='.

            init = parse_expression();
            if (!init)
                return nullptr;
        }

        var_names.push_back(std::make_pair(name, std::move(init)));

        if (cur_tok != ',')
            break;

        get_next_token(); 

        if (cur_tok != Token::TOK_IDENTIFIER)
            return log_error("expected identifier list after var");
    }

    if (cur_tok != Token::TOK_IN)
        return log_error("expected 'in' keyword after 'var'");

    get_next_token(); 

    auto body = parse_expression();
    if (!body)
        return nullptr;

    return std::make_unique<VarExprAST>(std::move(var_names), std::move(body));
}

static std::unique_ptr<ExprAST> parse_primary() 
{
    switch (cur_tok) 
    {
    case Token::TOK_IDENTIFIER:
        return parse_identifier_expr();
    case Token::TOK_NUMBER:
        return parse_number_expr();
    case '(':
        return parse_paren_expr();
    case Token::TOK_IF:
        return parse_if_expr();
    case Token::TOK_FOR:
        return parse_for_expr();
    case Token::TOK_VAR:
        return parse_var_expr();
    default:
        return log_error("unknown token when expecting an expression");
    }
}

static std::unique_ptr<ExprAST> parse_unary()
{
    if(!isascii(cur_tok) || cur_tok == '(' || cur_tok == ',')
        return parse_primary();
    
    int opc = cur_tok;

    get_next_token();
    
    if(auto operand = parse_unary())
        return std::make_unique<UnaryExprAST>(opc, std::move(operand));
    
    return nullptr;
}

static std::unique_ptr<ExprAST> parse_binop_rhs(int expr_prec, std::unique_ptr<ExprAST> lhs) 
{
    while (true) 
    {
        int tok_prec = get_tok_precedence();

        if (tok_prec < expr_prec)
            return lhs;

        int binop = cur_tok;
        SourceLocation bin_loc = cur_loc;

        get_next_token();

        auto rhs = parse_unary();
        if (!rhs)
            return nullptr;
            
        int next_prec = get_tok_precedence();
        if (tok_prec < next_prec) 
        {
            rhs = parse_binop_rhs(tok_prec + 1, std::move(rhs));
            if (!rhs)
                return nullptr;
        }

        lhs = std::make_unique<BinaryExprAST>(bin_loc, binop, std::move(lhs), std::move(rhs));
    }
}

static std::unique_ptr<ExprAST> parse_expression()
{
    auto lhs = parse_unary();
    if(!lhs)
        return nullptr;
    
    return parse_binop_rhs(0, std::move(lhs));
}

static std::unique_ptr<PrototypeAST> parse_prototype() 
{
    std::string function_name;

    SourceLocation fn_loc = cur_loc;

    unsigned kind = 0; // 0 : idientifier / 1 : unary / 2 : binary
    unsigned binary_precedence = 30;

    switch(cur_tok)
    {
        case Token::TOK_IDENTIFIER:
            function_name = identifier_str;
            kind = 0;
            get_next_token();
            break;
        case Token::TOK_UNARY:
            get_next_token();
            if(!isascii(cur_tok))
                return log_error_p("expected unary operator");
            
            function_name = "unary";
            function_name += (char)cur_tok;

            kind = 1;

            get_next_token();
            break;
        case Token::TOK_BINARY:
            get_next_token();
            if(!isascii(cur_tok))
                return log_error_p("expected binary operator");
            
            function_name = "binary";
            function_name += (char)cur_tok;

            kind = 2;

            get_next_token();

            if(cur_tok == Token::TOK_NUMBER)
            {
                if(num_val < 1 || num_val > 100)
                    return log_error_p("invalid precedence: must be 1..100");
                
                binary_precedence = (unsigned)num_val;
                get_next_token();
            }
            
            break;
            
        default:
            return log_error_p("expected function name in prototype");
    }

    if (cur_tok != '(')
        return log_error_p("expected '(' in prototype");

    std::vector<std::string> arg_names;
    while (get_next_token() == Token::TOK_IDENTIFIER)
        arg_names.push_back(identifier_str);

    if (cur_tok != ')')
        return log_error_p("expected ')' in prototype");

    get_next_token(); 

    if(kind && arg_names.size() != kind)
        return log_error_p("invalid number of operands for operator");

    return std::make_unique<PrototypeAST>(fn_loc, function_name, arg_names, kind != 0, binary_precedence);
}

static std::unique_ptr<FunctionAST> parse_definition()
{
    get_next_token(); // def

    auto proto = parse_prototype();
    if(!proto)
        return nullptr;

    if(auto e = parse_expression())
        return std::make_unique<FunctionAST>(std::move(proto), std::move(e));

    return nullptr;
}

static std::unique_ptr<FunctionAST> parse_top_level_expr()
{
    SourceLocation fn_loc = cur_loc;

    if(auto e = parse_expression())
    {
        auto proto = std::make_unique<PrototypeAST>(cur_loc, "main", std::vector<std::string>());

        return std::make_unique<FunctionAST>(std::move(proto), std::move(e));
    }

    return nullptr;
}

static std::unique_ptr<PrototypeAST> parse_extern()
{
    get_next_token();
    return parse_prototype();
}

// generate code

static std::unique_ptr<LLVMContext> the_context;
static std::unique_ptr<Module> the_module;
static std::unique_ptr<IRBuilder<>> builder;
static std::map<std::string, AllocaInst*> named_values;

static std::unique_ptr<legacy::FunctionPassManager> the_fpm;
static std::unique_ptr<KaleidoscopeJIT> the_jit;
static std::map<std::string, std::unique_ptr<PrototypeAST>> function_protos;
static ExitOnError exit_on_error;

static std::unique_ptr<DIBuilder> d_builder;

DIType *DebugInfo::get_double_ty()
{
    if(dblty)
        return dblty;

    dblty = d_builder->createBasicType("double", 64, dwarf::DW_ATE_float);

    return dblty;
}

void DebugInfo::emit_location(ExprAST *ast) {
    if (!ast)
        return builder->SetCurrentDebugLocation(DebugLoc());

    DIScope *scope;

    if (lexical_blocks.empty())
        scope = the_cu;
    else
        scope = lexical_blocks.back();

    builder->SetCurrentDebugLocation(DILocation::get(scope->getContext(), ast->get_line(), ast->get_col(), scope));
}

static DISubroutineType *create_function_type(unsigned num_args) 
{
    SmallVector<Metadata *, 8> elt_tys;
    DIType *dblty = ks_dbg_info.get_double_ty();

    elt_tys.push_back(dblty);

    for (unsigned i = 0, e = num_args; i != e; ++i)
        elt_tys.push_back(dblty);

    return d_builder->createSubroutineType(d_builder->getOrCreateTypeArray(elt_tys));
}


Value *log_error_v(const char *message)
{
    log_error(message);

    return nullptr;
}

Function *get_function(std::string name)
{
    if(auto *f = the_module->getFunction(name))
        return f;

    auto fi = function_protos.find(name);
    if(fi != function_protos.end())
        return fi->second->codegen();
    
    return nullptr;
}

static AllocaInst *create_entry_block_alloca(Function *the_function, StringRef var_name) 
{
    IRBuilder<> tmp_b(&the_function->getEntryBlock(), the_function->getEntryBlock().begin());
    return tmp_b.CreateAlloca(Type::getDoubleTy(*the_context), nullptr, var_name);
}

Value *NumberExprAST::codegen()
{
    ks_dbg_info.emit_location(this);
    return ConstantFP::get(*the_context, APFloat(val));
}

Value *VariableExprAST::codegen()
{
    AllocaInst *v = named_values[name];

    if(!v)
        return log_error_v("unknown variable name");

    ks_dbg_info.emit_location(this);

    return builder->CreateLoad(v->getAllocatedType(), v, name.c_str());
}

Value *UnaryExprAST::codegen()
{
    Value *operand_v = operand->codegen();
    if(!operand_v)
        return nullptr;

    Function *f = get_function(std::string("unary") + opcode);
    if(!f)
        return log_error_v("unknown unary operator");

    ks_dbg_info.emit_location(this);
    
    return builder->CreateCall(f, operand_v, "unop");
}

Value *BinaryExprAST::codegen()
{
    ks_dbg_info.emit_location(this);

    if (op == '=') 
    {
        VariableExprAST *lhse = static_cast<VariableExprAST *>(lhs.get());
        if (!lhse)
            return log_error_v("destination of '=' must be a variable");
            
        Value *val = rhs->codegen();
        if (!val)
            return nullptr;

        Value *variable = named_values[lhse->get_name()];
        if (!variable)
            return log_error_v("unknown variable name");

        builder->CreateStore(val, variable);

        return val;
    }

    Value *l = lhs->codegen();
    Value *r = rhs->codegen();

    if(!l || !r)
        return nullptr;
    
    switch(op)
    {
        case '+':
            return builder->CreateFAdd(l, r, "addtmp");
        case '-':
            return builder->CreateFSub(l, r, "subtmp");
        case '*':
            return builder->CreateFMul(l, r, "multmp");
        case '<':
            l = builder->CreateFCmpULT(l, r, "cmptmp");

            return builder->CreateUIToFP(l, Type::getDoubleTy(*the_context), "booltmp");
        default:
            break;
    }

    Function *f = get_function(std::string("binary") + op);

    assert(f && "binary operator not found..!");

    Value *ops[] = {l, r};
    return builder->CreateCall(f, ops, "binop");
}

Value *CallExprAST::codegen()
{
    ks_dbg_info.emit_location(this);

    Function *callee_f = get_function(callee);

    if(!callee_f)
        return log_error_v("unknown function referenced");

    if(callee_f->arg_size() != args.size())
        return log_error_v("incorrect # arguments passed");

    std::vector<Value *> args_v;

    for(unsigned i = 0, e = args.size(); i != e; ++i)
    {
        args_v.push_back(args[i]->codegen());
        if(!args_v.back())
            return nullptr;
    }

    return builder->CreateCall(callee_f, args_v, "calltmp");
}

Value *IfExprAST::codegen() 
{
    ks_dbg_info.emit_location(this);

    Value *cond_v = cond->codegen();
    if (!cond_v)
        return nullptr;

    cond_v = builder->CreateFCmpONE(cond_v, ConstantFP::get(*the_context, APFloat(0.0)), "ifcond");

    Function *the_function = builder->GetInsertBlock()->getParent();
    BasicBlock *then_bb = BasicBlock::Create(*the_context, "then", the_function);
    BasicBlock *else_bb = BasicBlock::Create(*the_context, "else");
    BasicBlock *merge_bb = BasicBlock::Create(*the_context, "ifcont");

    builder->CreateCondBr(cond_v, then_bb, else_bb);

    // then
    builder->SetInsertPoint(then_bb);

    Value *then_v = then->codegen();
    if (!then_v)
        return nullptr;

    builder->CreateBr(merge_bb);
    then_bb = builder->GetInsertBlock();

    // else
    the_function->getBasicBlockList().push_back(else_bb);
    builder->SetInsertPoint(else_bb);

    Value *else_v = _else->codegen();
    if (!else_v)
        return nullptr;

    builder->CreateBr(merge_bb);
    else_bb = builder->GetInsertBlock();

    the_function->getBasicBlockList().push_back(merge_bb);
    builder->SetInsertPoint(merge_bb);

    // ph
    PHINode *pn = builder->CreatePHI(Type::getDoubleTy(*the_context), 2, "iftmp");

    pn->addIncoming(then_v, then_bb);
    pn->addIncoming(else_v, else_bb);
    return pn;
}

Value *ForExprAST::codegen() 
{
    Function *the_function = builder->GetInsertBlock()->getParent();

    AllocaInst *alloca = create_entry_block_alloca(the_function, var_name);

    ks_dbg_info.emit_location(this);

    Value *start_v = start->codegen();
    if (!start_v)
        return nullptr;

    builder->CreateStore(start_v, alloca);

    BasicBlock *loop_bb = BasicBlock::Create(*the_context, "loop", the_function);
    builder->CreateBr(loop_bb);

    builder->SetInsertPoint(loop_bb);

    AllocaInst *old_v = named_values[var_name];
    named_values[var_name] = alloca;

    if(!body->codegen())
        return nullptr;
    
    Value *step_v = nullptr;
    if (step) 
    {
        step_v = step->codegen();
        if (!step_v)
            return nullptr;
    } 
    else 
    {
        // else set 1.0
        step_v = ConstantFP::get(*the_context, APFloat(1.0));
    }

    Value *end_cond = end->codegen();
    if (!end_cond)
        return nullptr;

    Value *cur_var = builder->CreateLoad(alloca->getAllocatedType(), alloca, var_name.c_str());
    Value *next_var = builder->CreateFAdd(cur_var, step_v, "nextvar");
    
    builder->CreateStore(next_var, alloca);

    end_cond = builder->CreateFCmpONE(end_cond, ConstantFP::get(*the_context, APFloat(0.0)), "loopcond");

    BasicBlock *after_bb = BasicBlock::Create(*the_context, "afterloop", the_function);

    builder->CreateCondBr(end_cond, loop_bb, after_bb);

    builder->SetInsertPoint(after_bb);

    if (old_v)
        named_values[var_name] = old_v;
    else
        named_values.erase(var_name);

    return Constant::getNullValue(Type::getDoubleTy(*the_context));
}

Value *VarExprAST::codegen()
{
    std::vector<AllocaInst *> old_bindings;

    Function *the_function = builder->GetInsertBlock()->getParent();

    for (unsigned i = 0, e = var_names.size(); i != e; ++i) 
    {
        const std::string &var_name = var_names[i].first;

        ExprAST *init = var_names[i].second.get();
        
        Value *init_val;
        if (init) 
        {
            init_val = init->codegen();

            if (!init_val)
                return nullptr;
        } 
        else
        {
            init_val = ConstantFP::get(*the_context, APFloat(0.0));
        }

        AllocaInst *alloca = create_entry_block_alloca(the_function, var_name);
        builder->CreateStore(init_val, alloca);
        
        old_bindings.push_back(named_values[var_name]);

        named_values[var_name] = alloca;
    }

    ks_dbg_info.emit_location(this);

    Value *body_v = body->codegen();
    if (!body_v)
        return nullptr;

    for (unsigned i = 0, e = var_names.size(); i != e; ++i)
        named_values[var_names[i].first] = old_bindings[i];

    return body_v;
}

Function *PrototypeAST::codegen() 
{
    std::vector<Type *> Doubles(args.size(), Type::getDoubleTy(*the_context));
    FunctionType *ft = FunctionType::get(Type::getDoubleTy(*the_context), Doubles, false);

    Function *f = Function::Create(ft, Function::ExternalLinkage, name, the_module.get());

    unsigned idx = 0;
    for (auto &arg : f->args())
        arg.setName(args[idx++]);

    return f;
}

Function *FunctionAST::codegen() 
{    
    auto &p = *proto;
    function_protos[proto->getName()] = std::move(proto);

    Function *the_function = get_function(p.getName());

    if (!the_function)
        return nullptr;
    
    if(p.is_binary_op())
        binop_precedence[p.get_operator_name()] = p.get_binary_precedence();

    BasicBlock *bb = BasicBlock::Create(*the_context, "entry", the_function);
    builder->SetInsertPoint(bb);

    DIFile *unit = d_builder->createFile(ks_dbg_info.the_cu->getFilename(), ks_dbg_info.the_cu->getDirectory());
    DIScope *f_context = unit;

    unsigned line_no = p.get_line();
    unsigned scope_line = line_no;

    DISubprogram *sp = d_builder->createFunction(f_context, p.getName(), StringRef(), unit, line_no, create_function_type(the_function->arg_size()), scope_line, DINode::FlagPrototyped, DISubprogram::SPFlagDefinition);
    the_function->setSubprogram(sp);

    ks_dbg_info.lexical_blocks.push_back(sp);

    ks_dbg_info.emit_location(nullptr);

    named_values.clear();

    unsigned arg_idx = 0;
    for (auto &arg : the_function->args())
    {
        AllocaInst *alloca = create_entry_block_alloca(the_function, arg.getName());

        DILocalVariable *d =  d_builder->createParameterVariable(sp, arg.getName(), ++arg_idx, unit, line_no, ks_dbg_info.get_double_ty(), true);
        d_builder->insertDeclare(alloca, d, d_builder->createExpression(), DILocation::get(sp->getContext(), line_no, 0, sp), builder->GetInsertBlock());
        
        builder->CreateStore(&arg, alloca);

        named_values[std::string(arg.getName())] = alloca;
    }

    ks_dbg_info.emit_location(body.get());

    if (Value *ret_val = body->codegen()) 
    {
        builder->CreateRet(ret_val);

        ks_dbg_info.lexical_blocks.pop_back();

        verifyFunction(*the_function);

        // the_fpm->run(*the_function);

        return the_function;
    }

    the_function->eraseFromParent();

    if(p.is_binary_op())
        binop_precedence.erase(p.get_operator_name());

    ks_dbg_info.lexical_blocks.pop_back();

    return nullptr;
}

static void initialize_module_and_pass_manager()
{
    the_context = std::make_unique<LLVMContext>();
    the_module = std::make_unique<Module>("my cool jit", *the_context);
    the_module->setDataLayout(the_jit->getDataLayout());

    builder = std::make_unique<IRBuilder<>>(*the_context);
}

static void handle_definition() 
{
    if(auto fn_ast = parse_definition())
    {
        if(!fn_ast->codegen())
        {
            fprintf(stderr, "error reading function definition:");
        }
    }
    else 
    {
        get_next_token();
    }
}

static void handle_extern() 
{
    if(auto proto_ast = parse_extern())
    {
        if(!proto_ast->codegen())
        {
            fprintf(stderr, "error reading extern");
        }
        else
            function_protos[proto_ast->getName()] = std::move(proto_ast);
    }
    else 
    {
        get_next_token();
    }
}

static void handle_top_level_expression() 
{
    if(auto fn_ast = parse_top_level_expr())
    {
        if(!fn_ast->codegen())
            fprintf(stderr, "error generating code for top-level expression");
    }
    else 
    {
        get_next_token();
    }
}

static void main_loop() 
{
    while (true) 
    {
        fprintf(stderr, "ready> ");

        switch (cur_tok) 
        {
        case Token::TOK_EOF:
            return;
        case ';': 
            get_next_token();
            break;
        case Token::TOK_DEF:
            handle_definition();
            break;
        case Token::TOK_EXTERN:
            handle_extern();
            break;
        default:
            handle_top_level_expression();
            break;
        }
    }
}

#ifdef _WIN32
#define DLLEXPORT __declspec(dllexport)
#else
#define DLLEXPORT
#endif

extern "C" DLLEXPORT double putchard(double x) 
{
  fputc((char)x, stderr);
  return 0;
}

extern "C" DLLEXPORT double printd(double x) 
{
  fprintf(stderr, "%f\n", x);
  return 0;
}

int main()
{
    InitializeNativeTarget();
    InitializeNativeTargetAsmPrinter();
    InitializeNativeTargetAsmParser();

    binop_precedence['='] = 2;
    binop_precedence['<'] = 10;
    binop_precedence['+'] = 20;
    binop_precedence['-'] = 20;
    binop_precedence['*'] = 40;

    get_next_token();


    the_jit = exit_on_error(KaleidoscopeJIT::Create());

    initialize_module_and_pass_manager();

    the_module->addModuleFlag(Module::Warning, "Debug Info Version", DEBUG_METADATA_VERSION);

    if (Triple(sys::getProcessTriple()).isOSDarwin())
        the_module->addModuleFlag(llvm::Module::Warning, "Dwarf Version", 2);

    d_builder = std::make_unique<DIBuilder>(*the_module);

    ks_dbg_info.the_cu = d_builder->createCompileUnit(dwarf::DW_LANG_C, d_builder->createFile("fib.ks", "."), "Kaleidoscope Compiler", false, "", 0);

    main_loop();

    d_builder->finalize();

    the_module->print(errs(), nullptr);

    return 0;
}