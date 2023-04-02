#include <cctype>
#include <cstdio>
#include <cstdlib>
#include <map>
#include <memory>
#include <string>
#include <utility>
#include <vector>

enum Token 
{
    TOK_EOF = -1,
    TOK_DEF = -2,
    TOK_EXTERN = -3,
    TOK_IDENTIFIER = -4,
    TOK_NUMBER = -5
};

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
    class ExprAST
    {
        public:
            virtual ~ExprAST() = default;
    };

    class NumberExprAST : public ExprAST
    {
        double val;

        public:
            NumberExprAST(double val) : val(val) {}
    };

    class VariableExprAST : public ExprAST 
    {
        std::string name;

        public:
            VariableExprAST(const std::string &name) : name(name) {}
    };

    class BinaryExprAST : public ExprAST 
    {
        char op;
        std::unique_ptr<ExprAST> lhs, rhs;

        public:
            BinaryExprAST(char op, std::unique_ptr<ExprAST> lhs, std::unique_ptr<ExprAST> rhs)
                : op(op), lhs(std::move(lhs)), rhs(std::move(rhs)) {}
    };

    class CallExprAST : public ExprAST 
    {
        std::string callee;
        std::vector<std::unique_ptr<ExprAST>> args;

        public:
        CallExprAST(const std::string &callee, std::vector<std::unique_ptr<ExprAST>> args)
            : callee(callee), args(std::move(args)) {}
    };

    class PrototypeAST 
    {
        std::string name;
        std::vector<std::string> args;

        public:
        PrototypeAST(const std::string &name, std::vector<std::string> args)
            : name(name), args(std::move(args)) {}

        const std::string &getName() const { return name; }
    };

    class FunctionAST 
    {
        std::unique_ptr<PrototypeAST> proto;
        std::unique_ptr<ExprAST> body;

        public:
        FunctionAST(std::unique_ptr<PrototypeAST> proto, std::unique_ptr<ExprAST> body)
            : proto(std::move(proto)), body(std::move(body)) {}
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

    return std::make_unique<CallExprAST>(id_name, std::move(args));
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
    default:
        return log_error("unknown token when expecting an expression");
    }
}


static std::unique_ptr<ExprAST> parse_binop_rhs(int expr_prec, std::unique_ptr<ExprAST> lhs) 
{
    while (true) 
    {
        int tok_prec = get_tok_precedence();

        if (tok_prec < expr_prec)
            return lhs;

        int binop = cur_tok;
        get_next_token();

        auto rhs = parse_primary();
        if (!rhs)
            return nullptr;
            
        int next_prec = get_tok_precedence();
        if (tok_prec < next_prec) 
        {
            rhs = parse_binop_rhs(tok_prec + 1, std::move(rhs));
            if (!rhs)
                return nullptr;
        }

        lhs = std::make_unique<BinaryExprAST>(binop, std::move(lhs), std::move(rhs));
    }
}

static std::unique_ptr<ExprAST> parse_expression()
{
    auto lhs = parse_primary();
    if(!lhs)
        return nullptr;
    
    return parse_binop_rhs(0, std::move(lhs));
}

static std::unique_ptr<PrototypeAST> parse_prototype() 
{
    if (cur_tok != Token::TOK_IDENTIFIER)
        return log_error_p("expected function name in prototype");

    std::string function_name = identifier_str;
    get_next_token();

    if (cur_tok != '(')
        return log_error_p("expected '(' in prototype");

    std::vector<std::string> arg_names;
    while (get_next_token() == Token::TOK_IDENTIFIER)
        arg_names.push_back(identifier_str);

    if (cur_tok != ')')
        return log_error_p("expected ')' in prototype");

    get_next_token(); 

    return std::make_unique<PrototypeAST>(function_name, std::move(arg_names));
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
    if(auto e = parse_expression())
    {
        auto proto = std::make_unique<PrototypeAST>("__anon_expr", std::vector<std::string>());

        return std::make_unique<FunctionAST>(std::move(proto), std::move(e));
    }

    return nullptr;
}

static std::unique_ptr<PrototypeAST> parse_extern()
{
    get_next_token();
    return parse_prototype();
}

static void handle_definition() 
{
    if (parse_definition()) 
    {
        fprintf(stderr, "parsed a function definition.\n");
    } 
    else 
    {
        get_next_token();
    }
}

static void handle_extern() 
{
    if (parse_extern()) 
    {
        fprintf(stderr, "parsed an extern\n");
    } 
    else 
    {
        get_next_token();
    }
}

static void handle_top_level_expression() 
{
    if (parse_top_level_expr()) 
    {
        fprintf(stderr, "parsed a top-level expr\n");
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

int main()
{
    binop_precedence['<'] = 10;
    binop_precedence['+'] = 20;
    binop_precedence['-'] = 20;
    binop_precedence['*'] = 40;

    fprintf(stderr, "ready> ");
    get_next_token();

    main_loop();

    return 0;
}