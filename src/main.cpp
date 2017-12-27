#include <iostream>
#include <sstream>
#include <fstream>
#include "smt2scanner.h"
#include "smt2parser.h"
// #include "sexpr.h"

using namespace std;

string token_str[] = { "NULL_TOKEN",
                       "LEFT_PAREN",
                       "RIGHT_PAREN",
                       "KEYWORD_TOKEN",
                       "SYMBOL_TOKEN",
                       "STRING_TOKEN",
                       "INT_TOKEN",
                       "BV_TOKEN",
                       "FLOAT_TOKEN",
                       "EOF_TOKEN"};

std::string file_name = "test.smt";

void test() {
        try {
                fstream f(file_name);
                z3::context ctx;
                smt2context m_ctx(ctx, "log");
                m_ctx.logger().disable();
                smt2parser parser(m_ctx, f);
                parser();
                // std::cout << "formula: " << m_ctx.get_negf() << std::endl;
        } catch(const smt2exception& e) {
                cout << e.get_msg() << endl;
        }
}

int main(int argc, char *argv[])
{
        if (argc>0) {
                file_name = argv[1];
                std::cout << "file_name: " << file_name << std::endl;
        }

        test();

        return 0;
}
