#include <iostream>
#include <sstream>
#include <fstream>
#include "smt2scanner.h"
#include "smt2parser.h"
#include "qgdbs_translator.h"
#include "mona_translator.h"

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


void test_qgdbs_translator() {
        z3::context ctx;
        z3::expr_vector pars(ctx);
        z3::expr S1 = expr_tool::mk_set_var(ctx, "S1");
        z3::expr S2 = expr_tool::mk_set_var(ctx, "S2");
        z3::expr x = ctx.int_const("x");
        z3::expr y = ctx.int_const("y");
        z3::expr x_set = expr_tool::mk_single_set(ctx, x);
        z3::expr S3 = expr_tool::mk_binary_set(ctx, "setunion", S1, x_set);
        z3::expr min_s1 = expr_tool::mk_min_max(ctx, 0, S1);
        z3::expr max_s1 = expr_tool::mk_min_max(ctx, 1, S1);
        z3::expr min_s2 = expr_tool::mk_min_max(ctx, 0, S2);
        z3::expr max_s2 = expr_tool::mk_min_max(ctx, 1, S2);
        z3::expr body =  x >= y+1;

        pars.push_back(S1);
        pars.push_back(S2);
        //pars.push_back(x);
        //pars.push_back(y);

        z3::expr all = z3::forall(pars, body);
        std::cout << "formual: " << all << std::endl;

        // translate into N
        qgdbs_translator translator(ctx, all);
        translator.generate_formula();
        for (int i=0; i<translator.formula_size(); i++) {
                z3::expr f_ps_qgdbs_n = translator.get_formula(i);
                std::cout << "f_ps_qgdbs_n: " << f_ps_qgdbs_n << std::endl;
        }
}


int main(int argc, char *argv[])
{
        if (argc>0) {
                file_name = argv[1];
                std::cout << "file_name: " << file_name << std::endl;
        }

        test();

        //test_qgdbs_translator();

        return 0;
}
