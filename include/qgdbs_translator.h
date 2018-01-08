#ifndef QGDBS_TRANSLATOR_H
#define QGDBS_TRANSLATOR_H

#include "expr_tool.h"
#include "log.h"

class qgdbs_translator {
private:
        z3::expr m_formula;
        z3::context& m_ctx;

        std::vector<z3::expr> m_first_order_vars;
        std::vector<z3::expr> m_second_order_vars;
        std::vector<int> m_fovar_ctx; //  [0: +, 1: -]
        std::vector<int> m_sovar_ctx;
        std::vector<z3::expr> m_bounds;
        int m_bctx;

        std::vector<z3::expr> m_ctx_items; // [index(ectx) : item]

        int plus_one_foctx();
        int plus_one_soctx();
        int plus_one_ctx();

        void init_ctx();

private:
        // void get_first_order_vars(z3::expr exp, std::set<z3::expr, exprcomp>& vars_set);
        int get_fo_ctx(z3::expr exp, std::vector<z3::expr>& bounds, int b_ctx);
        int get_fo_ctx(z3::expr exp);

        bool has_quantified_var(z3::expr delta, std::set<z3::expr, exprcomp>& var_set);
        z3::expr translate_formula(z3::expr formula);
        z3::expr translate_formula_plus(z3::expr formula);
        z3::expr translate_formula_minus(z3::expr formula);
        z3::expr translate_qgdbs_minus(z3::expr t_i_1, std::string R, int c);
        z3::expr translate_qgdbs_minus(z3::expr t_i_1, std::string R, z3::expr t_i_2, int c);
public:
qgdbs_translator(z3::context& z3_ctx, z3::expr formula):m_ctx(z3_ctx), m_formula(formula), m_bctx(0) {}



        z3::expr get_formula();

};



#endif /* QGDBS_TRANSLATOR_H */
