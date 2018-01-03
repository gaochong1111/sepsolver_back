#ifndef QGDBS_TRANSLATOR_H
#define QGDBS_TRANSLATOR_H

#include "expr_tool.h"
#include "log.h"

class qgdbs_translator {
private:
        z3::expr m_formula;
        z3::context& m_ctx;
        std::vector<z3::expr> m_first_order_vars;
        std::vector<z3::expr> m_ctx_items; // [index(ctx) : item]
        int m_fovar_ctx; // bits: 000111 [0: +, 1: -]

private:
        // void get_first_order_vars(z3::expr exp, std::set<z3::expr, exprcomp>& vars_set);
        int get_fo_ctx(z3::expr exp, int ctx, std::vector<z3::expr>& bounds, int b_ctx);

        z3::expr translate_formula(z3::expr formula, std::vector<z3::expr>& bounds, int b_ctx);
        z3::expr translate_atom_plus(z3::expr atom, std::vector<z3::expr>& bounds, int b_ctx);
        z3::expr translate_atom_minus(z3::expr atom, std::vector<z3::expr>& bounds, int b_ctx);
        z3::expr translate_formula_plus(z3::expr formula, std::vector<z3::expr>& bounds, int b_ctx);
        z3::expr translate_formula_minus(z3::expr formula, std::vector<z3::expr>& bounds, int b_ctx);
public:
qgdbs_translator(z3::context& z3_ctx, z3::expr formula):m_ctx(z3_ctx), m_formula(formula) {}



        z3::expr get_formula();

};



#endif /* QGDBS_TRANSLATOR_H */
