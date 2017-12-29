#include "qgdbs_translator.h"

z3::expr qgdbs_translator::get_formula() {
        // 1. get first order vars
        std::set<z3::expr, exprcomp> vars_set;
        get_first_order_vars(m_formula, vars_set);
        expr_tool::expr_set_to_vec(vars_set, m_first_order_vars);
        int num = m_first_order_vars.size();
        int LIMIT = 1<<num;

        m_fovar_ctx = 0; // 0000
        while(m_fovar_ctx < LIMIT) {
                std::vector<z3::expr> bounds;
                int b_ctx = 0;
                z3::expr or_i = translate_formula(m_formula, bounds, b_ctx);

                m_ctx_items.push_back(or_i);
                m_fovar_ctx++;
        }

        return m_ctx.bool_val(true);
}


/**
 * translate formula into tr_ctx(formula)
 * @param formula : formula
 * @param bounds : bound var
 * @param b_ctx : bound var ctx
 * @return tr(formula)
 */
z3::expr qgdbs_translator::translate_formula(z3::expr formula, std::vector<z3::expr>& bounds, int b_ctx) {
        z3::expr result = m_ctx.bool_val(true);

        if (formula.is_app()) {
                if (expr_tool::is_fun(formula, "and")) {
                        // and
                        z3::expr_vector items(m_ctx);
                        for (int i=0; i<formula.num_args(); i++) {
                                z3::expr item = translate_formula(formula.arg(i), bounds, b_ctx);
                                items.push_back(item);
                        }
                        result = z3::mk_and(items);
                } else if (expr_tool::is_fun(formula, "not")) {
                        // not
                        result = !translate_formula(formula.arg(0), bounds, b_ctx);
                } else if (expr_tool::is_setint(formula.arg(1))) {
                        // second order
                        z3::expr tr_minus0 =  translate_formula_minus(formula.arg(0), bounds, b_ctx);
                        z3::expr tr_minus1 =  translate_formula_minus(formula.arg(1), bounds, b_ctx);

                        z3::expr tr_plus0 =  translate_formula_plus(formula.arg(0), bounds, b_ctx);
                        z3::expr tr_plus1 =  translate_formula_plus(formula.arg(1), bounds, b_ctx);
                        if (expr_tool::is_fun(formula, "=")) {
                                // ==
                                z3::expr eq_1 = tr_minus0 == tr_minus1;
                                z3::expr eq_2 = tr_plus0 == tr_plus1;
                                result = eq_1 && eq_2;
                        } else if(expr_tool::is_fun(formula, "subset")) {
                                // subset
                                z3::expr subset1 = expr_tool::mk_binary_bool(m_ctx, "subset", tr_minus0, tr_minus1);
                                z3::expr subset2 = expr_tool::mk_binary_bool(m_ctx, "subset", tr_plus0, tr_plus1);

                                result = subset1 && subset2;
                        } else if (expr_tool::is_fun(formula, "belongsto")) {
                                // belongsto
                                if (Z3_ast(tr_minus0) != 0) {
                                        result = expr_tool::mk_belongsto(m_ctx, tr_minus0, tr_minus1);
                                } else if (Z3_ast(tr_plus0) != 0) {
                                        result = expr_tool::mk_belongsto(m_ctx, tr_plus0, tr_plus1);
                                }
                        }
                } else if (formula.arg(1).is_int()) {
                        // first order
                        z3::expr t_i_1 = formula.arg(0);
                        z3::expr t_i_2 = formula.arg(1);
                        int c = 0;
                        std::string R = formula.decl().name().str();
                        int case_i = 0; // bit1: t_i_2 is const? bit0: c<0?
                        if (t_i_2.num_args() == 2) {
                                // t_i_2 = t_i + c | c + c
                                c = t_i_2.arg(1).get_numeral_int();
                                t_i_2 = t_i_2.arg(1);
                                if (expr_tool::is_constant(t_i_2)) {
                                        c += t_i_2.get_numeral_int();
                                        case_i += 2;
                                }
                                if (c < 0) {
                                        // table 3
                                        case_i += 1;
                                }
                        } else {
                                // t_i_2 = t_i | c
                                if (expr_tool::is_constant(t_i_2)) {
                                        c = t_i_2.get_numeral_int();
                                        case_i += 2;
                                }

                                if (c < 0) {
                                        case_i += 1;
                                }
                        }

                        if (case_i == 0) {
                                // table 1
                                // t_i_1, R, c
                        } else if(case_i == 1) {
                                // table 2
                                // t_i_1, R, c
                        } else if (case_i == 2) {
                                // table 3
                                // t_i_1 R, t_i_2 c
                        } else {
                                // table 4
                                // t_i_1 R, t_i_2 c
                        }
                }
        } else if (formula.is_quantifier()) {
                // forall
                z3::expr body = formula.body();
                int size = bounds.size();
                int bnum = Z3_get_quantifier_num_bound(Z3_context(m_ctx), Z3_ast(formula));
                z3::expr_vector pars(m_ctx);
                for (int i=bnum-1; i>=0; i--) {
                        Z3_symbol sym = Z3_get_quantifier_bound_name(Z3_context(m_ctx), Z3_ast(formula), i);
                        Z3_sort sym_s = Z3_get_quantifier_bound_sort(Z3_context(m_ctx), Z3_ast(formula), i);
                        Z3_ast x = Z3_mk_const(Z3_context(m_ctx), sym, sym_s);
                        z3::expr bound(m_ctx, x);
                        bounds.push_back(bound);
                        pars.push_back(bound);
                }

                int NUM = 1<<pars.size();
                int i=0;
                z3::expr_vector all_items(m_ctx);
                int new_ctx = 0;
                while(i < NUM) {
                        new_ctx = (i<<size) | b_ctx;
                        z3::expr body_p = translate_formula(body, bounds, new_ctx);
                        all_items.push_back(z3::forall(pars, body_p)); // new items
                }
                result = z3::mk_and(all_items);
        }
        return result;

}


/**
 * get first order var exp ctx [+, -]
 * @param exp : first order var
 * @param ctx : default ctx
 * @param bounds : bound var
 * @param b_ctx : bound var ctx
 * @return 0[+], 1[-]
 */
int qgdbs_translator::get_fo_ctx(z3::expr exp, int ctx , std::vector<z3::expr>& bounds, int b_ctx) {
        int index = expr_tool::index_of_exp(exp, bounds);
        // exp is bound var
        if (index != -1) return b_ctx & (1<<index);

        // exp is first order var
        index = expr_tool::index_of_exp(exp, m_first_order_vars);
        if (index == -1) return ctx; // exp
        return (m_fovar_ctx & (1<<index));
}


/**
 * translate atom into tr+(atom)
 * @param atom : atom formula
 * @param bounds : bound var
 * @param b_ctx : bound var ctx
 * @return tr+(atom)
 */
z3::expr qgdbs_translator::translate_atom_plus(z3::expr atom, std::vector<z3::expr>& bounds, int b_ctx) {
        return m_ctx.bool_val(true);
}

/**
 * translate atom into tr-(atom)
 * @param atom : atom formula
 * @param bounds : bound var
 * @param b_ctx : bound var ctx
 * @return tr-(atom)
 */
z3::expr qgdbs_translator::translate_atom_minus(z3::expr atom, std::vector<z3::expr>& bounds, int b_ctx) {
        return m_ctx.bool_val(true);

}

/**
 * translate formula into tr+(formula)
 * @param atom : sub formula
 * @param bounds : bound var
 * @param b_ctx : bound var ctx
 * @return tr+(formula)
 */
z3::expr qgdbs_translator::translate_formula_plus(z3::expr formula, std::vector<z3::expr>& bounds, int b_ctx) {
        return m_ctx.bool_val(true);

}

/**
 * translate formula into tr+(formula)
 * @param atom : sub formula
 * @param bounds : bound var
 * @param b_ctx : bound var ctx
 * @return tr+(formula)
 */
z3::expr qgdbs_translator::translate_formula_minus(z3::expr formula, std::vector<z3::expr>& bounds, int b_ctx) {
        return m_ctx.bool_val(true);

}

/**
 * get first order vars in exp
 * @param exp: formula
 * @param vars_set : result
 */
void qgdbs_translator::get_first_order_vars(z3::expr exp, std::set<z3::expr, exprcomp> &vars_set) {
        if (exp.is_app()) {
                if (exp.is_const() && !expr_tool::is_constant(exp)) {
                        if (exp.get_sort().to_string() == "Int")
                            vars_set.insert(exp);
                } else {
                        for (int i=0; i<exp.num_args(); i++) {
                                get_first_order_vars(exp.arg(i), vars_set);
                        }
                }
        }
}
