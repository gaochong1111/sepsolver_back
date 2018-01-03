#include "qgdbs_translator.h"

z3::expr qgdbs_translator::get_formula() {
        // 1. get first order vars
        std::set<z3::expr, exprcomp> vars_set;
        expr_tool::get_first_order_vars(m_formula, vars_set);
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
        int index = expr_tool::rindex_of_exp(exp, bounds);
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

        // second order var
        int ctx_atom = get_fo_ctx(atom, -1, bounds, b_ctx);
        if (ctx_atom == -1) {
        }

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
        Log log;
        z3::expr empty = expr_tool::mk_emptyset(m_ctx);

        // atom
        // [first order ]
        if (formula.get_sort().to_string() == "Int") {
                // first order var
                if (expr_tool::is_int_const(formula)) {
                        if (formula.is_numeral()) {
                                // constant
                                int c = formula.get_numeral_int();
                                if (c>=0) {
                                        return formula;
                                } else {
                                        // ctx non-consistent
                                        return empty;
                                }
                        } else {
                                // variable
                                int ctx_v = get_fo_ctx(formula, -1, bounds, b_ctx);
                                if (ctx_v == -1 || ctx_v == 1) {
                                        return empty;
                                } else {
                                        std::string name = log.string_format("%s_plus", formula.to_string());
                                        return m_ctx.int_const(name.c_str());
                                }
                        }
                }
                // (min ) (max )
                if (expr_tool::is_fun(formula, "min")) {
                        z3::expr ts = translate_formula_plus(formula.arg(0), bounds, b_ctx);
                        if (expr_tool::is_fun(ts, "emptyset")) {
                                // TODO UNDEF
                        }
                        return expr_tool::mk_min_max(m_ctx, 0, ts);
                }
                if (expr_tool::is_fun(formula, "max")) {
                        z3::expr ts = translate_formula_plus(formula.arg(0), bounds, b_ctx);
                        if (expr_tool::is_fun(ts, "emptyset")) {
                                // TODO UNDEF
                        }
                        return expr_tool::mk_min_max(m_ctx, 1, ts);
                }
        }


        // [second order]
        // emptyset
        if (expr_tool::is_fun(formula, "emptyset")) {
                return expr_tool::mk_emptyset(m_ctx);
        }
        // set var
        if (expr_tool::is_setint(formula)) {
                std::string name = log.string_format("%s_plus", formula.to_string());
                return expr_tool::mk_set_var(m_ctx, name);
        }
        // (set int)
        if (expr_tool::is_fun(formula, "set")) {
                z3::expr element = translate_formula_plus(formula.arg(0), bounds, b_ctx); // first order
                if (expr_tool::is_fun(element, "emptyset")) {
                        return expr_tool::mk_emptyset(m_ctx);
                } else {
                        return expr_tool::mk_single_set(m_ctx, element);
                }
        }


        // (setunion ) (setintersect ) (setminus )
        if (expr_tool::is_fun(formula, "setunion")) {
                z3::expr ts1 = translate_formula_plus(formula.arg(0), bounds, b_ctx);
                z3::expr ts2 = translate_formula_plus(formula.arg(1), bounds, b_ctx);

                return expr_tool::mk_binary_set(m_ctx, "setunion", ts1, ts2);
        }

        if (expr_tool::is_fun(formula, "setintersect")) {
                z3::expr ts1 = translate_formula_plus(formula.arg(0), bounds, b_ctx);
                z3::expr ts2 = translate_formula_plus(formula.arg(1), bounds, b_ctx);

                return expr_tool::mk_binary_set(m_ctx, "setintersect", ts1, ts2);
        }

        if (expr_tool::is_fun(formula, "setminus")) {
                z3::expr ts1 = translate_formula_plus(formula.arg(0), bounds, b_ctx);
                z3::expr ts2 = translate_formula_plus(formula.arg(1), bounds, b_ctx);

                return expr_tool::mk_binary_set(m_ctx, "setminus", ts1, ts2);
        }

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

