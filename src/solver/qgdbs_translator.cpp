#include "qgdbs_translator.h"

z3::expr qgdbs_translator::get_formula() {
        // 1. get first order vars
        std::set<z3::expr, exprcomp> fo_vars_set;
        std::set<z3::expr, exprcomp> so_vars_set;

        expr_tool::get_first_order_vars(m_formula, fo_vars_set);
        expr_tool::expr_set_to_vec(fo_vars_set, m_first_order_vars);
        expr_tool::get_second_order_vars(m_formula, so_vars_set);
        expr_tool::expr_set_to_vec(so_vars_set, m_second_order_vars);

        init_ctx();

        do {
                m_bctx = 0;
                z3::expr or_i = translate_formula(m_formula);
                m_ctx_items.push_back(or_i);
        } while (plus_one_ctx());

        return m_ctx.bool_val(true);
}

/**
 * check delta item
 * @param delta: T_i,1 R T_i,2
 * @param var_set: free vars
 * @return true: delta has quantified var
 */
bool qgdbs_translator::has_quantified_var(z3::expr delta, std::set<z3::expr, exprcomp>& var_set) {

        bool result = false;
        if (delta.is_app()) {
                if (delta.is_const() && !expr_tool::is_constant(delta)) {
                        var_set.insert(delta);
                }
                for (int i=0; i<delta.num_args(); i++) {
                        if(has_quantified_var(delta.arg(i), var_set)) result = true;;
                }
        } else if (delta.is_var()) {
                return true;
        }
        return result;
}


/**
 * translate formula into tr_ctx(formula)
 * @param formula : formula
 * @return tr(formula)
 */
z3::expr qgdbs_translator::translate_formula(z3::expr formula) {
        z3::expr result = m_ctx.bool_val(true);

        if (formula.is_app()) {
                if (expr_tool::is_fun(formula, "and")) {
                        // and
                        z3::expr_vector items(m_ctx);
                        for (int i=0; i<formula.num_args(); i++) {
                                z3::expr item = translate_formula(formula.arg(i));
                                items.push_back(item);
                        }
                        result = z3::mk_and(items);
                } else if (expr_tool::is_fun(formula, "not")) {
                        // not
                        result = !translate_formula(formula.arg(0));
                } else if (expr_tool::is_setint(formula.arg(1))) {
                        // second order
                        z3::expr tr_minus0 =  translate_formula_minus(formula.arg(0));
                        z3::expr tr_minus1 =  translate_formula_minus(formula.arg(1));

                        z3::expr tr_plus0 =  translate_formula_plus(formula.arg(0));
                        z3::expr tr_plus1 =  translate_formula_plus(formula.arg(1));

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
                                // belongsto [TODO]
                                if (Z3_ast(tr_minus0) != 0) {
                                        result = expr_tool::mk_belongsto(m_ctx, tr_minus0, tr_minus1);
                                } else if (Z3_ast(tr_plus0) != 0) {
                                        result = expr_tool::mk_belongsto(m_ctx, tr_plus0, tr_plus1);
                                }
                        }
                } else if (formula.arg(1).is_int()) {
                        // first order
                        std::set<z3::expr, exprcomp> var_set;
                        bool has_q = has_quantified_var(formula, var_set);

                        int case_i = 0; // bit1: t_i_2 is const? bit0: c<0?
                        if (has_q) {
                                z3::expr t_i_1 = formula.arg(0);
                                z3::expr t_i_2 = formula.arg(1);
                                int c = 0;
                                std::string R = formula.decl().name().str();
                                if (t_i_2.num_args() == 2) {
                                        // t_i_2 = t_i + c | c + c
                                        if (expr_tool::is_constant(t_i_2.arg(1))) {
                                                c = t_i_2.arg(1).get_numeral_int();
                                                t_i_2 = t_i_2.arg(0);
                                                if (expr_tool::is_constant(t_i_2)) {
                                                        c += t_i_2.get_numeral_int();
                                                        case_i += 2;
                                                }
                                                if (c < 0) {
                                                        // table 3
                                                        case_i += 1;
                                                }
                                        } else {
                                                case_i = 4;
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
                        } else if (case_i == 3){
                                // table 4
                                // t_i_1 R, t_i_2 c
                        } else {
                                // trival
                        }
                }
        } else if (formula.is_quantifier()) {
                // forall
                z3::expr body = formula.body();
                // int size = m_bounds.size();
                z3::expr_vector pars(m_ctx);
                expr_tool::get_pars_quantifier(m_ctx, formula, pars, body);

                z3::expr_vector fo_pars(m_ctx);
                z3::expr_vector so_pars(m_ctx);
                for (int i=0; i<pars.size(); i++) {
                        if (pars[i].is_int()) {
                                fo_pars.push_back(expr_tool::get_plus_exp(m_ctx, pars[i]));
                                fo_pars.push_back(expr_tool::get_minus_exp(m_ctx, pars[i]));

                                m_bounds.push_back(pars[i]);
                        } else {
                                so_pars.push_back(expr_tool::get_plus_exp(m_ctx, pars[i]));
                                so_pars.push_back(expr_tool::get_minus_exp(m_ctx, pars[i]));
                        }
                }

                int size = fo_pars.size() / 2;
                int NUM = 1<<size;
                int i=0;
                z3::expr_vector all_items(m_ctx);
                int b_ctx = m_bctx;

                while(i < NUM) {
                        m_bctx =  i | (b_ctx<<size);
                        //i->expr : TODO
                        z3::expr pre_exp(m_ctx);

                        z3::expr body_p = translate_formula(body);
                        z3::expr imp_exp = z3::implies(pre_exp, body_p);
                        all_items.push_back(imp_exp); // new items
                        i++;
                }
                result = z3::mk_and(all_items);
                // make all

                for (i=0; i<size; i++) m_bounds.pop_back();
                m_bctx = b_ctx;

        }
        return result;

}


/**
 * get first order var exp ctx [+, -]
 * @param exp : first order var
 * @param bounds : bound var
 * @param b_ctx : bound var ctx
 * @return 0[+], 1[-]
 */
int qgdbs_translator::get_fo_ctx(z3::expr exp, std::vector<z3::expr>& bounds, int b_ctx) {
        int index = expr_tool::rindex_of_exp(exp, bounds);
        // exp is bound var
        if (index != -1) return b_ctx & (1<<index);

        // exp is first order var
        index = expr_tool::index_of_exp(exp, m_first_order_vars);
        if (index == -1) return -1; // exp
        return m_fovar_ctx[index];
}


/**
 * get first order var exp ctx [+, -]
 * @param exp : first order var
 * @return 0[+], 1[-]
 */
int qgdbs_translator::get_fo_ctx(z3::expr exp) {
        int index = expr_tool::rindex_of_exp(exp, m_bounds);
        // exp is bound var
        if (index != -1) return m_bctx & (1<<index);

        // exp is first order var
        index = expr_tool::index_of_exp(exp, m_first_order_vars);
        if (index == -1) return -1; // exp
        return m_fovar_ctx[index];
}

void qgdbs_translator::init_ctx() {
        int fo_num = m_first_order_vars.size();
        int so_num = m_second_order_vars.size();
        for (int i=0; i<fo_num; i++) m_fovar_ctx.push_back(0);
        for (int i=0; i<so_num; i++) m_sovar_ctx.push_back(0);
}

/**
 * get next ctx
 * @return plus: 0:yes, 1:no
 */
int qgdbs_translator::plus_one_ctx() {
        if (plus_one_foctx() == 0) return 0;
        if (plus_one_soctx() == 0) return 0;
        return 1;
}

int qgdbs_translator::plus_one_foctx() {
        int c = 1;
        int cur = 0;
        for (int i=m_fovar_ctx.size()-1; i>=0; i--) {
                cur = m_fovar_ctx[i] + c;
                m_fovar_ctx[i] = cur & 1;
                c = cur & 2;
                if (c==0) break;
        }
        return c;
}

int qgdbs_translator::plus_one_soctx() {
        int c = 1;
        int cur = 0;
        for (int i=m_sovar_ctx.size()-1; i>=0; i--) {
                cur = m_sovar_ctx[i] + c;
                c=0;
                m_sovar_ctx[i] = cur;
                if (cur == 3) {
                        c = 1;
                        m_sovar_ctx[i] = 0;
                }
                if (c==0) break;
        }
        return c;
}





/**
 * translate formula into tr+(formula)
 * @param atom : sub formula
 * @return tr+(formula)
 */
z3::expr qgdbs_translator::translate_formula_plus(z3::expr formula) {
        z3::expr empty = expr_tool::mk_emptyset(m_ctx);
        z3::expr min_empty = expr_tool::mk_min_max(m_ctx, 0, empty);

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
                                        return min_empty;
                                }
                        } else {
                                // variable
                                int ctx_v = get_fo_ctx(formula);
                                if (ctx_v == -1 || ctx_v == 1) {
                                        return min_empty;
                                } else {
                                        return expr_tool::get_plus_exp(m_ctx, formula);
                                }
                        }
                }
                // (min ) (max )
                if (expr_tool::is_fun(formula, "min")) {
                        z3::expr ts = translate_formula_plus(formula.arg(0));
                        if (expr_tool::is_fun(ts, "emptyset")) {
                                // TODO UNDEF
                                return min_empty;
                        }
                        return expr_tool::mk_min_max(m_ctx, 0, ts);
                }
                if (expr_tool::is_fun(formula, "max")) {
                        z3::expr ts = translate_formula_plus(formula.arg(0));
                        if (expr_tool::is_fun(ts, "emptyset")) {
                                // TODO UNDEF
                                return min_empty;
                        }
                        return expr_tool::mk_min_max(m_ctx, 1, ts);
                }
        }


        // [second order]
        // emptyset
        if (expr_tool::is_fun(formula, "emptyset")) {
                return empty;
        }
        // set var
        if (expr_tool::is_setint(formula)) {
                int index = expr_tool::index_of_exp(formula, m_second_order_vars);

                if (index != -1) {
                        int ctx = m_sovar_ctx[index];
                        if (ctx == 1) {
                                // ctx = '-'
                                return empty;
                        }
                }
                // context consistent
                return expr_tool::get_plus_exp(m_ctx, formula);
        }
        // (set int)
        if (expr_tool::is_fun(formula, "set")) {
                z3::expr element = translate_formula_plus(formula.arg(0)); // first order
                if (element.hash() == min_empty.hash()) {
                        return empty;
                } else {
                        return expr_tool::mk_single_set(m_ctx, element);
                }
        }


        // (setunion ) (setintersect ) (setminus )
        if (expr_tool::is_fun(formula, "setunion")) {
                z3::expr ts1 = translate_formula_plus(formula.arg(0));
                z3::expr ts2 = translate_formula_plus(formula.arg(1));

                return expr_tool::mk_binary_set(m_ctx, "setunion", ts1, ts2);
        }

        if (expr_tool::is_fun(formula, "setintersect")) {
                z3::expr ts1 = translate_formula_plus(formula.arg(0));
                z3::expr ts2 = translate_formula_plus(formula.arg(1));

                return expr_tool::mk_binary_set(m_ctx, "setintersect", ts1, ts2);
        }

        if (expr_tool::is_fun(formula, "setminus")) {
                z3::expr ts1 = translate_formula_plus(formula.arg(0));
                z3::expr ts2 = translate_formula_plus(formula.arg(1));

                return expr_tool::mk_binary_set(m_ctx, "setminus", ts1, ts2);
        }

        return m_ctx.bool_val(true);
}

/**
 * translate formula into tr+(formula)
 * @param atom : sub formula
 * @return tr+(formula)
 */
z3::expr qgdbs_translator::translate_formula_minus(z3::expr formula) {
        z3::expr empty = expr_tool::mk_emptyset(m_ctx);
        z3::expr min_empty = expr_tool::mk_min_max(m_ctx, 0, empty);

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
                                        return min_empty;
                                }
                        } else {
                                // variable
                                int ctx_v = get_fo_ctx(formula);
                                if (ctx_v == -1 || ctx_v == 0) {
                                        return min_empty;
                                } else {
                                        return expr_tool::get_minus_exp(m_ctx, formula);
                                }
                        }
                }
                // (min ) (max )
                if (expr_tool::is_fun(formula, "min")) {
                        z3::expr ts = translate_formula_minus(formula.arg(0));
                        if (expr_tool::is_fun(ts, "emptyset")) {
                                // TODO UNDEF
                                return min_empty;
                        }
                        return expr_tool::mk_min_max(m_ctx, 1, ts);
                }
                if (expr_tool::is_fun(formula, "max")) {
                        z3::expr ts = translate_formula_minus(formula.arg(0));
                        if (expr_tool::is_fun(ts, "emptyset")) {
                                // TODO UNDEF
                                return min_empty;
                        }
                        return expr_tool::mk_min_max(m_ctx, 0, ts);
                }
        }


        // [second order]
        // emptyset
        if (expr_tool::is_fun(formula, "emptyset")) {
                return empty;
        }
        // set var
        if (expr_tool::is_setint(formula)) {
                int index = expr_tool::index_of_exp(formula, m_second_order_vars);

                if (index != -1) {
                        int ctx = m_sovar_ctx[index];
                        if (ctx == 0) {
                                // ctx = '+'
                                return empty;
                        }
                }
                // context consistent
                return expr_tool::get_minus_exp(m_ctx, formula);
        }
        // (set int)
        if (expr_tool::is_fun(formula, "set")) {
                z3::expr element = translate_formula_minus(formula.arg(0)); // first order
                if (element.hash() == min_empty.hash()) {
                        return empty;
                } else {
                        return expr_tool::mk_single_set(m_ctx, element);
                }
        }


        // (setunion ) (setintersect ) (setminus )
        if (expr_tool::is_fun(formula, "setunion")) {
                z3::expr ts1 = translate_formula_minus(formula.arg(0));
                z3::expr ts2 = translate_formula_minus(formula.arg(1));

                return expr_tool::mk_binary_set(m_ctx, "setunion", ts1, ts2);
        }

        if (expr_tool::is_fun(formula, "setintersect")) {
                z3::expr ts1 = translate_formula_minus(formula.arg(0));
                z3::expr ts2 = translate_formula_minus(formula.arg(1));

                return expr_tool::mk_binary_set(m_ctx, "setintersect", ts1, ts2);
        }

        if (expr_tool::is_fun(formula, "setminus")) {
                z3::expr ts1 = translate_formula_minus(formula.arg(0));
                z3::expr ts2 = translate_formula_minus(formula.arg(1));

                return expr_tool::mk_binary_set(m_ctx, "setminus", ts1, ts2);
        }

        return m_ctx.bool_val(true);
}


/**
 * translate t_i_1 = t_i_2 + c by table 3, 4
 *
 */
z3::expr qgdbs_translator::translate_qgdbs_minus(z3::expr t_i_1, std::string R, z3::expr t_i_2, int c) {
        z3::expr c_exp = m_ctx.int_val(c);
        z3::expr c_minus_exp = m_ctx.int_val(-c);
        z3::expr zero_exp = m_ctx.int_val(0);
        z3::expr empty = expr_tool::mk_emptyset(m_ctx);
        int case_i = 0;

        if (expr_tool::is_int_const(t_i_1) && expr_tool::is_int_const(t_i_2)) {
                // x1 = x2 + c
                int ctx_1 = get_fo_ctx(t_i_1);
                int ctx_2 = get_fo_ctx(t_i_2);
                z3::expr x1_plus = expr_tool::get_plus_exp(m_ctx, t_i_1);
                z3::expr x1_minus = expr_tool::get_minus_exp(m_ctx, t_i_1);
                z3::expr x2_plus = expr_tool::get_plus_exp(m_ctx, t_i_2);
                z3::expr x2_minus = expr_tool::get_minus_exp(m_ctx, t_i_2);
                case_i = ctx_1<<1 + ctx_2;

                if (case_i == 0) {
                        // +, +
                        return expr_tool::mk_item(x1_plus, R, x2_plus, c_exp);

                } else if (case_i == 3) {
                        // -, -
                        return expr_tool::mk_item(x2_minus, R, x1_minus, c_exp);

                } else if (case_i == 1) {
                        // +, -
                        return expr_tool::mk_item(x1_plus+x2_minus, R, zero_exp, c_exp);

                } else {
                        // -, + [NON-DB]
                        if (R == "<=") R = ">=";
                        else if (R == ">=") R = "<=";
                        return expr_tool::mk_item(x2_plus+x1_minus, R, zero_exp, c_minus_exp);
                }
        }

        case_i = 0;
        if (expr_tool::is_fun(t_i_2, "max")) {
                // t_i_2 : min
                case_i += 1;
        }

        if (expr_tool::is_fun(t_i_1, "min")) {
                case_i += 2;
        } else  if (expr_tool::is_fun(t_i_1, "max")) {
                case_i += 4;
        }


        z3::expr ts2_minus = translate_formula_minus(t_i_2.arg(0));
        z3::expr ts2_plus = translate_formula_plus(t_i_2.arg(0));


        if (c >= 0) {
                // table 3
                if (case_i < 2) {
                        int ctx_1 = get_fo_ctx(t_i_1);
                        z3::expr x1_plus = expr_tool::get_plus_exp(m_ctx, t_i_1);
                        z3::expr x1_minus = expr_tool::get_minus_exp(m_ctx, t_i_1);
                        if (case_i == 0) {
                                // x R min(Ts) + c
                                z3::expr min_ts2_plus = expr_tool::mk_min_max(m_ctx, 0, ts2_plus);
                                z3::expr max_ts2_minus = expr_tool::mk_min_max(m_ctx, 1, ts2_minus);

                                if (R == "=" || R == ">=") {
                                        if (ctx_1) {
                                                return expr_tool::mk_item(max_ts2_minus, R, x1_minus, c_exp);
                                        }

                                        z3::expr item1 = (ts2_minus == empty && expr_tool::mk_item(x1_plus, R, min_ts2_plus, c_exp));
                                        z3::expr item2 = (expr_tool::mk_item(x1_plus+max_ts2_minus, R, zero_exp, c_exp)); // NON-DB
                                        return  item1 || item2;
                                } else if (R == "<=") {
                                        if (ctx_1) {
                                                return ts2_minus == empty || expr_tool::mk_item(max_ts2_minus, R, x1_minus, c_exp);
                                        }

                                        z3::expr item1 = (ts2_minus == empty && expr_tool::mk_item(x1_plus, R, min_ts2_plus, c_exp));
                                        z3::expr item2 = (expr_tool::mk_item(x1_plus+max_ts2_minus, R, zero_exp, c_exp)); // NON-DB
                                        return  item1 || item2;
                                }
                        } else if(case_i == 1) {
                                // x R max(Ts) + c
                                z3::expr max_ts2_plus = expr_tool::mk_min_max(m_ctx, 1, ts2_plus);
                                z3::expr min_ts2_minus = expr_tool::mk_min_max(m_ctx, 0, ts2_minus);

                                if (R == "=" || R == "<=") {
                                        if (ctx_1) {
                                                return ts2_minus == empty || expr_tool::mk_item(min_ts2_minus, R, x1_minus, c_exp);
                                        }

                                        z3::expr item1 =  expr_tool::mk_item(x1_plus, R, max_ts2_plus, c_exp);
                                        z3::expr item2 = (ts2_plus==empty && expr_tool::mk_item(x1_plus + min_ts2_minus, R, zero_exp, c_exp)); // NON-DB
                                        return  item1 || item2;
                                } else if (R == ">=") {
                                        if (ctx_1) {
                                                return  expr_tool::mk_item(min_ts2_minus, R, x1_minus, c_exp);
                                        }

                                        z3::expr item1 = expr_tool::mk_item(x1_plus, R, max_ts2_plus, c_exp);
                                        z3::expr item2 = (ts2_plus == empty && expr_tool::mk_item(x1_plus+min_ts2_minus, R, zero_exp, c_exp)); // NON-DB
                                        return  item1 || item2;
                                }

                        }
                } else {
                        // min(Ts) R min(Ts) + c
                        z3::expr ts1_minus = translate_formula_minus(t_i_1.arg(0));
                        z3::expr ts1_plus = translate_formula_plus(t_i_1.arg(0));

                        z3::expr max_ts2_plus = expr_tool::mk_min_max(m_ctx, 1, ts2_plus);
                        z3::expr min_ts2_plus = expr_tool::mk_min_max(m_ctx, 0, ts2_plus);
                        z3::expr max_ts2_minus = expr_tool::mk_min_max(m_ctx, 1, ts2_minus);
                        z3::expr min_ts2_minus = expr_tool::mk_min_max(m_ctx, 0, ts2_minus);

                        z3::expr max_ts1_plus = expr_tool::mk_min_max(m_ctx, 1, ts1_plus);
                        z3::expr min_ts1_plus = expr_tool::mk_min_max(m_ctx, 0, ts1_plus);
                        z3::expr max_ts1_minus = expr_tool::mk_min_max(m_ctx, 1, ts1_minus);
                        z3::expr min_ts1_minus = expr_tool::mk_min_max(m_ctx, 0, ts1_minus);

                        if (case_i == 2) {
                                if (R == "=" || R == ">=") {
                                        z3::expr item1 = ts1_minus == empty && ts2_minus == empty && expr_tool::mk_item(min_ts1_plus, R, min_ts2_plus, c_exp);
                                        z3::expr item2 = ts1_minus == empty && expr_tool::mk_item(min_ts1_plus+max_ts2_minus, R, zero_exp, c_exp); // NON-DB
                                        z3::expr item3 = expr_tool::mk_item(max_ts2_minus, R, max_ts1_minus, c_exp);
                                        return item1 || item2 || item3;
                                } else if (R == "<=") {
                                        z3::expr item1 = ts1_minus == empty && ts2_minus == empty && expr_tool::mk_item(min_ts1_plus, R, min_ts2_plus, c_exp);
                                        z3::expr item2 = ts1_minus == empty && expr_tool::mk_item(min_ts1_plus+max_ts2_minus, R, zero_exp, c_exp); // NON-DB
                                        z3::expr item3 = expr_tool::mk_item(max_ts2_minus, R, max_ts1_minus, c_exp);
                                        z3::expr item4 = ts1_minus != empty && ts2_minus == empty;
                                        return item1 || item2 || item4 || item3;
                                }
                        } else if (case_i == 3) {
                                // min(Ts) R max(Ts) + c
                                if (R == "=" || R == ">=") {
                                        z3::expr item1 = ts1_minus == empty  && expr_tool::mk_item(min_ts1_plus, R, max_ts2_plus, c_exp);
                                        z3::expr item2 = ts1_minus == empty && ts2_plus == empty && expr_tool::mk_item(min_ts1_plus+min_ts2_minus, R, zero_exp, c_exp); // NON-DB
                                        z3::expr item3 = ts2_plus == empty && expr_tool::mk_item(min_ts2_minus, R, max_ts1_minus, c_exp);
                                        return item1 || item2 || item3;
                                } else if (R == "<=") {
                                        z3::expr item1 = ts1_minus == empty && ts2_plus == empty && expr_tool::mk_item(min_ts1_plus, R, max_ts2_plus, c_exp);
                                        z3::expr item2 = ts1_minus == empty && expr_tool::mk_item(min_ts1_plus+min_ts2_minus, R, zero_exp, c_exp); // NON-DB
                                        z3::expr item3 = ts2_plus == empty && expr_tool::mk_item(min_ts2_minus, R, max_ts1_minus, c_exp);
                                        z3::expr item4 = ts1_minus != empty && ts2_plus != empty;
                                        return item1 || item2 || item4 || item3;
                                }
                        } else if (case_i == 4) {
                                // max(Ts) R min(Ts) + c
                                if (R == "=" || R == ">=") {
                                        z3::expr item1 = ts2_minus == empty && expr_tool::mk_item(max_ts1_plus, R, min_ts2_plus, c_exp);
                                        z3::expr item2 = expr_tool::mk_item(min_ts1_plus+max_ts2_minus, R, zero_exp, c_exp); // NON-DB
                                        z3::expr item3 = ts1_plus == empty && expr_tool::mk_item(max_ts2_minus, R, min_ts1_minus, c_exp);
                                        return item1 || item2 || item3;
                                } else if (R == "<=") {
                                        z3::expr item1 = ts2_minus == empty && expr_tool::mk_item(max_ts1_plus, R, min_ts2_plus, c_exp);
                                        z3::expr item2 = expr_tool::mk_item(min_ts1_plus+max_ts2_minus, R, zero_exp, c_exp); // NON-DB
                                        z3::expr item3 = ts1_plus == empty && expr_tool::mk_item(max_ts2_minus, R, min_ts1_minus, c_exp);
                                        z3::expr item4 = ts1_plus == empty && ts2_minus == empty;
                                        return item1 || item2 || item4 || item3;
                                }
                        } else if (case_i == 5) {
                                // max(Ts) R max(Ts) + c
                                if (R == "=" || R == ">=") {
                                        z3::expr item1 =  expr_tool::mk_item(max_ts1_plus, R, max_ts2_plus, c_exp);
                                        z3::expr item2 = ts2_plus == empty && expr_tool::mk_item(max_ts1_plus+min_ts2_minus, R, zero_exp, c_exp); // NON-DB
                                        z3::expr item3 = ts1_plus == empty && ts2_plus == empty && expr_tool::mk_item(min_ts2_minus, R, min_ts1_minus, c_exp);
                                        return item1 || item2 || item3;
                                } else if (R == "<=") {
                                        z3::expr item1 =  expr_tool::mk_item(max_ts1_plus, R, max_ts2_plus, c_exp);
                                        z3::expr item2 = ts2_plus == empty && expr_tool::mk_item(max_ts1_plus+min_ts2_minus, R, zero_exp, c_exp); // NON-DB
                                        z3::expr item3 = ts1_plus == empty && ts2_plus == empty && expr_tool::mk_item(min_ts2_minus, R, min_ts1_minus, c_exp);
                                        z3::expr item4 = ts1_plus == empty && ts2_minus != empty;
                                        return item1 || item2 || item4 || item3;
                                }
                        }
                }

        } else {
                // table 4
                if (case_i < 2) {
                        int ctx_1 = get_fo_ctx(t_i_1);
                        z3::expr x1_plus = expr_tool::get_plus_exp(m_ctx, t_i_1);
                        z3::expr x1_minus = expr_tool::get_minus_exp(m_ctx, t_i_1);
                        if (case_i == 0) {
                                // x R min(Ts) + c
                                z3::expr min_ts2_plus = expr_tool::mk_min_max(m_ctx, 0, ts2_plus);
                                z3::expr max_ts2_minus = expr_tool::mk_min_max(m_ctx, 1, ts2_minus);

                                if (R == "=" || R == ">=") {
                                        if (ctx_1 == 0) {
                                                return (ts2_minus == empty && expr_tool::mk_item(x1_plus, R, min_ts2_plus, c_exp));
                                        }

                                        z3::expr item1 =  expr_tool::mk_item(max_ts2_minus, R, x1_minus, c_exp);
                                        if (R == ">=") R="<=";
                                        z3::expr item2 = (ts2_minus == empty && expr_tool::mk_item(x1_minus+min_ts2_plus, R, zero_exp, c_minus_exp)); // NON-DB
                                        return  item1 || item2;
                                } else if (R == "<=") {
                                        if (ctx_1 == 0) {
                                                return (ts2_minus == empty && expr_tool::mk_item(x1_plus, R, min_ts2_plus, c_exp));
                                        }

                                        R = ">=";
                                        z3::expr item1 =  expr_tool::mk_item(x1_minus, R, max_ts2_minus, c_minus_exp);
                                        z3::expr item2 = (ts2_minus == empty && expr_tool::mk_item(x1_minus+min_ts2_plus, R, zero_exp, c_minus_exp)); // NON-DB
                                        return  item1 || item2;
                                }
                        } else if(case_i == 1) {
                                // x R max(Ts) + c
                                z3::expr max_ts2_plus = expr_tool::mk_min_max(m_ctx, 1, ts2_plus);
                                z3::expr min_ts2_minus = expr_tool::mk_min_max(m_ctx, 0, ts2_minus);

                                if (R == "=" || R == "<=") {
                                        if (ctx_1 == 0) {
                                                return expr_tool::mk_item(x1_plus, R, max_ts2_plus, c_exp);
                                        }

                                        z3::expr item1 =  ts2_plus == empty && expr_tool::mk_item(min_ts2_minus, R, x1_minus, c_exp);
                                        if (R == "<=") R = ">=";
                                        z3::expr item2 = (expr_tool::mk_item(x1_minus + max_ts2_plus, R, zero_exp, c_minus_exp)); // NON-DB
                                        return  item1 || item2;
                                } else if (R == ">=") {
                                        if (ctx_1 == 0) {
                                                return  expr_tool::mk_item(x1_plus, R, max_ts2_plus, c_exp) || ts2_plus == empty;
                                        }

                                        if (R == "<=") R = ">=";
                                        z3::expr item1 =  ts2_plus == empty && expr_tool::mk_item(x1_minus, R, min_ts2_minus, c_minus_exp);
                                        z3::expr item2 = (expr_tool::mk_item(x1_minus + max_ts2_plus, R, zero_exp, c_minus_exp)); // NON-DB
                                        return  item1 || item2;
                                }

                        }
                } else {
                        // c<0
                        z3::expr ts1_minus = translate_formula_minus(t_i_1.arg(0));
                        z3::expr ts1_plus = translate_formula_plus(t_i_1.arg(0));

                        z3::expr max_ts2_plus = expr_tool::mk_min_max(m_ctx, 1, ts2_plus);
                        z3::expr min_ts2_plus = expr_tool::mk_min_max(m_ctx, 0, ts2_plus);
                        z3::expr max_ts2_minus = expr_tool::mk_min_max(m_ctx, 1, ts2_minus);
                        z3::expr min_ts2_minus = expr_tool::mk_min_max(m_ctx, 0, ts2_minus);

                        z3::expr max_ts1_plus = expr_tool::mk_min_max(m_ctx, 1, ts1_plus);
                        z3::expr min_ts1_plus = expr_tool::mk_min_max(m_ctx, 0, ts1_plus);
                        z3::expr max_ts1_minus = expr_tool::mk_min_max(m_ctx, 1, ts1_minus);
                        z3::expr min_ts1_minus = expr_tool::mk_min_max(m_ctx, 0, ts1_minus);

                        if (case_i == 2) {
                                // min(Ts) R min(Ts) + c
                                if ( R == ">=") {
                                        z3::expr item1 = ts1_minus == empty && ts2_minus == empty && expr_tool::mk_item(min_ts1_plus, R, min_ts2_plus, c_exp);
                                        z3::expr item3 = expr_tool::mk_item(max_ts2_minus, R, max_ts1_minus, c_exp);
                                        z3::expr item4 = ts1_minus == empty && ts2_minus != empty;
                                        R = "<=";
                                        z3::expr item2 = ts2_minus == empty && expr_tool::mk_item(min_ts2_plus+max_ts1_minus, R, zero_exp, c_minus_exp); // NON-DB

                                        return item1 || item2 || item3 || item4;
                                } else if (R == "=" || R == "<=") {
                                        z3::expr item1 = ts1_minus == empty && ts2_minus == empty && expr_tool::mk_item(min_ts1_plus, R, min_ts2_plus, c_exp);
                                        z3::expr item3 = expr_tool::mk_item(max_ts2_minus, R, max_ts1_minus, c_exp);
                                        if (R == "<=") R = ">=";
                                        z3::expr item2 = ts2_minus == empty && expr_tool::mk_item(min_ts2_plus+max_ts1_minus, R, zero_exp, c_minus_exp); // NON-DB
                                        return item1 || item2 || item3;
                                }
                        } else if (case_i == 3) {
                                // min(Ts) R max(Ts) + c
                                if ( R == ">=") {
                                        z3::expr item1 = ts1_minus == empty && expr_tool::mk_item(min_ts1_plus, R, max_ts2_plus, c_exp);
                                        z3::expr item3 = ts2_plus == empty && expr_tool::mk_item(min_ts2_minus, R, max_ts1_minus, c_exp);
                                        z3::expr item4 = ts1_minus == empty && ts2_plus == empty;
                                         R = "<=";
                                        z3::expr item2 =  expr_tool::mk_item(max_ts1_minus+max_ts2_plus, R, zero_exp, c_minus_exp); // NON-DB

                                        return item1 || item2 || item4 || item3;
                                } else if (R == "=" || R == "<=") {
                                        z3::expr item1 = ts1_minus == empty && expr_tool::mk_item(min_ts1_plus, R, max_ts2_plus, c_exp);
                                        z3::expr item3 = ts2_plus == empty && expr_tool::mk_item(min_ts2_minus, R, max_ts1_minus, c_exp);
                                        if (R == "<=") R = ">=";
                                        z3::expr item2 =  expr_tool::mk_item(max_ts1_minus+max_ts2_plus, R, zero_exp, c_minus_exp); // NON-DB

                                        return item1 || item2 || item3;
                                }
                        } else if (case_i == 4) {
                                // max(Ts) R min(Ts) + c
                                if ( R == ">=") {
                                        z3::expr item1 = ts2_minus == empty && expr_tool::mk_item(max_ts1_plus, R, min_ts2_plus, c_exp);
                                        z3::expr item3 = ts1_plus == empty && expr_tool::mk_item(max_ts2_minus, R, min_ts1_minus, c_exp);
                                        z3::expr item4 = ts1_plus != empty && ts2_minus != empty;
                                        R = "<=";
                                        z3::expr item2 = ts1_plus == empty && ts2_minus == empty && expr_tool::mk_item(min_ts1_minus+max_ts2_plus, R, zero_exp, c_minus_exp); // NON-DB

                                        return item1 || item2 || item4 || item3;
                                } else if (R == "=" || R == "<=") {
                                        z3::expr item1 = ts2_minus == empty && expr_tool::mk_item(max_ts1_plus, R, min_ts2_plus, c_exp);
                                        z3::expr item3 = ts1_plus == empty && expr_tool::mk_item(max_ts2_minus, R, min_ts1_minus, c_exp);
                                        if (R == "<=") R = ">=";
                                        z3::expr item2 = ts1_plus == empty && ts2_minus == empty && expr_tool::mk_item(min_ts1_minus+max_ts2_plus, R, zero_exp, c_minus_exp); // NON-DB
                                        return item1 || item2 || item3;
                                }
                        } else if (case_i == 5) {
                                // max(Ts) R max(Ts) + c
                                if ( R == ">=") {
                                        z3::expr item1 =  expr_tool::mk_item(max_ts1_plus, R, max_ts2_plus, c_exp);
                                        z3::expr item3 = ts1_plus == empty && ts2_plus == empty && expr_tool::mk_item(min_ts2_minus, R, min_ts1_minus, c_exp);
                                        z3::expr item4 = ts1_plus != empty && ts2_minus == empty;
                                        R = "<=";
                                        z3::expr item2 = ts1_plus == empty && expr_tool::mk_item(max_ts2_plus+min_ts1_minus, R, zero_exp, c_minus_exp); // NON-DB

                                        return item1 || item2 || item4 || item3;
                                } else if (R == "=" || R == "<=") {
                                        z3::expr item1 =  expr_tool::mk_item(max_ts1_plus, R, max_ts2_plus, c_exp);
                                        z3::expr item3 = ts1_plus == empty && ts2_plus == empty && expr_tool::mk_item(min_ts2_minus, R, min_ts1_minus, c_exp);
                                        if (R == "<=")R = ">=";
                                        z3::expr item2 = ts1_plus == empty && expr_tool::mk_item(max_ts2_plus+min_ts1_minus, R, zero_exp, c_minus_exp); // NON-DB
                                        return item1 || item2  || item3;
                                }
                        }
                }

        }
}

/**
 * translate t_i_1 = c
 */
z3::expr qgdbs_translator::translate_qgdbs_minus(z3::expr t_i_1, std::string R, int c) {

        z3::expr zero_exp = m_ctx.int_val(0);
        z3::expr empty = expr_tool::mk_emptyset(m_ctx);

        if (c >= 0) {
                // table 1
                z3::expr c_exp = m_ctx.int_val(c);
                if (expr_tool::is_int_const(t_i_1)) {
                        // t_i_1 is x
                        int ctx_x = get_fo_ctx(t_i_1);
                        if (ctx_x == 0) {
                                // +
                                z3::expr x_plus = expr_tool::get_plus_exp(m_ctx, t_i_1);
                                return expr_tool::mk_item(x_plus, R, zero_exp, c_exp);
                        } else {
                                if (R == "=" || R == ">=") return m_ctx.bool_val(false);
                                else if (R == "<=") return m_ctx.bool_val(true);
                        }
                } else {
                        z3::expr t_s = t_i_1.arg(0);
                        z3::expr t_s_minus = translate_formula_minus(t_s);
                        z3::expr t_s_plus = translate_formula_plus(t_s);

                        if (expr_tool::is_fun(t_i_1, "min")) {
                                // t_i_1 is min (T_s)
                                z3::expr min_ts_plus = expr_tool::mk_min_max(m_ctx, 0, t_s_plus);
                                if (R == "=" || R == ">=") {
                                        return (t_s_minus == empty) && (expr_tool::mk_item(min_ts_plus, R, zero_exp, c_exp));
                                } else if (R == "<=") {
                                        return (t_s_minus != empty) || (expr_tool::mk_item(min_ts_plus, R, zero_exp, c_exp));
                                }
                        } else if (expr_tool::is_fun(t_i_1, "max")){
                                // t_i_1 is max (T_s)
                                z3::expr max_ts_plus = expr_tool::mk_min_max(m_ctx, 1, t_s_plus);

                                if (R == "=" || R == ">=") {
                                        // ???
                                        return (t_s_plus != empty) && (expr_tool::mk_item(max_ts_plus, R, zero_exp, c_exp));
                                } else if (R == "<=") {
                                        return (t_s_plus == empty) || (expr_tool::mk_item(max_ts_plus, R, zero_exp, c_exp));
                                }
                        }
                }
        } else {
                // table 2
                z3::expr c_exp = m_ctx.int_val(-c);
                if (expr_tool::is_int_const(t_i_1)) {
                        // t_i_1 is x
                        int ctx_x = get_fo_ctx(t_i_1);
                        if (ctx_x == 1) {
                                // -
                                z3::expr x_minus = expr_tool::get_minus_exp(m_ctx, t_i_1);
                                if (R == ">= ") R == "<=";
                                else if (R == "<=") R == ">=";
                                return expr_tool::mk_item(x_minus, R, zero_exp, c_exp);
                        } else {
                                if (R == "=" || R == "<=") return m_ctx.bool_val(false);
                                else if (R == ">=") return m_ctx.bool_val(true);
                        }
                } else {
                        z3::expr t_s = t_i_1.arg(0);
                        z3::expr t_s_minus = translate_formula_minus(t_s);
                        z3::expr t_s_plus = translate_formula_plus(t_s);

                        if (expr_tool::is_fun(t_i_1, "min")) {
                                // t_i_1 is min (T_s)
                                z3::expr max_ts_minus = expr_tool::mk_min_max(m_ctx, 1, t_s_minus);
                                if (R == "=" || R == "<=") {
                                        if (R == "<=") R = ">=";
                                        return (expr_tool::mk_item(max_ts_minus, R, zero_exp, c_exp));
                                } else if (R == ">=") {
                                        R = "<=";
                                        return (t_s_minus == empty) || (expr_tool::mk_item(max_ts_minus, R, zero_exp, c_exp));
                                }
                        } else if (expr_tool::is_fun(t_i_1, "max")){
                                // t_i_1 is max (T_s)
                                z3::expr min_ts_minus = expr_tool::mk_min_max(m_ctx, 0, t_s_minus);

                                if (R == ">=") {
                                        R = "<=";
                                        return (t_s_plus != empty) || (expr_tool::mk_item(min_ts_minus, R, zero_exp, c_exp));
                                } else if (R == "=") {
                                        return expr_tool::mk_item(min_ts_minus, R, zero_exp, c_exp);


                                } else if (R == "<=") {
                                        R = ">=";
                                        return (t_s_plus == empty) && (expr_tool::mk_item(min_ts_minus, R, zero_exp, c_exp));
                                }

                        }
                }
        }
}
