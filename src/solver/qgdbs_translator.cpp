#include "qgdbs_translator.h"


int qgdbs_translator::formula_size(){
        return m_ctx_items.size();
}

/**
 * get formula by ectx
 * @param ectx
 * @return ectx -> formula
 */
z3::expr qgdbs_translator::get_formula(int ectx) {
        assert(ectx < m_ctx_items.size());

        return m_ctx_items[ectx];
}


void qgdbs_translator::prepare() {
        // 1. get first order vars
        //std::set<z3::expr, exprcomp> fo_vars_set;
        //std::set<z3::expr, exprcomp> so_vars_set;
        // std::cout << "m_formula: " << m_formula << std::endl;

        //expr_tool::get_first_order_vars(m_formula, fo_vars_set);
        // expr_tool::expr_set_to_vec(fo_vars_set, m_first_order_vars);
        //expr_tool::get_second_order_vars(m_formula, so_vars_set);
        //expr_tool::expr_set_to_vec(so_vars_set, m_second_order_vars);

        init_ctx();


        std::cout << "fo_vars: " << m_first_order_vars.size() << std::endl;
        std::cout << "so_vars: " << m_second_order_vars.size() << std::endl;

}

bool qgdbs_translator::get_next(z3::expr& formula) {
        // print_ctx();
        if (m_index == -1 || !plus_one_ctx()) {
                // m_bctx = -1;
                // std::cout << "m_bounds: " << m_bounds.size() << std::endl;
                formula = translate_formula(m_formula);
                z3::expr ectx_exp = ectx_to_expr();
                formula = formula && ectx_exp;
                m_index++;
                return true;
        }

        return false;
}

void qgdbs_translator::print_ctx() {
        std::cout << "ectx: ";
        for (int i=0; i<m_sovar_ctx.size(); i++) {
                std::cout << m_sovar_ctx[i];
        }
        std::cout << "   ";
        for (int i=0; i<m_fovar_ctx.size(); i++) {
                std::cout << m_fovar_ctx[i];
        }
        std::cout << std::endl;
}


void qgdbs_translator::set_first_order_vars(std::set<z3::expr, exprcomp> &fo_vars_set) {
        expr_tool::expr_set_to_vec(fo_vars_set, m_first_order_vars);
}

void qgdbs_translator::set_second_order_vars(std::set<z3::expr, exprcomp> &so_vars_set) {
        expr_tool::expr_set_to_vec(so_vars_set, m_second_order_vars);
}

/**
 * generate_formula
 */
z3::expr qgdbs_translator::generate_formula() {
        // 1. get first order vars
        std::set<z3::expr, exprcomp> fo_vars_set;
        std::set<z3::expr, exprcomp> so_vars_set;
        // std::cout << "m_formula: " << m_formula << std::endl;

        expr_tool::get_first_order_vars(m_formula, fo_vars_set);
        expr_tool::expr_set_to_vec(fo_vars_set, m_first_order_vars);
        expr_tool::get_second_order_vars(m_formula, so_vars_set);
        expr_tool::expr_set_to_vec(so_vars_set, m_second_order_vars);

        init_ctx();


        std::cout << "fo_vars: " << m_first_order_vars.size() << std::endl;
        std::cout << "so_vars: " << m_second_order_vars.size() << std::endl;


        do {
                // m_bctx = -1;
                z3::expr or_i = translate_formula(m_formula);
                z3::expr ectx_exp = ectx_to_expr();
                or_i = or_i && ectx_exp;
                m_ctx_items.push_back(or_i);
        } while (!plus_one_ctx());

        std::cout << "size: " << m_ctx_items.size() << std::endl;

        // z3::expr result = z3::mk_or(m_ctx_items);

        return m_ctx.bool_val(true);
}

/**
 * ectx append constraints
 */
z3::expr qgdbs_translator::ectx_to_expr() {
        z3::expr empty = expr_tool::mk_emptyset(m_ctx);
        z3::expr_vector and_items(m_ctx);

        for (int i=0; i<m_first_order_vars.size(); i++) {
                z3::expr x = m_first_order_vars[i];
                z3::expr x_plus = expr_tool::get_plus_exp(m_ctx, x);
                z3::expr x_minus = expr_tool::get_minus_exp(m_ctx, x);
                if (m_fovar_ctx[i]) {
                        // -
                        and_items.push_back(x_plus==0 && x_minus>0);
                } else {
                        and_items.push_back(x_minus == 0);
                }
        }

        for (int i=0; i<m_second_order_vars.size(); i++) {
                z3::expr s = m_second_order_vars[i];
                z3::expr s_plus = expr_tool::get_plus_exp(m_ctx, s);
                z3::expr s_minus = expr_tool::get_minus_exp(m_ctx, s);
                if (m_sovar_ctx[i] == 0) {
                        // +
                        and_items.push_back(s_minus == empty && s_plus != empty);
                } else if (m_sovar_ctx[i] == 1) {
                        // -
                        and_items.push_back(s_minus != empty && s_plus == empty);
                } else if (m_sovar_ctx[i] == 2){
                        // +-
                        and_items.push_back(s_plus != empty && s_minus != empty);
                } else {
                        and_items.push_back(s_plus == empty && s_minus == empty);
                }
        }

        if (and_items.size() > 0) {
                return z3::mk_and(and_items);
        }
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
                        if (expr_tool::index_of_exp(delta, m_bounds) != -1) {
                                result = true;
                        }
                }
                for (int i=0; i<delta.num_args(); i++) {
                        if(has_quantified_var(delta.arg(i), var_set)) result = true;;
                }
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
                if (formula.num_args() == 0) return formula;

                if (expr_tool::is_fun(formula, "and")) {
                        // and
                        z3::expr_vector items(m_ctx);
                        for (int i=0; i<formula.num_args(); i++) {
                                z3::expr item = translate_formula(formula.arg(i));
                                if (!item.is_bool()) {
                                        std::cout << "problem: " << formula << std::endl;
                                        exit(-1);
                                }
                                items.push_back(item);
                        }
                        // std::cout << "items : " << items << std::endl;

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
                        if (expr_tool::is_bottom(tr_minus0) || expr_tool::is_bottom(tr_minus1) ||
                            expr_tool::is_bottom(tr_plus0) || expr_tool::is_bottom(tr_plus1)) return m_ctx.bool_val(false);

                        /*
                          std::set<z3::expr, exprcomp> singles;
                          z3::expr empty = expr_tool::mk_emptyset(m_ctx);
                          expr_tool::get_singleset(formula, singles); // get singles

                          z3::expr plus_empty = m_ctx.bool_val(true); //
                          z3::expr minus_empty = m_ctx.bool_val(true);

                          z3::expr_vector srcs_plus(m_ctx);
                          z3::expr_vector dsts_plus(m_ctx);
                          z3::expr_vector srcs_minus(m_ctx);
                          z3::expr_vector dsts_minus(m_ctx);


                          // single {min or max}
                          for (auto single : singles) {
                          z3::expr S(m_ctx);
                          if (expr_tool::get_singleset_min(single, S)) {
                          z3::expr plus_s = translate_formula_plus(S);
                          z3::expr minus_s = translate_formula_minus(S);
                          plus_empty = plus_empty && (plus_s == empty);
                          minus_empty = minus_empty && (minus_s == empty);

                          z3::expr plus_single = translate_formula_plus(single);
                          z3::expr minus_single = translate_formula_minus(single);

                          srcs_plus.push_back(plus_single);
                          dsts_plus.push_back(empty);

                          srcs_minus.push_back(minus_single);
                          dsts_minus.push_back(empty);

                          }
                          }
                        */


                        z3::expr and_1(m_ctx);
                        z3::expr and_2(m_ctx);

                        if (expr_tool::is_fun(formula, "=")) {
                                // ==
                                and_1 = tr_minus0 == tr_minus1;
                                and_2 = tr_plus0 == tr_plus1;

                        } else if(expr_tool::is_fun(formula, "subset")) {
                                // subset
                                and_1 = expr_tool::mk_binary_bool(m_ctx, "subset", tr_minus0, tr_minus1);
                                and_2 = expr_tool::mk_binary_bool(m_ctx, "subset", tr_plus0, tr_plus1);
                        } else {
                                std::cout << "NO SUPPORT!\n";
                        }

                        /*
                          z3::expr f = formula;

                          if (srcs_plus.size() > 0) {
                          // std::cout << "formula: " << formula << std::endl;
                          //std::cout << "srcs_plus: " << srcs_plus << std::endl;
                          //std::cout << "src_minus: " << srcs_minus << std::endl;
                          z3::expr or_2 = and_2.substitute(srcs_plus, dsts_plus) && plus_empty;
                          z3::expr or_1 = and_1.substitute(srcs_minus, dsts_minus) && minus_empty;
                          // std::cout << "or_1: " << or_1 << std::endl;
                          //std::cout << "or_2: " << or_2 << std::endl;
                          and_1 = and_1 || or_1;
                          and_2 = and_2 || or_2;
                          }
                        */

                        result = and_1 && and_2;

                } else if (formula.arg(1).is_int()) {
                        // first order
                        std::set<z3::expr, exprcomp> var_set;
                        bool has_q = has_quantified_var(formula, var_set);

                        int case_i = 0; // bit1: t_i_2 is const? bit0: c<0?
                        z3::expr t_i_1 = formula.arg(0);
                        z3::expr t_i_2 = formula.arg(1);
                        int c = 0;
                        std::string R = formula.decl().name().str();
                        /*
                          if (has_q) {

                          } else {
                          case_i = 4;
                          }
                        */
                        if (t_i_1.num_args() < 2) {
                                if (t_i_2.num_args() == 2) {
                                        // t_i_2 = t_i + c | c + c
                                        std::string plus = t_i_2.decl().name().str();
                                        if (expr_tool::is_constant(t_i_2.arg(1))) {
                                                c = t_i_2.arg(1).get_numeral_int();
                                                if (plus == "-") c = -c;
                                                t_i_2 = t_i_2.arg(0);
                                                if (expr_tool::is_constant(t_i_2)) {
                                                        c += t_i_2.get_numeral_int();
                                                } else {
                                                        case_i += 2;
                                                }
                                                if (c < 0) {
                                                        // table 3
                                                        case_i += 1;
                                                }
                                        } else {
                                                case_i = 4;
                                        }
                                } else if (t_i_2.num_args() < 2) {
                                        // t_i_2 = t_i | c
                                        if (expr_tool::is_constant(t_i_2)) {
                                                c = t_i_2.get_numeral_int();
                                        } else {
                                                case_i += 2;
                                        }

                                        if (c < 0) {
                                                case_i += 1;
                                        }
                                } else {
                                        case_i = 4;
                                }
                        } else {
                                case_i = 4;
                        }

                        // std::cout << "case_i: " << case_i << std::endl;

                        if (case_i == 0) {
                                // table 1
                                // t_i_1, R, c
                                result = translate_qgdbs_minus(t_i_1, R, c);

                        } else if(case_i == 1) {
                                // table 2
                                // t_i_1, R, c
                                result = translate_qgdbs_minus(t_i_1, R, c);
                        } else if (case_i == 2) {
                                // table 3
                                // t_i_1 R, t_i_2 c
                                // std::cout << "ti1: " << t_i_1 << " " << R <<  " , ti2: " << t_i_2 << ", c: " << c << std::endl;
                                result = translate_qgdbs_minus(t_i_1, R, t_i_2, c);
                        } else if (case_i == 3){
                                // table 4
                                // t_i_1 R, t_i_2 c
                                result = translate_qgdbs_minus(t_i_1, R, t_i_2, c);
                        } else {
                                // trival TODO
                                for (auto var : var_set) {
                                        int ctx_var = get_ctx(var);
                                        if (ctx_var == -1) {
                                                result = m_ctx.bool_val(false);
                                                break;
                                        }

                                        if (expr_tool::is_int_const(var)) {
                                                if (ctx_var == 0) {
                                                        // +


                                                } else {
                                                        // -
                                                }
                                        } else {
                                                if (ctx_var == 0) {
                                                        // +
                                                } else if (ctx_var == 1) {
                                                        // -

                                                } else {
                                                        // +-

                                                }
                                        }
                                }

                        }
                }
        } else if (formula.is_quantifier()) {
                // forall
                z3::expr body = formula.body();
                z3::expr_vector pars(m_ctx);
                expr_tool::get_pars_quantifier(m_ctx, formula, pars, body);

                // z3::expr_vector fo_pars(m_ctx);
                // z3::expr_vector so_pars(m_ctx);
                // z3::expr_vector fo_bounds(m_ctx);
                int NUM = 1;
                int size = pars.size();
                z3::expr_vector all_pars(m_ctx);
                int start = m_bounds.size();

                for (int i=0; i<size; i++) {
                        z3::expr plus = expr_tool::get_plus_exp(m_ctx, pars[i]);
                        z3::expr minus = expr_tool::get_minus_exp(m_ctx, pars[i]);
                        all_pars.push_back(plus);
                        all_pars.push_back(minus);

                        if (pars[i].is_int()) {
                                // fo_pars.push_back(expr_tool::get_plus_exp(m_ctx, pars[i]));
//                                 fo_pars.push_back(expr_tool::get_minus_exp(m_ctx, pars[i]));

                                // fo_bounds.push_back(pars[i]);
                                NUM *= 2;
                                // m_bounds_ctx.push_back(0);
                        } else {
                                // so_pars.push_back(expr_tool::get_plus_exp(m_ctx, pars[i]));
                                // so_pars.push_back(expr_tool::get_minus_exp(m_ctx, pars[i]));
                                //m_so_bounds.push_back(pars[i]);
                                NUM *= 4;
                        }
                        m_bounds.push_back(pars[i]);
                        m_bounds_ctx.push_back(0);
                }

                // int size = fo_bounds.size();
                int i=0;
                z3::expr_vector all_items(m_ctx);
                // int b_ctx = m_bctx; // push

                // std::cout << "NUM:: " << NUM << std::endl;

                do{
                        //i->expr
                        z3::expr pre_exp = bctx_to_expr(pars, start);
                        z3::expr body_p = translate_formula(body);

                        z3::expr imp_exp = !(pre_exp && !body_p);
                        all_items.push_back(imp_exp); // new items
                        i++;
                        if (i < NUM) { // the last can not do
                                plus_one_bctx();
                        }
                }while(i < NUM);

                // std::cout << "end body.....\n";



                result = z3::mk_and(all_items);
                result = z3::forall(all_pars, result);

                //std::cout << "formula: " << formula << std::endl;

                //std::cout << "result: " << result << std::endl;
                //exit(-1);
                /*
                  if (fo_pars.size() > 0) {
                  result = z3::forall(fo_pars, result);
                  }
                  // make all
                  if (so_pars.size() > 0)
                  result = z3::forall(so_pars, result);
                */
                // pop
                for (i=0; i<size; i++) {
                        m_bounds.pop_back();
                        m_bounds_ctx.pop_back();
                }
                // std::cout << "m_bounds: " << m_bounds.size() << std::endl;
        }
        return result;

}


/**
 * ctx to premise
 * @param bounds : quantifiers
 * @param start : index
 * @return exp
 */
z3::expr qgdbs_translator::bctx_to_expr(z3::expr_vector &bounds, int start) {
        int size = bounds.size();

        z3::expr premise = m_ctx.bool_val(true);
        z3::expr empty = expr_tool::mk_emptyset(m_ctx);
        for (int i=0; i<size; i++) {
                int ctx_i = m_bounds_ctx[start+i];
                z3::expr x_i = bounds[i];
                z3::expr x_i_plus = expr_tool::get_plus_exp(m_ctx, x_i);
                z3::expr x_i_minus = expr_tool::get_minus_exp(m_ctx, x_i);
                if (x_i.get_sort().is_int()) {
                        if (ctx_i == 1) {
                                premise = premise && (x_i_plus==0 && x_i_minus>0);
                        } else {
                                premise = premise && (x_i_minus == 0);
                        }
                } else {
                        if (ctx_i == 0) {
                                premise = premise && (x_i_plus != empty && x_i_minus == empty);
                        } else if (ctx_i == 1) {
                                premise = premise && (x_i_plus == empty && x_i_minus != empty);
                        } else if (ctx_i == 2) {
                                premise = premise && (x_i_plus != empty && x_i_minus != empty);
                        } else {
                                premise = premise && (x_i_plus == empty && x_i_minus == empty);
                        }
                }
        }
        return premise;
}




/**
 * get first order var exp ctx [+, -]
 * @param exp : first order var
 * @return 0[+], 1[-]
 */
int qgdbs_translator::get_ctx(z3::expr exp) {
        int index = expr_tool::index_of_exp(exp, m_bounds);
        // exp is bound var
        if (index != -1) return m_bounds_ctx[index];

        // exp is first order var
        index = expr_tool::index_of_exp(exp, m_first_order_vars);
        if (index != -1)
                return m_fovar_ctx[index];
        index = expr_tool::index_of_exp(exp, m_second_order_vars);
        if (index != -1)
                return m_sovar_ctx[index];
        return 0;
}

void qgdbs_translator::init_ctx() {
        int fo_num = m_first_order_vars.size();
        int so_num = m_second_order_vars.size();

        for (int i=0; i<fo_num; i++) m_fovar_ctx.push_back(0);
        for (int i=0; i<so_num; i++) m_sovar_ctx.push_back(0);
        // m_sovar_ctx.push_back(2);
        // m_sovar_ctx.push_back(0);

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
                c=0;
                m_fovar_ctx[i] = cur;
                if (cur == 2) {
                        c = 1;
                        m_fovar_ctx[i] = 0;
                }
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

int qgdbs_translator::plus_one_bctx() {
        int c = 1;
        int cur = 0;
        int CN = 0;
        for (int i=m_bounds.size()-1; i>=0; i--) {
                cur = m_bounds_ctx[i] + c;
                c = 0;
                m_bounds_ctx[i] = cur;
                if (m_bounds[i].get_sort().is_int()) {
                        CN = 2;
                } else {
                        CN = 4;
                }
                if (cur == CN) {
                        c = 1;
                        m_bounds_ctx[i] = 0;
                }
                if (c == 0) break;
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
        z3::expr bottom = expr_tool::mk_bottom(m_ctx);

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
                                int ctx_v = get_ctx(formula);
                                if (ctx_v == -1 || ctx_v == 1) {
                                        return min_empty;
                                } else {
                                        return expr_tool::get_plus_exp(m_ctx, formula);
                                }
                        }
                }
                // (min ) (max )
                if (expr_tool::is_fun(formula, "min")) {

                        /*
                          z3::expr ts = translate_formula_plus(formula.arg(0));
                          if (expr_tool::is_fun(ts, "emptyset")) {
                          // TODO UNDEF
                          return min_empty;
                          }
                        */

                        z3::expr ts = formula.arg(0);
                        z3::expr ts_plus = expr_tool::get_plus_exp(m_ctx, ts);
                        if (expr_tool::is_setint_const(ts)) {
                                int ctx_ts = get_ctx(ts);
                                if (ctx_ts == 1 || ctx_ts == 2) {
                                        return min_empty;
                                } else if (ctx_ts == 0) {
                                        return expr_tool::mk_min_max(m_ctx, 0, ts_plus);
                                } else {
                                        return expr_tool::mk_bottom(m_ctx);
                                }
                        } else {
                                std::cout << "Error!!!\n";
                                exit(-1);
                        }
                        // return expr_tool::mk_min_max(m_ctx, 0, ts);
                }
                if (expr_tool::is_fun(formula, "max")) {
                        /*
                          z3::expr ts = translate_formula_plus(formula.arg(0));
                          if (expr_tool::is_fun(ts, "emptyset")) {
                          // TODO UNDEF
                          return min_empty;
                          }
                          return expr_tool::mk_min_max(m_ctx, 1, ts);
                        */

                        z3::expr ts = formula.arg(0);
                        z3::expr ts_plus = expr_tool::get_plus_exp(m_ctx, ts);
                        if (expr_tool::is_setint_const(ts)) {
                                int ctx_ts = get_ctx(ts);
                                if (ctx_ts == 1) {
                                        return min_empty;
                                } else if (ctx_ts == 0 || ctx_ts == 2) {
                                        return expr_tool::mk_min_max(m_ctx, 1, ts_plus);
                                } else {
                                        return bottom;
                                }
                        } else {
                                std::cout << "Error!!!\n";
                                exit(-1);
                        }
                }
        }


        // [second order]
        // emptyset
        if (expr_tool::is_fun(formula, "emptyset")) {
                return empty;
        }
        // set var
        if (expr_tool::is_setint_const(formula)) {
                int ctx_f = get_ctx(formula);
                if (ctx_f == 0 || ctx_f == 2) {
                        return expr_tool::get_plus_exp(m_ctx, formula);
                } else {
                        return empty;
                }
        }
        // (set int)
        if (expr_tool::is_fun(formula, "set")) {
                z3::expr element = translate_formula_plus(formula.arg(0)); // first order
                if (expr_tool::is_bottom(element)) {
                        return bottom;
                }else if (element.hash() == min_empty.hash()) {
                        return empty;
                } else {
                        return expr_tool::mk_single_set(m_ctx, element);
                }
        }


        z3::expr ts1 = translate_formula_plus(formula.arg(0));
        z3::expr ts2 = translate_formula_plus(formula.arg(1));

        if (expr_tool::is_bottom(ts1) || expr_tool::is_bottom(ts2)) {
                return bottom;
        }
        // (setunion ) (setintersect ) (setminus )
        if (expr_tool::is_fun(formula, "setunion")) {
                return expr_tool::mk_binary_set(m_ctx, "setunion", ts1, ts2);
        }

        if (expr_tool::is_fun(formula, "setintersect")) {

                return expr_tool::mk_binary_set(m_ctx, "setintersect", ts1, ts2);
        }

        if (expr_tool::is_fun(formula, "setminus")) {

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
        z3::expr bottom = expr_tool::mk_bottom(m_ctx);

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
                                int ctx_v = get_ctx(formula);
                                if (ctx_v == -1 || ctx_v == 0) {
                                        return min_empty;
                                } else {
                                        return expr_tool::get_minus_exp(m_ctx, formula);
                                }
                        }
                }
                // (min ) (max )
                if (expr_tool::is_fun(formula, "min")) {
                        z3::expr ts = formula.arg(0);
                        z3::expr ts_minus = expr_tool::get_minus_exp(m_ctx, ts);
                        if (expr_tool::is_setint_const(ts)) {
                                int ctx_ts = get_ctx(ts);
                                if (ctx_ts == 0) {
                                        return min_empty;
                                } else if (ctx_ts == 1 || ctx_ts == 2) {
                                        return expr_tool::mk_min_max(m_ctx, 1, ts_minus);
                                } else {
                                        // std::cout << "bottom.....\n";
                                        return bottom;
                                }
                        } else {
                                std::cout << "Error!!!\n";
                                exit(-1);
                        }
                }
                if (expr_tool::is_fun(formula, "max")) {
                        z3::expr ts = formula.arg(0);
                        z3::expr ts_minus = expr_tool::get_minus_exp(m_ctx, ts);

                        if (expr_tool::is_setint_const(ts)) {
                                int ctx_ts = get_ctx(ts);
                                if (ctx_ts == 0 || ctx_ts == 2) {
                                        return min_empty;
                                } else if (ctx_ts == 1) {
                                        return expr_tool::mk_min_max(m_ctx, 0, ts_minus);
                                } else {
                                        return bottom;
                                }
                        } else {
                                std::cout << "Error!!!\n";
                                exit(-1);
                        }
                }
        }


        // [second order]
        // emptyset
        if (expr_tool::is_fun(formula, "emptyset")) {
                return empty;
        }
        // set var
        if (expr_tool::is_setint_const(formula)) {
                int ctx_f = get_ctx(formula);
                if (ctx_f == 1 || ctx_f == 2) {
                        return expr_tool::get_minus_exp(m_ctx, formula);
                } else {
                        return empty;
                }
        }
        // (set int)
        if (expr_tool::is_fun(formula, "set")) {
                z3::expr element = translate_formula_minus(formula.arg(0)); // first order
                if (expr_tool::is_bottom(element)) {
                        return bottom;
                }else if (element.hash() == min_empty.hash()) {
                        return empty;
                } else {
                        return expr_tool::mk_single_set(m_ctx, element);
                }
        }


        z3::expr ts1 = translate_formula_minus(formula.arg(0));
        z3::expr ts2 = translate_formula_minus(formula.arg(1));


        if (expr_tool::is_bottom(ts1) || expr_tool::is_bottom(ts2)) {
                return bottom;
        }

        // (setunion ) (setintersect ) (setminus )
        if (expr_tool::is_fun(formula, "setunion")) {

                return expr_tool::mk_binary_set(m_ctx, "setunion", ts1, ts2);
        }

        if (expr_tool::is_fun(formula, "setintersect")) {

                return expr_tool::mk_binary_set(m_ctx, "setintersect", ts1, ts2);
        }

        if (expr_tool::is_fun(formula, "setminus")) {

                return expr_tool::mk_binary_set(m_ctx, "setminus", ts1, ts2);
        }

        return m_ctx.bool_val(true);
}


/**
 * item to qgdbs (t_i_1 + t_i_2 R c)
 * @param t_i_1
 * @param t_i_2
 * @param R: >=, <=, =
 * @param c: constant value
 * @return
 */
z3::expr qgdbs_translator::item_to_qgdbs(z3::expr t_i_1, z3::expr t_i_2, std::string R, int c) {
        z3::expr zero = m_ctx.int_val(0);
        if (c < 0) {
                if (R == ">=") return m_ctx.bool_val(true);
                else return m_ctx.bool_val(false);
        } else {
                int c1=0;
                z3::expr result = m_ctx.bool_val(false);
                for (; c1<=c; c1++) {
                        z3::expr c1_exp = m_ctx.int_val(c1);
                        z3::expr c2_exp = m_ctx.int_val(c-c1);
                        result = result || (expr_tool::mk_item(t_i_1, R, zero, c1_exp) && expr_tool::mk_item(t_i_2, R, zero, c2_exp));
                }
                return result;
        }
}

/**
 * translate t_i_1 = t_i_2 + c by table 3, 4
 *
 */
z3::expr qgdbs_translator::translate_qgdbs_minus(z3::expr t_i_1, std::string R, z3::expr t_i_2, int c) {

        // OP is {<=, =, >=}
        if (R == ">") {
                R = ">=";
                c += 1;
        } else if (R == "<") {
                c -= 1;
                R = "<=";
        }

        z3::expr c_exp = m_ctx.int_val(c);
        z3::expr c_minus_exp = m_ctx.int_val(-c);
        z3::expr zero_exp = m_ctx.int_val(0);
        z3::expr empty = expr_tool::mk_emptyset(m_ctx);
        int case_i = 0;




        if (expr_tool::is_int_const(t_i_1) && expr_tool::is_int_const(t_i_2)) {
                // x1 = x2 + c
                int ctx_1 = get_ctx(t_i_1);
                int ctx_2 = get_ctx(t_i_2);
                z3::expr x1_plus = expr_tool::get_plus_exp(m_ctx, t_i_1);
                z3::expr x1_minus = expr_tool::get_minus_exp(m_ctx, t_i_1);
                z3::expr x2_plus = expr_tool::get_plus_exp(m_ctx, t_i_2);
                z3::expr x2_minus = expr_tool::get_minus_exp(m_ctx, t_i_2);

                case_i = ctx_1*2 + ctx_2;

                if (case_i == 0) {
                        // +, +
                        return expr_tool::mk_item(x1_plus, R, x2_plus, c_exp);

                } else if (case_i == 3) {
                        // -, -
                        return expr_tool::mk_item(x2_minus, R, x1_minus, c_exp);

                } else if (case_i == 1) {
                        // +, -
                        //  return expr_tool::mk_item(x1_plus+x2_minus, R, zero_exp, c_exp);
                        return item_to_qgdbs(x1_plus, x2_minus, R, c);

                } else {
                        // -, + [NON-DB]
                        if (R == "<=") R = ">=";
                        else if (R == ">=") R = "<=";
                        // return expr_tool::mk_item(x2_plus+x1_minus, R, zero_exp, c_minus_exp);
                        return item_to_qgdbs(x1_minus, x2_plus, R, -c);
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
                        int ctx_1 = get_ctx(t_i_1);
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
                                        // z3::expr item2 = (expr_tool::mk_item(x1_plus+max_ts2_minus, R, zero_exp, c_exp)); // NON-DB
                                        z3::expr item2 = item_to_qgdbs(x1_plus, max_ts2_minus, R, c);
                                        return  item1 || item2;
                                } else if (R == "<=") {
                                        if (ctx_1) {
                                                return ts2_minus == empty || expr_tool::mk_item(max_ts2_minus, R, x1_minus, c_exp);
                                        }

                                        z3::expr item1 = (ts2_minus == empty && expr_tool::mk_item(x1_plus, R, min_ts2_plus, c_exp));
                                        // z3::expr item2 = (expr_tool::mk_item(x1_plus+max_ts2_minus, R, zero_exp, c_exp)); // NON-DB
                                        z3::expr item2 = item_to_qgdbs(x1_plus, max_ts2_minus, R, c);

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
                                        // z3::expr item2 = (ts2_plus==empty && expr_tool::mk_item(x1_plus + min_ts2_minus, R, zero_exp, c_exp)); // NON-DB
                                        z3::expr item2 = (ts2_plus==empty && item_to_qgdbs(x1_plus, min_ts2_minus, R, c));

                                        return  item1 || item2;
                                } else if (R == ">=") {
                                        if (ctx_1) {
                                                return  expr_tool::mk_item(min_ts2_minus, R, x1_minus, c_exp);
                                        }

                                        z3::expr item1 = expr_tool::mk_item(x1_plus, R, max_ts2_plus, c_exp);
                                        // z3::expr item2 = (ts2_plus == empty && expr_tool::mk_item(x1_plus+min_ts2_minus, R, zero_exp, c_exp)); // NON-DB
                                        z3::expr item2 = (ts2_plus==empty && item_to_qgdbs(x1_plus, min_ts2_minus, R, c));

                                        return  item1 || item2;
                                }

                        }
                } else {

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
                                if (R == "=" || R == ">=") {
                                        z3::expr item1 = ts1_minus == empty && ts2_minus == empty && expr_tool::mk_item(min_ts1_plus, R, min_ts2_plus, c_exp);
                                        // z3::expr item2 = ts1_minus == empty && expr_tool::mk_item(min_ts1_plus+max_ts2_minus, R, zero_exp, c_exp); // NON-DB
                                        z3::expr item2 = ts1_minus == empty && item_to_qgdbs(min_ts1_plus, max_ts2_minus, R, c);
                                        z3::expr item3 = expr_tool::mk_item(max_ts2_minus, R, max_ts1_minus, c_exp);
                                        return item1 || item2 || item3;
                                } else if (R == "<=") {
                                        z3::expr item1 = ts1_minus == empty && ts2_minus == empty && expr_tool::mk_item(min_ts1_plus, R, min_ts2_plus, c_exp);
                                        // z3::expr item2 = ts1_minus == empty && expr_tool::mk_item(min_ts1_plus+max_ts2_minus, R, zero_exp, c_exp); // NON-DB
                                        z3::expr item2 = ts1_minus == empty && item_to_qgdbs(min_ts1_plus, max_ts2_minus, R, c);

                                        z3::expr item3 = expr_tool::mk_item(max_ts2_minus, R, max_ts1_minus, c_exp);
                                        z3::expr item4 = ts1_minus != empty && ts2_minus == empty && ts2_plus != empty;
                                        return item1 || item2 || item4 || item3;
                                }
                        } else if (case_i == 3) {
                                // min(Ts) R max(Ts) + c
                                z3::expr item1 = ts1_minus == empty  && expr_tool::mk_item(min_ts1_plus, R, max_ts2_plus, c_exp);
                                // z3::expr item2 = ts1_minus == empty && ts2_plus == empty && expr_tool::mk_item(min_ts1_plus+min_ts2_minus, R, zero_exp, c_exp); // NON-DB
                                z3::expr item2 = ts1_minus == empty && ts2_plus == empty && item_to_qgdbs(min_ts1_plus, min_ts2_minus, R, c);
                                z3::expr item3 = ts2_plus == empty && expr_tool::mk_item(min_ts2_minus, R, max_ts1_minus, c_exp);

                                if (R == "=" || R == ">=") {
                                        return item1 || item2 || item3;
                                } else if (R == "<=") {
                                        z3::expr item4 = ts1_minus != empty && ts2_plus != empty;
                                        return item1 || item2 || item4 || item3;
                                }
                        } else if (case_i == 4) {
                                // max(Ts) R min(Ts) + c
                                // std::cout << "item: " << t_i_1 << R << t_i_2 << std::endl;
                                z3::expr item1 = ts2_minus == empty && expr_tool::mk_item(max_ts1_plus, R, min_ts2_plus, c_exp);
                                // z3::expr item2 = expr_tool::mk_item(min_ts1_plus+max_ts2_minus, R, zero_exp, c_exp); // NON-DB
                                z3::expr item2 = item_to_qgdbs(min_ts1_plus, max_ts2_minus, R, c);

                                z3::expr item3 = ts1_plus == empty && expr_tool::mk_item(max_ts2_minus, R, min_ts1_minus, c_exp);
                                if (R == "=" || R == ">=") {
                                        return item1 || item2 || item3;
                                } else if (R == "<=") {
                                        z3::expr item4 = ts1_plus == empty && ts1_minus != empty && ts2_minus == empty && ts2_plus != empty;
                                        return item1 || item2 || item4 || item3;
                                }
                        } else if (case_i == 5) {
                                // max(Ts) R max(Ts) + c
                                z3::expr item1 =  expr_tool::mk_item(max_ts1_plus, R, max_ts2_plus, c_exp);
                                // z3::expr item2 = ts2_plus == empty && expr_tool::mk_item(max_ts1_plus+min_ts2_minus, R, zero_exp, c_exp); // NON-DB
                                z3::expr item2 = ts2_plus == empty && item_to_qgdbs(max_ts1_plus, min_ts2_minus, R, c);

                                z3::expr item3 = ts1_plus == empty && ts2_plus == empty && expr_tool::mk_item(min_ts2_minus, R, min_ts1_minus, c_exp);
                                if (R == "=" || R == ">=") {
                                        return item1 || item2 || item3;
                                } else if (R == "<=") {
                                        z3::expr item4 = ts1_plus == empty && ts1_minus != empty && ts2_plus != empty;
                                        return item1 || item2 || item4 || item3;
                                }
                        }
                }

        } else {
                // table 4 (c<0)

                // c<0
                if (R == ">=") R = "<=";
                if (R == "<=") R = ">=";
                return translate_qgdbs_minus(t_i_2, R, t_i_1, -c);




                /*
                if (case_i < 2) {
                        int ctx_1 = get_ctx(t_i_1);
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
                                        // z3::expr item2 = (ts2_minus == empty && expr_tool::mk_item(x1_minus+min_ts2_plus, R, zero_exp, c_minus_exp)); // NON-DB
                                        z3::expr item2 = (ts2_minus == empty && item_to_qgdbs(x1_minus, min_ts2_plus, R, -c)); // NON-DB

                                        return  item1 || item2;
                                } else if (R == "<=") {
                                        if (ctx_1 == 0) {
                                                return (ts2_minus == empty && expr_tool::mk_item(x1_plus, R, min_ts2_plus, c_exp));
                                        }

                                        R = ">=";
                                        z3::expr item1 =  expr_tool::mk_item(x1_minus, R, max_ts2_minus, c_minus_exp);
                                        // z3::expr item2 = (ts2_minus == empty && expr_tool::mk_item(x1_minus+min_ts2_plus, R, zero_exp, c_minus_exp)); // NON-DB
                                        z3::expr item2 = (ts2_minus == empty && item_to_qgdbs(x1_minus, min_ts2_plus, R, -c)); // NON-DB

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
                                        // z3::expr item2 = (expr_tool::mk_item(x1_minus + max_ts2_plus, R, zero_exp, c_minus_exp)); // NON-DB
                                        z3::expr item2 = item_to_qgdbs(x1_minus, max_ts2_plus, R, -c); // NON-DB

                                        return  item1 || item2;
                                } else if (R == ">=") {
                                        if (ctx_1 == 0) {
                                                return  expr_tool::mk_item(x1_plus, R, max_ts2_plus, c_exp) || ts2_plus == empty;
                                        }

                                        if (R == "<=") R = ">=";
                                        z3::expr item1 =  ts2_plus == empty && expr_tool::mk_item(x1_minus, R, min_ts2_minus, c_minus_exp);
                                        // z3::expr item2 = (expr_tool::mk_item(x1_minus + max_ts2_plus, R, zero_exp, c_minus_exp)); // NON-DB
                                        z3::expr item2 = item_to_qgdbs(x1_minus, max_ts2_plus, R, -c); // NON-DB

                                        return  item1 || item2;
                                }

                        }
                } else {
                        // case_i >= 2


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
                                z3::expr item1 = ts1_minus == empty && ts2_minus == empty && expr_tool::mk_item(min_ts1_plus, R, min_ts2_plus, c_exp);
                                z3::expr item3 = expr_tool::mk_item(max_ts2_minus, R, max_ts1_minus, c_exp);
                                if ( R == ">=") {

                                        z3::expr item4 = ts1_minus == empty && ts2_minus != empty;
                                        R = "<=";
                                        // z3::expr item2 = ts2_minus == empty && expr_tool::mk_item(min_ts2_plus+max_ts1_minus, R, zero_exp, c_minus_exp); // NON-DB
                                        z3::expr item2 = ts2_minus == empty && item_to_qgdbs(max_ts1_minus, min_ts2_plus, R, -c);


                                        return item1 || item2 || item3 || item4;
                                } else if (R == "=" || R == "<=") {
                                        if (R == "<=") R = ">=";
                                        // z3::expr item2 = ts2_minus == empty && expr_tool::mk_item(min_ts2_plus+max_ts1_minus, R, zero_exp, c_minus_exp); // NON-DB
                                        z3::expr item2 = ts2_minus == empty && item_to_qgdbs(max_ts1_minus, min_ts2_plus, R, -c);

                                        return item1 || item2 || item3;
                                }
                        } else if (case_i == 3) {
                                // min(Ts) R max(Ts) + c
                                z3::expr item1 = ts1_minus == empty && expr_tool::mk_item(min_ts1_plus, R, max_ts2_plus, c_exp);
                                z3::expr item3 = ts2_plus == empty && expr_tool::mk_item(min_ts2_minus, R, max_ts1_minus, c_exp);
                                if ( R == ">=") {
                                        z3::expr item4 = ts1_minus == empty && ts1_plus != empty && ts2_plus == empty && ts2_minus != empty;
                                        R = "<=";
                                        // z3::expr item2 =  expr_tool::mk_item(max_ts1_minus+max_ts2_plus, R, zero_exp, c_minus_exp); // NON-DB
                                        z3::expr item2 = item_to_qgdbs(max_ts1_minus, max_ts2_plus, R, -c);

                                        return item1 || item2 || item4 || item3;
                                } else if (R == "=" || R == "<=") {
                                        if (R == "<=") R = ">=";
                                        // z3::expr item2 =  expr_tool::mk_item(max_ts1_minus+max_ts2_plus, R, zero_exp, c_minus_exp); // NON-DB
                                        z3::expr item2 = item_to_qgdbs(max_ts1_minus, max_ts2_plus, R, -c);

                                        return item1 || item2 || item3;
                                }
                        } else if (case_i == 4) {
                                // max(Ts) R min(Ts) + c
                                z3::expr item1 = ts2_minus == empty && expr_tool::mk_item(max_ts1_plus, R, min_ts2_plus, c_exp);
                                z3::expr item3 = ts1_plus == empty && expr_tool::mk_item(max_ts2_minus, R, min_ts1_minus, c_exp);
                                if ( R == ">=") {
                                        z3::expr item4 = ts1_plus != empty && ts2_minus != empty;
                                        R = "<=";
                                        // z3::expr item2 = ts1_plus == empty && ts2_minus == empty && expr_tool::mk_item(min_ts1_minus+max_ts2_plus, R, zero_exp, c_minus_exp); // NON-DB
                                        z3::expr item2 = ts1_plus == empty && ts2_minus == empty && item_to_qgdbs(min_ts1_minus, max_ts2_plus, R, -c);

                                        return item1 || item2 || item4 || item3;
                                } else if (R == "=" || R == "<=") {
                                        if (R == "<=") R = ">=";
                                        // z3::expr item2 = ts1_plus == empty && ts2_minus == empty && expr_tool::mk_item(min_ts1_minus+max_ts2_plus, R, zero_exp, c_minus_exp); // NON-DB
                                        z3::expr item2 = ts1_plus == empty && ts2_minus == empty && item_to_qgdbs(min_ts1_minus, max_ts2_plus, R, -c);

                                        return item1 || item2 || item3;
                                }
                        } else if (case_i == 5) {
                                // max(Ts) R max(Ts) + c
                                z3::expr item1 =  expr_tool::mk_item(max_ts1_plus, R, max_ts2_plus, c_exp);
                                z3::expr item3 = ts1_plus == empty && ts2_plus == empty && expr_tool::mk_item(min_ts2_minus, R, min_ts1_minus, c_exp);
                                if ( R == ">=") {
                                        z3::expr item4 = ts1_plus != empty && ts2_minus != empty && ts2_plus == empty;
                                        R = "<=";
                                        // z3::expr item2 = ts1_plus == empty && expr_tool::mk_item(max_ts2_plus+min_ts1_minus, R, zero_exp, c_minus_exp); // NON-DB
                                        z3::expr item2 = ts1_plus == empty && item_to_qgdbs(min_ts1_minus, max_ts2_plus, R, -c);

                                        return item1 || item2 || item4 || item3;
                                } else if (R == "=" || R == "<=") {
                                        if (R == "<=") R = ">=";
                                        // z3::expr item2 = ts1_plus == empty && expr_tool::mk_item(max_ts2_plus+min_ts1_minus, R, zero_exp, c_minus_exp); // NON-DB

                                        z3::expr item2 = ts1_plus == empty && item_to_qgdbs(min_ts1_minus, max_ts2_plus, R, -c);

                                        return item1 || item2  || item3;
                                }
                        }
                }
                */

        }
}

/**
 * translate t_i_1 = c
 */
z3::expr qgdbs_translator::translate_qgdbs_minus(z3::expr t_i_1, std::string R, int c) {

        z3::expr zero_exp = m_ctx.int_val(0);
        z3::expr empty = expr_tool::mk_emptyset(m_ctx);
        if (R == ">") {
                R = ">=";
                c += 1;
        } else if (R == "<") {
                c -= 1;
                R = "<=";
        }

        if (c >= 0) {
                // table 1
                z3::expr c_exp = m_ctx.int_val(c);
                if (expr_tool::is_int_const(t_i_1)) {
                        // t_i_1 is x
                        int ctx_x = get_ctx(t_i_1);
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
                        int ctx_x = get_ctx(t_i_1);
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
