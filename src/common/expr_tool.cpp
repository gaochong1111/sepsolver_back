#include "expr_tool.h"

void expr_tool::get_vars(z3::expr exp, std::set<z3::expr, exprcomp> &var_set) {
        if (exp.is_app()) {
                for (int i=0; i<exp.num_args(); i++) {
                        get_vars(exp.arg(i), var_set);
                }
        } else {
                if (exp.is_var()) {
                        var_set.insert(exp);
                }
        }
}

void expr_tool::get_lvars(z3::expr exp, std::set<z3::expr, exprcomp> &lvar_set) {
        if (exp.is_app()) {
                for (int i=0; i<exp.num_args(); i++) {
                        get_lvars(exp.arg(i), lvar_set);
                }
        } else {
                if (exp.is_var() && is_location(exp)) {
                       lvar_set.insert(exp);
                }
        }
}

void expr_tool::get_consts(z3::expr exp, std::set<z3::expr, exprcomp> &const_set) {
        if (exp.is_app()) {
                if (exp.is_const() && !is_constant(exp) && !exp.is_array()) {
                        const_set.insert(exp);
                } else {
                        for (int i=0; i<exp.num_args(); i++) {
                                get_consts(exp.arg(i), const_set);
                        }
                }
        }
}

void expr_tool::get_lconsts(z3::expr exp, std::set<z3::expr, exprcomp> &lconst_set) {
        if (exp.is_app()) {
                if (exp.is_const() && !is_constant(exp) && !exp.is_array() && is_location(exp)) {
                        lconst_set.insert(exp);
                } else {
                        for (int i=0; i<exp.num_args(); i++) {
                                get_lconsts(exp.arg(i), lconst_set);
                        }
                }
        }
}

void expr_tool::get_dconsts(z3::expr exp, std::set<z3::expr, exprcomp> &dconst_set) {
        if (exp.is_app()) {
                if (exp.is_const() && !is_constant(exp) && !exp.is_array() && !is_location(exp)) {
                        dconst_set.insert(exp);
                } else {
                        for (int i=0; i<exp.num_args(); i++) {
                                get_dconsts(exp.arg(i), dconst_set);
                        }
                }
        }
}


void expr_tool::get_constants(z3::expr exp, std::set<z3::expr, exprcomp> &constants_set) {
        if (exp.is_app()) {
                if (exp.is_numeral()) {
                        constants_set.insert(exp);
                } if((exp.decl().name().str() == "to_real" || exp.decl().name().str() == "to_int")){
                        constants_set.insert(exp.arg(0));
                }else {
                        for (unsigned i=0; i<exp.num_args(); i++) {
                                get_constants(exp.arg(i), constants_set);
                        }
                }
        } else if(exp.is_quantifier()) {
                get_constants(exp.body(), constants_set);
        }
}


void expr_tool::get_all_field_of_pto(z3::expr pto, std::vector<z3::expr> fields) {
        if (is_fun(pto, "pto")) {
                z3::expr sref = pto.arg(1);
                if (is_fun(sref, "ref")) {
                        fields.push_back(sref.arg(1));
                } else {
                        for (int i=0; i<sref.num_args(); i++) {
                                fields.push_back(sref.arg(i).arg(1));
                        }
                }
        }
}

void expr_tool::expr_set_to_vec(std::set<z3::expr, exprcomp> &expr_set, std::vector<z3::expr> &expr_vec) {
        for (auto e : expr_set) {
                expr_vec.push_back(e);
        }
}

bool expr_tool::is_sub_set(std::set<z3::expr, exprcomp> &expr_set1, std::set<z3::expr, exprcomp> &expr_set2) {
        for (auto e : expr_set1) {
                if (expr_set2.find(e) == expr_set2.end()) return false;
        }
        return true;
}

void expr_tool::diff_set(std::set<z3::expr, exprcomp> &expr_set1, std::set<z3::expr, exprcomp> &expr_set2, std::set<z3::expr, exprcomp> &expr_set3) {
        for (auto e : expr_set1) {
                if (expr_set2.find(e) == expr_set2.end()) expr_set3.insert(e);
        }
}

void expr_tool::union_set(std::set<z3::expr, exprcomp> &expr_set1, std::set<z3::expr, exprcomp> &expr_set2, std::set<z3::expr, exprcomp> &expr_set3) {
        for (auto e : expr_set1) {
               expr_set3.insert(e);
        }
        for (auto e : expr_set2) {
                expr_set3.insert(e);
        }
}

void expr_tool::inter_set(std::set<z3::expr, exprcomp> &expr_set1, std::set<z3::expr, exprcomp> &expr_set2, std::set<z3::expr, exprcomp> &expr_set3) {
        for (auto e : expr_set1) {
                if (expr_set2.find(e) != expr_set2.end()) expr_set3.insert(e);
        }
}

int expr_tool::index_of_exp(z3::expr exp, std::vector<z3::expr> &expr_vec) {
        for (int i=0; i<expr_vec.size(); i++) {
                if (exp.hash() == expr_vec[i].hash()) return i;
        }
        return -1;
}


bool expr_tool::is_constant(z3::expr exp) {
        if (exp.to_string() == "true" || exp.to_string()=="false" || exp.is_numeral()) return true;
        return false;
}

bool expr_tool::is_fun(z3::expr expr, std::string fname) {
        if (expr.is_app() && expr.decl().name().str() == fname) return true;
        return false;
}

bool expr_tool::is_location(z3::expr exp) {
        if (exp.get_sort().sort_kind() == Z3_UNINTERPRETED_SORT && !is_setint(exp)) return true;
        return false;
}

bool expr_tool::is_setint(z3::expr exp) {
        if (exp.get_sort().to_string() == "SetInt") return true;
        return false;
}

z3::expr expr_tool::eq_exp(z3::context& ctx, z3::expr exp1, z3::expr exp2) {
        if (is_location(exp1)) {
                z3::expr exp1_int = ctx.int_const(exp1.to_string().c_str());
                z3::expr exp2_int = ctx.int_const(exp2.to_string().c_str());
                return exp1_int == exp2_int;
        } else {
                return exp1 == exp2;
        }
}
