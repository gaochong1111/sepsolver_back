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
                if (exp.is_var() && exp.get_sort().sort_kind() == Z3_UNINTERPRETED_SORT) {
                       lvar_set.insert(exp);
                }
        }
}

void expr_tool::get_consts(z3::expr exp, std::set<z3::expr, exprcomp> &const_set) {
        if (exp.is_app()) {
                if (exp.is_const() && !exp.is_numeral() && !exp.is_array()) {
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
                if (exp.is_const() && !exp.is_numeral() && exp.get_sort().sort_kind() == Z3_UNINTERPRETED_SORT) {
                        lconst_set.insert(exp);
                } else {
                        for (int i=0; i<exp.num_args(); i++) {
                                get_lconsts(exp.arg(i), lconst_set);
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
