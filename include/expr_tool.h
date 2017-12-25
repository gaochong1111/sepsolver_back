#ifndef EXPR_TOOL_H
#define EXPR_TOOL_H

#include <z3++.h>
#include <set>
#include <vector>

/**
 * the expr comparator
 */
class exprcomp {
public:
        bool operator() (const z3::expr& lhs, const z3::expr& rhs) const {
                return lhs.hash() < rhs.hash();
        }
};


class expr_tool {
public:
        static void get_vars(z3::expr exp, std::set<z3::expr, exprcomp>& var_set);
        static void get_lvars(z3::expr exp, std::set<z3::expr, exprcomp>& lvar_set);
        static void get_consts(z3::expr exp, std::set<z3::expr, exprcomp>& const_set);
        static void get_lconsts(z3::expr exp, std::set<z3::expr, exprcomp>& lconst_set);
        static void get_dconsts(z3::expr exp, std::set<z3::expr, exprcomp>& dconst_set);
        static void get_constants(z3::expr exp,  std::set<z3::expr, exprcomp>& constants_set);

        static void expr_set_to_vec(std::set<z3::expr, exprcomp>& expr_set, std::vector<z3::expr>& expr_vec);
        static bool is_sub_set(std::set<z3::expr, exprcomp>& expr_set1, std::set<z3::expr, exprcomp>& expr_set2);
        static void union_set(std::set<z3::expr, exprcomp>& expr_set1, std::set<z3::expr, exprcomp>& expr_set2, std::set<z3::expr, exprcomp>& expr_set3);
        static void inter_set(std::set<z3::expr, exprcomp>& expr_set1, std::set<z3::expr, exprcomp>& expr_set2, std::set<z3::expr, exprcomp>& expr_set3);
        static void diff_set(std::set<z3::expr, exprcomp>& expr_set1, std::set<z3::expr, exprcomp>& expr_set2, std::set<z3::expr, exprcomp>& expr_set3);

        static void get_all_field_of_pto(z3::expr pto, std::vector<z3::expr> fields);


        static int index_of_exp(z3::expr exp, std::vector<z3::expr>& expr_vec);
        static bool is_constant(z3::expr exp);
        static bool is_fun(z3::expr expr, std::string fname);
        static bool is_location(z3::expr exp);
        static bool is_setint(z3::expr exp);
        static bool contain_setint(z3::expr exp);

        static z3::expr eq_exp(z3::context& ctx, z3::expr exp1, z3::expr exp2);
        static z3::expr mk_min_max(z3::context& ctx, int mm, z3::expr exp);

        static z3::expr mk_emptyset(z3::context& ctx);
        static z3::expr mk_set_var(z3::context& ctx, std::string name);
        static z3::expr mk_binary_set(z3::context& ctx, std::string name, z3::expr s1, z3::expr s2);
        static z3::expr mk_binary_bool(z3::context& ctx, std::string name, z3::expr s1, z3::expr s2);

        static z3::expr mk_belongsto(z3::context& ctx, z3::expr x, z3::expr S);

        static z3::expr mk_single_set(z3::context& ctx, z3::expr x);




};



#endif /* EXPR_TOOL_H */
