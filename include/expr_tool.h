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
        static void get_constants(z3::expr exp,  std::set<z3::expr, exprcomp>& constants_set);

        static void expr_set_to_vec(std::set<z3::expr, exprcomp>& expr_set, std::vector<z3::expr>& expr_vec);
        static bool is_sub_set(std::set<z3::expr, exprcomp>& expr_set1, std::set<z3::expr, exprcomp>& expr_set2);

        static int index_of_exp(z3::expr exp, std::vector<z3::expr>& expr_vec);



};



#endif /* EXPR_TOOL_H */
