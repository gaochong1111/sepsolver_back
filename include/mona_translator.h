#ifndef MONA_TRANSLATOR_H
#define MONA_TRANSLATOR_H
#include "expr_tool.h"
#include <map>

enum mona_op {
        MONA_AND=1,
        MONA_OR,
        MONA_NOT,
        MONA_IMPLY,
        MONA_LE,
        MONA_LT,
        MONA_GE,
        MONA_GT,
        MONA_EQ,
        MONA_DISTINCT,
        MONA_PLUS,
        MONA_SUBSTRACT,
        // MONA_MUL,
        // MONA_DIV,
        MONA_MIN,
        MONA_MAX,
        MONA_UNION,
        MONA_INTER,
        MONA_MINUS,
        MONA_SUB,
        MONA_IN,
        MONA_SET
};



class mona_translator {
private:
        z3::expr m_formula;
        z3::context& m_ctx;
        std::map<std::string, mona_op> op_map;
private:
        std::string get_decl_str(int order, std::set<z3::expr, exprcomp>& var_set);
        std::string get_quantifier_bounds_str(bool is_all, z3::expr_vector& bounds);
public:
mona_translator(z3::context& ctx, z3::expr formula): m_ctx(ctx), m_formula(formula){
                op_map["and"] = MONA_AND;
                op_map["or"] = MONA_OR;
                op_map["not"] = MONA_NOT;
                op_map["=>"] = MONA_IMPLY;
                op_map["<="] = MONA_LE;
                op_map["<"] = MONA_LT;
                op_map[">="] = MONA_GE;
                op_map[">"] = MONA_GT;
                op_map["="] = MONA_EQ;
                op_map["distinct"] = MONA_DISTINCT;
                op_map["+"] = MONA_PLUS;
                op_map["-"] = MONA_SUBSTRACT;
                //     op_map["*"] = MONA_MUL;
                // op_map["div"] = MONA_DIV;
                op_map["min"] = MONA_MIN;
                op_map["max"] = MONA_MAX;
                op_map["setunion"] = MONA_UNION;
                op_map["setintersect"] = MONA_INTER;
                op_map["setminus"] = MONA_MINUS;
                op_map["subset"] = MONA_SUB;
                op_map["belongsto"] = MONA_IN;
                op_map["set"] = MONA_SET;
        }
        void write_to_file(std::string name);
        std::string get_str(z3::expr item,  int ctx, std::vector<std::set<std::string> >& ctx_set_items);
};




#endif /* MONA_TRANSLATOR_H */
