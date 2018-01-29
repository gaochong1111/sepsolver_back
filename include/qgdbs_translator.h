#ifndef QGDBS_TRANSLATOR_H
#define QGDBS_TRANSLATOR_H

#include "expr_tool.h"
#include "log.h"

class qgdbs_translator {
private:
        z3::expr m_formula;
        z3::context& m_ctx;

        std::vector<z3::expr> m_first_order_vars;
        std::vector<z3::expr> m_second_order_vars;
        std::vector<int> m_fovar_ctx; //  [0: +, 1: -]
        std::vector<int> m_sovar_ctx; // [0:+, 1:-, 2:+-, 3: bot]
        std::vector<z3::expr> m_bounds;
        // std::vector<z3::expr> m_so_bounds;
        // int m_bctx;
        std::vector<int> m_bounds_ctx;

        int m_index;

        z3::expr_vector m_ctx_items; // [index(ectx) : item]



private:
        // void get_first_order_vars(z3::expr exp, std::set<z3::expr, exprcomp>& vars_set);

        int plus_one_foctx();
        int plus_one_soctx();
        int plus_one_ctx();
        int plus_one_bctx();

        void init_ctx();


        bool has_quantified_var(z3::expr delta, std::set<z3::expr, exprcomp>& var_set);
        int translate_fo_item(z3::expr var, z3::expr& result);
        z3::expr translate_formula(z3::expr formula);
        z3::expr translate_formula_plus(z3::expr formula);
        z3::expr translate_formula_minus(z3::expr formula);
        z3::expr translate_qgdbs_minus(z3::expr t_i_1, std::string R, int c);
        z3::expr translate_qgdbs_minus(z3::expr t_i_1, std::string R, z3::expr t_i_2, int c);
        z3::expr translate_qgdbs_minus_new(z3::expr t_i_1, std::string R, z3::expr t_i_2, int c);
        z3::expr bctx_to_expr(z3::expr_vector& bounds, int start);
        z3::expr item_to_qgdbs(z3::expr t_i_1, z3::expr t_i_2, std::string R, int c);
        z3::expr ectx_to_expr();
public:
qgdbs_translator(z3::context& z3_ctx, z3::expr formula):m_ctx(z3_ctx), m_formula(formula),  m_index(-1), m_ctx_items(z3_ctx) {}



        z3::expr generate_formula();
        int formula_size();
        z3::expr get_formula(int i);
        bool get_next();

        void translate_formula_ctx(z3::expr& formula);
        void prepare();
        void print_ctx();
        void set_first_order_vars(std::set<z3::expr, exprcomp>& fo_vars_set);
        void set_second_order_vars(std::set<z3::expr, exprcomp>& so_vars_set);
        int get_ctx(z3::expr exp);




};



#endif /* QGDBS_TRANSLATOR_H */
