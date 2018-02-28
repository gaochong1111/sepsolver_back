#ifndef LISTSETSOLVER_H
#define LISTSETSOLVER_H
#include "solver.h"
#include <map>

class listsetsolver :public solver {
private:
        std::vector<std::pair<z3::expr, z3::expr> > m_set_pairs;
        std::vector<z3::expr> m_free_items;
        std::vector<z3::expr> m_pred_tms;
private:
        void compute_all_tr_closure();
        bool check_data(z3::expr& data);
        z3::expr compute_tr_closure(predicate& pred);
        z3::expr compute_tr_by_case(int case_i, z3::expr& phi_r1, z3::expr& strt_phi_r2, z3::expr_vector& phi_r2_items, z3::expr_vector& set_vars);
        z3::expr compute_tr_by_case_02(int case_i, z3::expr& phi_r1, z3::expr& strt_phi_r2, z3::expr_vector& phi_r2_items, z3::expr_vector& set_vars);
        z3::expr compute_tr_by_case_13(int case_i, z3::expr& phi_r1, z3::expr& strt_phi_r2, z3::expr_vector& phi_r2_items, z3::expr_vector& set_vars);
        z3::expr compute_tr_by_case4(z3::expr& phi_r1, z3::expr& strt_phi_r2, z3::expr_vector& phi_r2_items, z3::expr_vector& set_vars);
        z3::expr compute_tr_by_case5(z3::expr& phi_r1, z3::expr& strt_phi_r2, z3::expr_vector& phi_r2_items, z3::expr_vector& set_vars);
        void quant_elmt(z3::expr_vector& tms, z3::expr_vector& quant_elmts);

        int get_strt(z3::expr phi_r, z3::expr& strt_phi_r2, z3::expr_vector& set_vars, z3::expr_vector& phi_r2_items);

        int get_card(z3::expr item, z3::expr_vector& set_vars);
        z3::expr get_card(int i, z3::expr_vector& set_vars);
        void set_matrix(int (&matrix)[4][4], int i, int j, int val);
        bool floyd(int (&matrix)[4][4]);
        z3::expr get_ij_expr(int matrix[4][4], int i, int j, z3::expr_vector& set_vars);


        void display(int matrix[4][4], z3::expr_vector& set_vars, std::string file_name);
        void display(int matrix[4][4]);

        void display_model(std::set<z3::expr, exprcomp>& bool_vars,  std::set<z3::expr, exprcomp>& fo_vars,  std::set<z3::expr, exprcomp>& so_vars,  std::map<std::string, std::string>& model);

        std::string merge_model_val(std::string& minus_val, std::string& plus_val);

public:
listsetsolver(smt2context& ctx) : solver(ctx) {}
        void check_preds();
        z3::check_result check_sat();
        z3::check_result check_entl();
        z3::expr pred2abs(z3::expr& atom, int i, z3::expr_vector& new_bools);
        z3::model get_model(){}
};



#endif /* LISTSETSOLVER_H */
