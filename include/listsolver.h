#ifndef LISTSOLVER_H
#define LISTSOLVER_H

#include "solver.h"
#include "listchecker.h"
#include "graph.h"

class listsolver :public solver {

private:

        // check sat
        z3::expr get_abstraction(z3::expr& formula, z3::expr& space, z3::expr_vector& new_bools);
        z3::expr get_abstraction(z3::expr& formula, z3::expr_vector& new_bools);

        // check entl
        int get_const_vec_and_eq_class(z3::expr& phi, z3::expr phi_abs, std::vector<z3::expr>& const_vec, std::vector<int>& const_eq_class);
        bool get_next_omega(std::vector<int>& curr, std::vector<int>& target);
        void get_omega_phi_abs(z3::expr& phi_abs, graph& g, std::vector<int>& omega, z3::expr& space, z3::expr& omega_phi_abs);

        // match
        bool match_graph(graph& psi_g, graph& omega_g_i);
        bool match_pto(z3::expr& psi_atom, z3::expr& omega_atom);
        bool match_path_to_atom_space(std::vector<int>& paths, z3::expr& atom_space, std::vector<z3::expr>&  oemga_const_vec, std::vector<int>&  omega_const_eq_class_vec, std::vector<int>& omega_eq_to_eq_table);
        bool match_path_to_atom_space(std::vector<int>& paths, z3::expr& atom_space);

        void unfold_by_path(std::vector<int>& path, z3::expr& psi_atom, z3::expr& oemga_f);
        void unfold_pto(predicate& pred, z3::expr& data, std::vector<z3::expr>& atom_space);
        void unfold_pred(predicate& pred, std::vector<z3::expr>& atom_space);


        // construct graph
        void construct_graph(z3::expr& phi_abs, std::vector<z3::expr>& lconsts, z3::expr& space, graph& g);
        void get_eq_class(z3::expr& phi_abs, std::vector<z3::expr>& lconsts, std::vector<std::set<int> >& eq_class_vec,  std::vector<int>& lconst_class);
        void get_eq_class(z3::expr& phi_abs, std::vector<z3::expr>& lconsts, std::vector<std::set<int> >& eq_class_vec);
        void get_edge_from_atom(z3::expr& atom, std::vector<z3::expr>& lconsts, std::pair<std::pair<int, int>, int>& edge);



        // data_closure
        void compute_all_data_closure();
        z3::expr compute_data_closure(predicate& pred);
        z3::expr normalize_item(z3::expr x);
        z3::expr compute_alpha_closure(std::vector<std::vector<z3::expr>>& data_items, z3::expr_vector& xi, z3::expr& gamma_i, z3::expr& beta_i);

        // aux
        int get_numeral(z3::expr x);
        int index_of_vec(z3::expr x, z3::expr_vector& vec);
        void init_int_vector(std::vector<int>& vec, int size);
        int index_of_int(int x, std::vector<int>& vec);



        // output
        bool is_allocated(z3::model& m, z3::expr& source, int n);
        void write_pto(z3::model& m, z3::expr& pto, int i, int n, std::string& node_str, std::string& edge_str);
        void write_pred_pto(z3::model& m, z3::model& data_m, z3::expr& pto, int i, int n, z3::expr& plfld_interp, z3::expr& plfld, int node_i, int k, std::string& node_str, std::string& edge_str);
        z3::expr get_interp(z3::model& m, z3::expr exp);



public:
listsolver(smt2context& ctx) : solver(ctx) {}
        void check_preds();
        z3::check_result check_sat();
        z3::check_result check_entl();
        z3::expr pred2abs(z3::expr& atom, int i, z3::expr_vector& new_bools);
        std::string get_model_of_atom(z3::model& m, z3::expr& atom, int i, int n);
        z3::model get_model();

};



#endif /* LISTSOLVER_H */
