#ifndef LISTSOLVER_H
#define LISTSOLVER_H

#include "solver.h"
#include "listchecker.h"
#include "graph.h"

class listsolver :public solver {
private:

        // check sat
        z3::expr get_abstraction(z3::expr& formula);
        // check entl
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



        // output
        bool is_allocated(z3::model& m, z3::expr& source, int n);
        void write_pto(z3::model& m, z3::expr& pto, int i, int n, std::string& node_str, std::string& edge_str);
        void write_pred_pto(z3::model& m, z3::model& data_m, z3::expr& pto, int i, int n, z3::expr& plfld_interp, z3::expr& plfld, int node_i, int k, std::string& node_str, std::string& edge_str);


public:
listsolver(smt2context& ctx) : solver(ctx){}
        void check_preds();
        z3::check_result check_sat();
        z3::check_result check_entl();
        z3::expr pred2abs(z3::expr& atom, int i);
        std::string get_model_of_atom(z3::model& m, z3::expr& atom, int i, int n);
};



#endif /* LISTSOLVER_H */
