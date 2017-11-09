#ifndef LISTSOLVER_H
#define LISTSOLVER_H

#include "solver.h"
#include "listchecker.h"

class listsolver :public solver {
private:
        void compute_all_data_closure();
        z3::expr compute_data_closure(predicate& pred);
        z3::expr normalize_item(z3::expr x);
        int get_numeral(z3::expr x);
        int index_of_vec(z3::expr x, z3::expr_vector& vec);
        z3::expr compute_alpha_closure(std::vector<std::vector<z3::expr>>& data_items, z3::expr_vector& xi, z3::expr& gamma_i, z3::expr& beta_i);

        std::string get_str_field(z3::model& m, z3::expr& ref, std::string& node_name, std::string& edge_str);

public:
listsolver(smt2context& ctx) : solver(ctx){}
        void check_preds();
        z3::check_result check_sat();
        z3::check_result check_entl();
        z3::expr pred2abs(z3::expr& atom, int i);
        std::string get_model_of_atom(z3::model& m, z3::expr& atom, int i);
};



#endif /* LISTSOLVER_H */
