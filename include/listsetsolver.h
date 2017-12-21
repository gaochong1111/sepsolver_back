#ifndef LISTSETSOLVER_H
#define LISTSETSOLVER_H
#include "solver.h"

class listsetsolver :public solver {
private:
        void compute_all_tr_closure();
        z3::expr compute_tr_closure(predicate& pred);

        z3::expr get_strt(z3::expr phi_r);
        int get_card(z3::expr item, z3::expr_vector& set_vars);
        z3::expr get_card(int i, z3::expr_vector& set_vars);
        void set_matrix(int (&matrix)[4][4], int i, int j, int val);
        bool floyd(int (&matrix)[4][4]);


        void display(int matrix[4][4], z3::expr_vector& set_vars, std::string file_name);
        void display(int matrix[4][4]);

public:
listsetsolver(smt2context& ctx) : solver(ctx) {}
        void check_preds();
        z3::check_result check_sat();
        z3::check_result check_entl();
        z3::expr pred2abs(z3::expr& atom, int i, z3::expr_vector& new_bools);
        z3::model get_model(){}
};



#endif /* LISTSETSOLVER_H */
