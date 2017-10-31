#ifndef LISTSOLVER_H
#define LISTSOLVER_H

#include "solver.h"
#include "listchecker.h"

class listsolver :public solver {
public:
listsolver(smt2context& ctx) : solver(ctx){}
        void check_preds();
        z3::check_result check_sat();
        z3::check_result check_entl();
        z3::expr pred2abs(z3::expr& atom, int i);
};



#endif /* LISTSOLVER_H */
