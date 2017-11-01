#ifndef TREECHECKER_H
#define TREECHECKER_H

#include "checker.h"

class treechecker :public checker {
private:
        bool is_data_var(z3::expr x);
        bool is_size_var(z3::expr x);

public:
treechecker(predicate pred):checker(pred){}
        void check_args();
        void check_rec_rule(pred_rule& rule);
        void check_rec_rules();
};




#endif /* TREECHECKER_H */
