#ifndef LISTCHECKER_H
#define LISTCHECKER_H

#include "checker.h"

class listchecker :public checker {
public:
listchecker(predicate pred):checker(pred){}
        void check_args();
        void check_rec_rule(pred_rule& rule);
        void check_rec_rules();
};


#endif /* LISTCHECKER_H */
