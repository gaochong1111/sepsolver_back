#include "csltp_order_graph_set.h"

/** class OrderGraphSet **/

/**
 * if og does not exist then  insert it.
 * @params og
 */
void OrderGraphSet::addOrderGraph(OrderGraph og) {
        if (!isExist(og)) {
                this->graphs.push_back(og);
        }
}

bool OrderGraphSet::isExist(const OrderGraph& og) const{

        for (unsigned int i=0; i < this->graphs.size(); i++) {
                if (this->graphs[i] == og) {
                        return true;
                }
        }
        return false;
}

int OrderGraphSet::size() {
        return this->graphs.size();
}

OrderGraph OrderGraphSet::at(unsigned int i) {
        if (i<this->graphs.size()) {
                return this->graphs[i];
        }
        OrderGraph og;
        return og;
}

bool OrderGraphSet::operator==(const OrderGraphSet& ogset) const {
        if (this->graphs.size() == ogset.graphs.size()) {
                for (auto graph : this->graphs) {
                        if (!ogset.isExist(graph)) {
                                return false;
                        }
                }
                return true;
        }
        return false;
}
