#ifndef CSLTP_ORDER_GRAPH_SET_H
#define CSLTP_ORDER_GRAPH_SET_H

#include "csltp_order_graph.h"

class OrderGraphSet
{
public:
        /**
         * if og does not exist then  insert it.
         * @params og
         */
        void addOrderGraph(OrderGraph og) ;

        bool isExist(const OrderGraph& og) const;

        int size() ;

        OrderGraph at(unsigned int i) ;

        bool operator == (const OrderGraphSet& ogset) const;

private:
        std::vector<OrderGraph> graphs;
};


#endif /* CSLTP_ORDER_GRAPH_SET_H */
