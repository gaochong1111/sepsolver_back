#ifndef CSLTP_ORDER_GRAPH_H
#define CSLTP_ORDER_GRAPH_H

#include "edge.h"


class OrderGraph
{
public:
        void addVertex(Vertex v) ;

        /***
         *
         * @return: 1 if ok,
         *         0 if the vertex does not exist in vertex std::set
         */
        int addEdge(Edge edge) ;


        /**
         * saturate the graph
         */
        void saturate() ;


        /**
         * check the order graph is consistent or inconsistent after saturating
         * @return true, if edges do not include (V,<,V)
         *         false, otherwise
         */
        bool isConsistent() ;

        /**
         * @param old_v : the old_v as vertex std::set
         * @param new_v : the new_v as new vertexes which may has the same element.
         * @return 1, if ok
         *         -1, otherwise
         */
        int substitution(const std::vector<Vertex>& old_v, const std::vector<Vertex>& new_v) ;


        /**
         * union graph og into this, vertexes union og.vertexes, edges union og.edges
         * @param og : union graph
         */
        void unionGraph(const OrderGraph& og) ;

        /**
         * restrict the order graph in vertex std::set
         * @param v_std::set : the restriction std::set
         * @return 1, if okay
         *        -1, otherwise
         */
        int restriction(std::set<Vertex>& v_set) ;


        bool operator == (const OrderGraph& og) const ;

        std::set<Vertex> getVertexes();
        std::set<Edge> getEdges();

        void printAsDot(std::string file) ;
private:
        std::string delSpecialChar(std::string str); // process the vertex name , used by printasdot

private:
        std::set<Vertex> vertexes;
        std::set<Edge> edges;
};



#endif // csltp_order_graph.h
