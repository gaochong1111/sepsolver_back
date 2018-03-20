#ifndef FA_H
#define FA_H

#include <vector>
#include <set>
#include <map>

#include <boost/config.hpp>
#include <boost/utility.hpp>
#include <boost/graph/adjacency_list.hpp>
#include <boost/graph/graph_traits.hpp>


#include <z3++.h>
#include "expr_tool.h"

class transition {
public:
        int src;
        int dst;
        std::vector<std::string> info;
public:
        bool operator<(const transition& other) const{
                return src<other.src || (src==other.src && dst<other.dst);
        }
};

class FA {
public:
        typedef std::vector<std::string> vertex_label;
        typedef std::vector<std::string> edge_label;
        typedef std::map<std::string, int>  graph_label;
        typedef boost::adjacency_list<boost::vecS,
                boost::vecS,
                boost::bidirectionalS,
                vertex_label,
                edge_label,
                graph_label> automata;

        typedef boost::graph_traits<automata>::vertex_iterator vertex_iter;
        typedef boost::graph_traits<automata>::edge_iterator edge_iter;
        typedef boost::property_map<automata, boost::vertex_index_t>::type index_t;
        typedef automata::vertex_descriptor vertex_t;
        typedef automata::edge_descriptor edge_t;

        automata m_fa;

        int m_init_state;
        int m_state_num;
        std::vector<int> m_accept_states;
        std::vector<std::string> m_alphabet;
        std::map<std::string, int> m_var_to_pos;
public:
        FA(){}
        FA(const FA& other);
        FA& operator=(const FA& other);
        void init();
        void set_init_state(const int i_state) {m_init_state = i_state;}
        void set_accept_states(const std::vector<int>& accept_states) {m_accept_states.insert(m_accept_states.end(), accept_states.begin(), accept_states.end());}
        std::vector<int> get_accept_states() {return m_accept_states;}
        void set_alphabet_set(const std::vector<std::string>& alphabet);

        std::vector<std::string> get_alphabet() {return m_alphabet;}

        void add_states(int n, std::string prefix);
        int get_state_num() {return m_state_num;}

        void add_transition(transition& tr);

        FA product(FA& other);
        FA state_as_edge();

        z3::expr to_expr(z3::context& ctx, int accept_state, std::set<int>& x_ids, std::set<z3::expr, exprcomp>& tpaq_set);
        FA get_flow(int accept);

        void print(std::string name);

        void print_flow(int accept_state);

        void print_model(std::string file_name, std::set<int>& ids, std::map<std::string, int>& edge_to_count, z3::model& model, z3::context& ctx,  std::vector<std::vector<std::string> >& word);

        std::string vec_to_str(std::vector<std::string>& vec, std::string sep=",");

        int get_pos(std::string str) {return m_var_to_pos[str];}

        bool has_path(int src, int dst,  std::set<int>& ids, std::map<std::string, int>& edge_count);


private:
        void get_valid_states(int accept_state, std::set<int>& valid_ids);
        bool is_same_alphabet(FA& other);
        bool interset_edge(std::vector<std::string>& vec1, std::vector<std::string>& vec2, std::vector<std::string>& result);



};


#endif /* FA_H */
