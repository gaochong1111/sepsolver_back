#include "fa.h"
#include <iostream>
#include <fstream>


FA::FA(const FA& other) {
        // std::cout << "copy fa.....\n";
        m_init_state = other.m_init_state;
        m_state_num = other.m_state_num;
        m_accept_states.clear();
        set_accept_states(other.m_accept_states);
        m_alphabet.clear();
        set_alphabet_set(other.m_alphabet);
        m_fa = other.m_fa;
}

FA& FA::operator=(const FA& other) {
        // std::cout << "operator = .....\n";
        if (this != &other) {
                m_init_state = other.m_init_state;
                m_state_num = other.m_state_num;
                m_accept_states.clear();
                set_accept_states(other.m_accept_states);
                m_alphabet.clear();
                set_alphabet_set(other.m_alphabet);
                m_fa = other.m_fa;
        }
        return *this;
}



void FA::init() {
        std::cout << "init automata.\n";
}

void FA::set_alphabet_set(const std::vector<std::string> &alphabet)  {
        m_alphabet.insert(m_alphabet.end(), alphabet.begin(), alphabet.end());
        for (int i=0; i<m_alphabet.size(); i++) {
                m_var_to_pos[m_alphabet[i]] = i;
        }
}

void FA::add_states(int n, std::string prefix) {
        m_state_num = n;
        for (int i=0; i<n; i++) {
                boost::add_vertex(m_fa);
                std::string name = prefix;
                name.append(std::to_string(i));
                m_fa[i].push_back(name);
                std::string key = vec_to_str(m_fa[i]);
                m_fa[boost::graph_bundle][key] = i;
        }
}


void FA::add_transition(transition& tr) {
        boost::add_edge(tr.src, tr.dst, tr.info, m_fa);
}

/**
 * interset this and other
 * @param other
 * @param result
 */
FA FA::product(FA& other) {
        FA result;
        if (!is_same_alphabet(other)) {
                std::cout << "THE ALPHABET IS NOT SAME!\n";
                exit(-1);
        }

        result.set_alphabet_set(m_alphabet);
        result.m_state_num = m_state_num * other.m_state_num;
        // accept states
        for (int i=0; i<m_accept_states.size(); i++) {
                for (int j=0; j<other.m_accept_states.size(); j++) {
                        result.m_accept_states.push_back(m_accept_states[i]*other.m_state_num + other.m_accept_states[j]);
                }
        }
        // result.m_accept_states.push_back(result.m_state_num-1);
        // add states
        int index = 0;
        for (int i=0; i<m_state_num; i++) {
                for (int j=0; j<other.m_state_num; j++) {
                        boost::add_vertex(result.m_fa);
                        result.m_fa[index].insert(result.m_fa[index].end(), m_fa[i].begin(), m_fa[i].end());
                        result.m_fa[index].insert(result.m_fa[index].end(), other.m_fa[j].begin(), other.m_fa[j].end());
                        std::string key = vec_to_str(result.m_fa[index]);
                        result.m_fa[boost::graph_bundle][key] = index;
                        index++;
                }
        }
        // add transitions
        std::vector<int> work_list;
        std::set<int> state_set;
        work_list.push_back(0);

        while(work_list.size() != 0) {
                int cur_state = work_list.back();
                // std::cout << "cur_state: " << cur_state << std::endl;
                work_list.pop_back();

                if (state_set.find(cur_state) != state_set.end()) {
                        continue;
                }
                state_set.insert(cur_state);

                int i = cur_state / other.m_state_num;
                int j = cur_state % other.m_state_num;

                automata::out_edge_iterator i_start, i_end;
                tie(i_start, i_end) = boost::out_edges(i, m_fa);
                for (; i_start != i_end; ++i_start) {
                        // edge : i-> i_target
                        int i_target = boost::target(*i_start, m_fa);
                        std::vector<std::string> i_edge = m_fa[*i_start];

                        automata::out_edge_iterator j_start, j_end;
                        tie(j_start, j_end) = boost::out_edges(j, other.m_fa);
                        for(; j_start != j_end; ++j_start) {
                                // edge: j->j_target
                                int j_target = boost::target(*j_start, other.m_fa);
                                std::vector<std::string> j_edge = other.m_fa[*j_start];
                                std::vector<std::string> r_edge;
                                if (interset_edge(i_edge, j_edge, r_edge)) {
                                        int r_target = i_target*other.m_state_num + j_target;
                                        if (state_set.find(r_target) == state_set.end()) {
                                                work_list.push_back(r_target);
                                        }
                                        // r_src -> r_target : r_edge
                                        // std::cout << "add edge: " << cur_state << "->" << r_target << std::endl;
                                        boost::add_edge(cur_state, r_target, r_edge, result.m_fa);
                                }
                        }
                }

        }

        return result;
}

/**
 * state -> edge
 * get new FA
 * @return
 */
FA FA::state_as_edge() {
        FA result;
        result.m_init_state = 0;
        result.m_state_num = m_state_num + 1;
        for (int i=0; i<m_accept_states.size(); i++) {
                result.m_accept_states.push_back(m_accept_states[i]+1);
        }

        result.add_states(result.m_state_num, "q");

        int edge_count = 0;
        // add transition
        boost::add_edge(0, 1, m_fa[0], result.m_fa);
        for (int i=0; i<m_state_num; i++) {
                automata::out_edge_iterator i_start, i_end;
                tie(i_start, i_end) = boost::out_edges(i, m_fa);
                for (; i_start != i_end; ++i_start) {
                        edge_count ++;
                        int i_target = boost::target(*i_start, m_fa);
                        boost::add_edge(i+1, i_target+1, m_fa[i_target], result.m_fa);
                        std::string key = vec_to_str(m_fa[i_target]);
                        result.m_fa[boost::graph_bundle][key] = m_fa[boost::graph_bundle][key];
                }
        }
        std::cout << "state_count: " << result.m_state_num << std::endl;
        std::cout << "edge_count: " << edge_count << std::endl;
        return result;
}


/**
 * pre: PA is special: one init state, one accept state
 * PA -> expr
 * expr = consitent_phi and connected_phi and sigma_item
 * @param accept_state : accept state id
 * @param x_ids : flow related to new var x_ids
 */
z3::expr FA::to_expr(z3::context& ctx, int accept_state, std::set<int>& x_ids, std::set<z3::expr, exprcomp>& tpaq_set) {
        z3::expr result = ctx.bool_val(true);
        // consitent
        std::map<std::string, std::vector<z3::expr> > xi_to_tpaq; // x_i = \Sigma (x_paq)
        // init
        for (int i=0; i<m_state_num-1; i++) {
                std::string x_i_name = "x_";
                x_i_name.append(std::to_string(i));
                xi_to_tpaq[x_i_name].push_back(ctx.int_val(0));
        }

        z3::expr_vector consistent_items(ctx); // consistent_items
        z3::expr_vector connected_items(ctx); // conneted_items
        bool is_accept = false; // check have and only have one accept state
        std::vector<int> work_list;
        work_list.push_back(accept_state);

        std::set<int> visited;
        while(work_list.size() > 0) {
                int i = work_list.back();
                work_list.pop_back();
                if (visited.find(i) != visited.end()) {
                        continue;
                }
                visited.insert(i);
                automata::in_edge_iterator i_start, i_end;
                tie(i_start, i_end) = boost::in_edges(i, m_fa);
                // mk x_i
                std::string u_i_name = "u_";
                u_i_name.append(std::to_string(i));
                z3::expr u_i = ctx.int_const(u_i_name.c_str());

                z3::expr_vector or_items(ctx);

                z3::expr_vector in_items(ctx);
                if (i==0) {
                        in_items.push_back(ctx.int_val(1));
                        is_accept = true;
                }
                for (; i_start != i_end; ++i_start) {
                        int i_src = boost::source(*i_start, m_fa);

                        if (visited.find(i_src) == visited.end()) {
                                work_list.push_back(i_src);
                        }

                        std::string key = vec_to_str(m_fa[*i_start]);
                        int i_edge = m_fa[boost::graph_bundle][key];

                        // make var t_p_a_q
                        std::string name = "t_";
                        name.append(std::to_string(i_src)).append("_").append(std::to_string(i_edge)).append("_").append(std::to_string(i));
                        z3::expr t_p_a_q = ctx.int_const(name.c_str());
                        in_items.push_back(t_p_a_q);


                        // insert x_i
                        std::string x_i_key = "x_";
                        x_i_key.append(std::to_string(i_edge));
                        xi_to_tpaq[x_i_key].push_back(t_p_a_q);

                        x_ids.insert(i_edge); // add x_id

                        // make var u_
                        std::string u_j_name = "u_";
                        u_j_name.append(std::to_string(i_src));
                        z3::expr u_j = ctx.int_const(u_j_name.c_str());
                        or_items.push_back(u_i > u_j);
                }


                automata::out_edge_iterator o_start, o_end;
                tie(o_start, o_end) = boost::out_edges(i, m_fa);
                z3::expr_vector out_items(ctx);
                if (i==accept_state) {
                        out_items.push_back(ctx.int_val(1));
                        // is_accept = true;
                }
                for (; o_start != o_end; ++o_start) {
                        int i_target = boost::target(*o_start, m_fa);

                        if (visited.find(i_target) != visited.end()) {
                                std::string key = vec_to_str(m_fa[*o_start]);
                                int i_edge = m_fa[boost::graph_bundle][key];
                                // make var t_p_a_q
                                std::string name = "t_";
                                name.append(std::to_string(i)).append("_").append(std::to_string(i_edge)).append("_").append(std::to_string(i_target));
                                z3::expr t_p_a_q = ctx.int_const(name.c_str());
                                out_items.push_back(t_p_a_q);

                                // make var u_

                                std::string u_j_name = "u_";
                                u_j_name.append(std::to_string(i_target));
                                z3::expr u_j = ctx.int_const(u_j_name.c_str());
                                or_items.push_back(u_i > u_j);
                        }
                }

                if (in_items.size() == 0) {
                        std::cout << "state: " << i << ", indegree is zero\n";
                        exit(-1);
                }
                if (out_items.size() == 0) {
                        std::cout << "state: " << i << ", outdegree is zero\n";
                        exit(-1);
                }

                z3::expr i_item = (z3::sum(in_items) == z3::sum(out_items));
                consistent_items.push_back(i_item);

                if (i == 0) {
                        connected_items.push_back(u_i == 0);
                } else {
                        z3::expr u_i_item = (u_i > 0) && z3::mk_or(or_items);
                        connected_items.push_back(u_i_item);
                }
        }

        if (!is_accept) {
                // init -> accept is conneted
                return ctx.bool_val(false);
        }
        // consitent phi
        z3::expr consistent_phi = z3::mk_and(consistent_items);
        // std::ofstream out("consitent.smt");
        // out << consistent_phi << std::endl;
        // out.close();

        // connected_phi
        z3::expr connected_phi = z3::mk_and(connected_items);
        // std::ofstream out1("connected.smt");
        // out1 << connected_phi << std::endl;
        // out1.close();

        // sigma items
        z3::expr_vector sum_items(ctx);
        // std::set<z3::expr, exprcomp> tpaq_set;

        for (int i=0; i<m_state_num-1; i++) {
                std::string x_i_name = "x_";
                x_i_name.append(std::to_string(i));
                z3::expr x_i = ctx.int_const(x_i_name.c_str());
                z3::expr_vector s_items(ctx);
                for (int j=0; j<xi_to_tpaq[x_i_name].size(); j++) {
                        s_items.push_back(xi_to_tpaq[x_i_name][j]);
                        tpaq_set.insert(xi_to_tpaq[x_i_name][j]);
                }
                sum_items.push_back(x_i == z3::sum(s_items));
        }

        z3::expr_vector ge_zero_items(ctx);

        std::cout << "tpaq size: " << tpaq_set.size() << std::endl;

        for (z3::expr tpaq : tpaq_set) {
                ge_zero_items.push_back(tpaq>=0);
        }
        z3::expr ge_zero = z3::mk_and(ge_zero_items);

        z3::expr sum_phi = z3::mk_and(sum_items);

        z3::expr phi = consistent_phi && connected_phi && sum_phi  && ge_zero;

        return phi;
}

void FA::print(std::string name) {
        std::cout << "write graph into " << name << std::endl;
        std::ofstream out(name);

        // out vertex
        std::pair<vertex_iter, vertex_iter> vp;
        vertex_t v;
        index_t index;
        size_t num = boost::num_vertices(m_fa);

        out << "digraph g {\n";

        // out vertex
        for (vp = vertices(m_fa); vp.first!=vp.second; ++vp.first) {
                v = *vp.first;

                std::vector<std::string> node = m_fa[v];
                out << "node_" << index[v] << " [label=\"";
                out << vec_to_str(node);
                out << "\"];\n";
        }
        out << "\n";

        // out edges

        vertex_t v1, v2;
        std::pair<edge_iter, edge_iter> ep;
        edge_iter ei, ei_end;
        for (tie(ei, ei_end)=edges(m_fa); ei!=ei_end; ++ei) {
                v1 = boost::source(*ei, m_fa);
                v2 = boost::target(*ei, m_fa);

                out << "node_" << index[v1] << " -> " << "node_" << index[v2] << "[label=\"";

                std::vector<std::string> edge = m_fa[*ei];

                out << vec_to_str(edge);

                out << "\"];\n";
        }

        out << "}\n";


        out.close();
}


void FA::print_model(std::set<int>& ids, z3::model& model, z3::context& ctx) {
        assert(ids.find(0) != ids.end());

        std::ofstream out("model.dot");
        out << "digraph {\n";

        std::vector<int> work_list;
        std::set<int> state_set;
        work_list.push_back(0);

        for (int i=0; i<m_accept_states.size(); i++) {
                out << "node_" << m_accept_states[i] << "_1 [shape = doublecircle];\n";
        }

        while(work_list.size() != 0) {
                int cur_state = work_list.back();
                // std::cout << "cur_state: " << cur_state << std::endl;
                work_list.pop_back();

                if (state_set.find(cur_state) != state_set.end()) {
                        continue;
                }
                state_set.insert(cur_state);

                std::string src_name = "x_";
                src_name.append(std::to_string(cur_state));
                z3::expr x_src = ctx.int_const(src_name.c_str());

                z3::expr src_val = model.get_const_interp(x_src.decl());

                // std::cout << "state: " << cur_state << ": " << src_val << std::endl;

                if (src_val.get_numeral_int() > 0) {
                        automata::out_edge_iterator i_start, i_end;
                        tie(i_start, i_end) = boost::out_edges(cur_state, m_fa);
                        for (; i_start != i_end; ++i_start) {
                                // edge : i -> i_target
                                int i_target = boost::target(*i_start, m_fa);

                                if (ids.find(i_target) != ids.end()) {
                                        std::string dst_name = "x_";
                                        dst_name.append(std::to_string(i_target));
                                        z3::expr x_dst = ctx.int_const(dst_name.c_str());

                                        z3::expr dst_val = model.get_const_interp(x_dst.decl());

                                        // std::cout << "state: " << i_target << ": " << dst_val << std::endl;

                                        if (dst_val.get_numeral_int() > 0) {
                                                if (state_set.find(i_target) == state_set.end()) {
                                                        work_list.push_back(i_target);
                                                }

                                                std::vector<std::string> i_edge = m_fa[*i_start];
                                                std::string edge_info = vec_to_str(i_edge);

                                                out << "node_" << cur_state << "_" << src_val << " -> " << "node_" << i_target << "_" << dst_val << "[label=\""<< edge_info <<"\"]\n";

                                        }
                                }
                        }
                }
        }

        out << "}\n";

        out.close();
}



void FA::print_flow(int accept_state) {

        std::ofstream out("flow.dot");
        bool is_accept = false; // check have and only have one accept state
        std::vector<int> work_list;
        work_list.push_back(accept_state);


        out << "digraph {\n";


        out << "node_" << accept_state << " [shape = doublecircle];\n";


        std::set<int> visited;
        while(work_list.size() > 0) {
                int i = work_list.back();
                work_list.pop_back();
                if (visited.find(i) != visited.end()) {
                        continue;
                }
                visited.insert(i);
                automata::in_edge_iterator i_start, i_end;
                tie(i_start, i_end) = boost::in_edges(i, m_fa);

                if (i==0) {
                        is_accept = true;
                }
                for (; i_start != i_end; ++i_start) {
                        int i_src = boost::source(*i_start, m_fa);

                        if (visited.find(i_src) == visited.end()) {
                                work_list.push_back(i_src);
                        }

                        std::string key = vec_to_str(m_fa[*i_start]);

                        out << "node_" << i_src << " -> " << "node_" << i  << "[label=\""<< key <<"\"]\n";
                }
        }

        if (!is_accept) {
                // init -> accept is conneted
                std::cout << "flow is NON-CONNECTED!\n";
                exit(-1);
        }

        out << "}\n";


        out.close();

}


std::string FA::vec_to_str(std::vector<std::string>& vec, std::string sep) {
        if (vec.size() == 0) return "";
        std::string result;
        result.append(vec[0]);
        for (int i=1; i<vec.size(); i++) {
                result.append(sep).append(vec[i]);
        }
        return result;
}

bool FA::is_same_alphabet(FA& other) {
        bool result = m_alphabet.size() == other.m_alphabet.size();
        for (int i=0; result && i<m_alphabet.size(); i++) {
                if (m_alphabet[i] != other.m_alphabet[i]) result = false;
        }

        return result;
}

/**
 * vec1 inter vec2
 * @param vec1 : [XX01XX]
 * @param vec2 : [XX11XX]
 * @param result: []
 * @return false, if empty
 */
bool FA::interset_edge(std::vector<std::string> &vec1, std::vector<std::string> &vec2, std::vector<std::string> &result) {
        assert(vec1.size() == vec2.size());
        for (int i=0; i<vec1.size(); i++) {
                int case_i = 0;
                if (vec1[i] == "0") case_i += 1;
                if (vec1[i] == "1") case_i += 2;
                if (vec2[i] == "0") case_i += 3;
                if (vec2[i] == "1") case_i += 6;
                switch(case_i) {
                case 0:
                        result.push_back("X");
                        break;
                case 1:
                case 3:
                case 4:
                        result.push_back("0");
                        break;
                case 2:
                case 6:
                case 8:
                        result.push_back("1");
                        break;
                case 5:
                case 7:
                        return false;
                        break;
                default:
                        std::cout << "FA PRODUCT EDGE INTERSET ERROR!\n";
                        exit(-1);
                }
        }
        return true;
}
