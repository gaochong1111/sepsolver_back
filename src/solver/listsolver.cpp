#include "listsolver.h"

/**
 *###################### listsolver ####################################
 */
/**
 * check whether all predicate definitions are corresponding to userdef constraints
 */
void listsolver::check_preds() {
        for (int i=0; i<m_ctx.pred_size(); i++) {
                predicate pred = m_ctx.get_pred(i);
                if (pred.is_list()) {
                        listchecker lc(pred);
                        lc.check_args();
                        lc.check_rec_rules();
                }
        }
}

/**
 * check sat, negf in m_ctx
 * or check entl, negf |= posf
 * @return z3::check_result
 */
z3::check_result listsolver::check_sat() {
        logger() << "list sat problem: " << std::endl;
        // 1.1 compute all phi_pd
        compute_all_data_closure();
        z3::expr formula = m_ctx.get_negf();
        z3::expr_vector f_new_bools(z3_ctx());
        z3::expr space(z3_ctx());
        z3::expr f_abs = get_abstraction(formula, space, f_new_bools);
        s.add(f_abs);
        z3::check_result result = s.check();
        return result;
}



z3::model listsolver::get_model() {
    z3::model m = s.get_model();

    z3::expr formula = m_ctx.get_negf();
    z3::expr data(z3_ctx());
    z3::expr space(z3_ctx());
    get_data_space(formula, data, space);

    std::ofstream out("model.dot");
    if (!out) return m;
    out<<"digraph g {\n";
    out<<"graph [rankdir=\"LR\"];\n";
    out<<"node [fontsize=\"16\" shape=\"record\"];\n";

    out << "subgraph cluster1 {\n label=\"(Stack)\"\n";

    int num = m.num_consts();

    out << "satck [label=\"";
    for (int i=0; i<num; i++) {
        z3::func_decl x = m.get_const_decl(i);
        z3::expr x_interp = m.get_const_interp(x);
        if (x.name().str().find("[") != 0) {
            out <<"|" <<x.name() << ":" << x_interp;
        }
    }
    out << "\"]\n";



    out << "}\n";

    out << "subgraph cluster2 {\n label=\"(Heap)\"\n";
    int n = space.num_args();

    for (int i=0; i<n; i++) {
        //1.1 fetch atom
        z3::expr atom = space.arg(i);
        //1.2 get_model_str
        std::string atom_str = get_model_of_atom(m, atom, i, n);
        out << atom_str;
    }

    out<<"}\n}\n";

    out.close();
    return s.get_model();
}


/**
 * get interpretation of exp in m
 * @param m : model
 * @param expr : exp
 * @return expr
 */
z3::expr listsolver::get_interp(z3::model &m, z3::expr exp) {

        z3::expr nil = z3_ctx().int_const("nil");
        // std::cout << "exp: " << exp << std::endl;
        if (exp.get_sort().sort_kind() == Z3_UNINTERPRETED_SORT) {
                z3::expr exp_int = z3_ctx().int_const(exp.to_string().c_str());
                if (m.has_interp(exp_int.decl())) {
                        return m.get_const_interp(exp_int.decl());
                } else if (exp.to_string().find("var_")==0) {
                        return exp;
                }
        } else {
                if (m.has_interp(exp.decl())) {
                        return m.get_const_interp(exp.decl());
                }
        }
        return nil;
}

/**
 * get abstraction of formula
 * @param formula :
 * @param space : the space part of formula
 * @param new_bools : aux output new bool vars
 * @return
 */
z3::expr listsolver::get_abstraction(z3::expr &formula, z3::expr& space, z3::expr_vector& new_bools) {
        logger() << "get abstraction of formula: " << formula << std::endl;
        // 1.2 formula -> (delta \and sigma)
        z3::expr data(z3_ctx());
        get_data_space(formula, data, space);
        z3::expr f_abs = data;

        // 1.3 space part
        f_abs = f_abs && abs_space(space, new_bools);

        // 1.4 sep (\phi_star)
        f_abs = f_abs && abs_phi_star(new_bools);

        return f_abs;
}

z3::expr listsolver::get_abstraction(z3::expr &formula, z3::expr_vector& new_bools) {

        z3::expr space(z3_ctx());
        return get_abstraction(formula, space, new_bools);
}

/**
 * check sat, negf in m_ctx
 * or check entl, negf |= posf
 * @return z3::check_result
 */
z3::check_result listsolver::check_entl() {
        // TODO ....
        logger() << "list entl problem:\n";

        z3::solver ss(z3_ctx());
        z3::expr f_abs = z3_ctx().bool_val(true);
        ss.add(f_abs);
        z3::check_result result = ss.check();

        // TO checking
        assert(m_ctx.pred_size() == 1);

        // 1.1 compute all phi_pd
        compute_all_data_closure();

        // \varphi
        z3::expr phi = m_ctx.get_negf();
        // \psi
        z3::expr psi = m_ctx.get_posf();

        logger() << "phi: " << phi << std::endl;
        logger() << "psi: " << psi << std::endl;

        // 1. const_set, lconst_set
        std::set<z3::expr, exprcomp> phi_const_set;
        expr_tool::get_consts(phi, phi_const_set);

        std::set<z3::expr, exprcomp> psi_const_set;
        expr_tool::get_consts(psi, psi_const_set);


        // 1.1 check var subset
        bool is_subset = expr_tool::is_sub_set(psi_const_set, phi_const_set);
        logger() << "psi_const_set size: " << psi_const_set.size() << std::endl;
        logger() << "phi_const_set size: " << phi_const_set.size() << std::endl;

        logger() << "psi_const_set is subset of phi_const_set: " <<  is_subset << std::endl;
        if(!is_subset) return z3::unsat;

        // 1.2 check sat
        z3::expr_vector phi_new_bools(z3_ctx());
        z3::expr phi_space(z3_ctx());
        z3::expr phi_abs = get_abstraction(phi, phi_space, phi_new_bools);
        m_ctx.phi_abs = phi_abs;
        m_ctx.phi_space = phi_space;
        ss.reset();
        ss.add(phi_abs);
        z3::check_result phi_res = ss.check();
        logger() << "phi sat res: " << phi_res << std::endl;
        if (phi_res == z3::unsat) return z3::sat;

        z3::expr_vector psi_new_bools(z3_ctx());
        z3::expr psi_space(z3_ctx());
        z3::expr psi_abs = get_abstraction(psi, psi_space, psi_new_bools);
        m_ctx.psi_abs = psi_abs;
        m_ctx.psi_space = psi_space;
        ss.reset();
        ss.add(psi_abs);
        z3::check_result psi_res = ss.check();
        logger() << "psi sat res: " << psi_res << std::endl;
        if (psi_res==z3::unsat) return z3::unsat;

        // 1.3 check Abs(\varphi) |= \exists Z. Abs(\psi)
        z3::expr_vector Z = psi_new_bools;
        for (int i=0; i<m_ctx.psi_space.num_args(); i++) {
                std::string k_i_name = logger().string_format("[k,%d]", i);
                Z.push_back(z3_ctx().int_const(k_i_name.c_str()));
        }
        logger() << "Z: " << Z << std::endl;
        z3::expr phi_abs_entl_psi_abs =  phi_abs && (z3::forall(Z, !psi_abs)); //
        // z3::expr phi_abs_entl_psi_abs = z3::implies(phi_abs, (z3::forall(Z, psi_abs))); //
        // logger() << "phi_abs_entl_psi_abs: " << phi_abs_entl_psi_abs << std::endl;

        z3::solver s1(z3_ctx(), "LIA");
        s1.add(phi_abs_entl_psi_abs);
        z3::check_result entl_abs_res = s1.check();
        // std::cout << "entl abs result: " << entl_abs_res << std::endl;
        logger() << "\nphi_abs entl forall psi_abs result: " << entl_abs_res << std::endl;
        if (entl_abs_res == z3::sat) { std::cout <<s1.get_model(); return z3::unsat; }


        // logger() << "model: " << ss.get_model() << std::endl;
        // if (pep_res == z3::sat || pep_res == z3::unknown) return z3::unsat; // if sat return unsat

        // 1.4 construct graph
        // phi phi_const_vec
        //std::vector<z3::expr> phi_const_vec;
        // std::vector<int> phi_const_eq_class_vec(phi_const_set.size(), -1);
        init_int_vector(m_ctx.phi_const_eq_class_vec, phi_const_set.size());

        get_const_vec_and_eq_class(phi, phi_abs, m_ctx.phi_const_vec, m_ctx.phi_const_eq_class_vec);

        // std::vector<z3::expr> psi_const_vec;
        // std::vector<int> psi_const_eq_class_vec(psi_const_set.size(), -1);
        init_int_vector(m_ctx.psi_const_eq_class_vec, psi_const_set.size());
        int psi_eq_class_size = get_const_vec_and_eq_class(psi, psi_abs, m_ctx.psi_const_vec, m_ctx.psi_const_eq_class_vec);
        // std::vector<int> psi_eq_to_eq_table(psi_eq_class_size, -1);
        // init map table
        init_int_vector(m_ctx.psi_eq_to_eq_table, psi_eq_class_size);

        graph g_phi;
        graph g_psi;

        construct_graph(phi_abs, m_ctx.phi_const_vec, m_ctx.phi_space, g_phi);
        g_phi.print(m_ctx.phi_const_vec, m_ctx.phi_space, "g_phi.dot");
        construct_graph(psi_abs, m_ctx.psi_const_vec, m_ctx.psi_space, g_psi);
        g_psi.print(m_ctx.psi_const_vec, m_ctx.psi_space, "g_psi.dot");

        // 1.5 allocating plans
        std::vector<int> cc_cycle_num = g_phi.get_cc_cycle_num();
        int cc_num = cc_cycle_num.size();
        logger() << "cc_num: " << cc_num << std::endl;
        for (int i=0; i<cc_num; i++)
                logger() << "cc_cycle_num: " << i << ": " << cc_cycle_num[i] <<std::endl;

        std::vector<int> omega(cc_num, 0);
        z3::expr omega_phi_abs_i = phi_abs;
        z3::expr omega_phi_abs_i1(z3_ctx());
        int i = 0;
        graph omega_g_i = g_phi;
        graph omega_g_i1;
        do{
                i++;
                logger() << "omega: [";
                for (int i=0; i<cc_num; i++)
                        logger()  << omega[i] << ", ";
                logger() << "]\n";
                int j=0;
                // omega_phi_abs = (phi_abs, omega, omega_target, g);
                logger() << "omega_g_i is dag like: " << omega_g_i.is_dag_like() << std::endl;
                while(!omega_g_i.is_dag_like()) {
                        get_omega_phi_abs(omega_phi_abs_i, omega_g_i, omega, m_ctx.phi_space, omega_phi_abs_i1);
                        omega_phi_abs_i = omega_phi_abs_i1;
                        ss.reset();
                        ss.add(omega_phi_abs_i);
                        // logger() << "omega_phi_abs_i: " << omega_phi_abs_i << std::endl;
                        // logger() << "omega result: " << ss.check() << std::endl;
                        if (ss.check() == z3::sat) {
                                // feasible allocating plans
                                construct_graph(omega_phi_abs_i, m_ctx.phi_const_vec, m_ctx.phi_space, omega_g_i1);
                                std::string file_name = logger().string_format("omega_g_%d_%d.dot", i, j++);
                                omega_g_i = omega_g_i1;
                                omega_g_i.print(m_ctx.phi_const_vec, m_ctx.phi_space, file_name);
                        }
                }
                // match omega_g_i psi_g
                std::cout << "matching \n";
                // match omega_graph to psi_graph
                // reset m_ctx.phi_const_eq_class_vec
                // reset m_ctx.psi_eq_to_eq_table

                m_ctx.phi_abs = omega_phi_abs_i;
                m_ctx.phi_const_vec.clear(); // TODO. modify get_const_vec_and_eq_class
                get_const_vec_and_eq_class(phi, omega_phi_abs_i, m_ctx.phi_const_vec, m_ctx.phi_const_eq_class_vec);
                logger() << "eq_to_eq table: \n";
                for (int i=0; i<m_ctx.psi_const_eq_class_vec.size(); i++) {
                        int psi_eq = m_ctx.psi_const_eq_class_vec[i];
                        int idx = expr_tool::index_of_exp(m_ctx.psi_const_vec[i], m_ctx.phi_const_vec);
                        int phi_eq = m_ctx.phi_const_eq_class_vec[idx];
                        m_ctx.psi_eq_to_eq_table[psi_eq] = phi_eq;

                        logger() << "psi_eq: " << psi_eq << "----" << "phi_eq: " << phi_eq << std::endl;
                }


                // match g_psi to omega_g_i
                bool flag = match_graph(g_psi, omega_g_i);
                // std::cout << "match flag: " << flag << std::endl;
                // exit(-1);
                if (!flag)  return z3::unsat;
                omega_g_i = g_phi;
                omega_phi_abs_i = phi_abs;
        } while(get_next_omega(omega, cc_cycle_num) && !g_phi.is_dag_like());

        return z3::sat;
}

/**
 * match pto
 * @param psi_atom : atom
 * @param omega_atom
 * @return true or false;
 */
bool listsolver::match_pto(z3::expr& psi_atom, z3::expr& omega_atom) {
        std::vector<z3::expr> psi_vars;
        std::vector<z3::expr> phi_atom_vars;
        psi_vars.push_back(psi_atom.arg(0));
        phi_atom_vars.push_back(omega_atom.arg(0));
        expr_tool::get_all_field_of_pto(psi_atom, psi_vars);
        expr_tool::get_all_field_of_pto(omega_atom, phi_atom_vars);
        // match
        for (int i=0; i<psi_vars.size(); i++) {
                z3::expr psi_v = psi_vars[i];
                z3::expr phi_v = phi_atom_vars[i];
                int phi_cls = m_ctx.phi_const_eq_class_vec[ expr_tool::index_of_exp(phi_v, m_ctx.phi_const_vec)];
                int psi_cls = m_ctx.psi_const_eq_class_vec[expr_tool::index_of_exp(psi_v, m_ctx.psi_const_vec)];
                if (m_ctx.psi_eq_to_eq_table[psi_cls] != phi_cls) return false;
        }
        return true;
}

/**
 * match path to atom space
 * @param paths : path atoms ids
 * @param atom_space : unfold space
 * @param omega_const_vec : omeg var vec
 * @param omega_const_eq_class_vec : omega eq_class
 * @param eq_to_eq table
 * @return true or false
 */
bool listsolver::match_path_to_atom_space(std::vector<int> &paths, z3::expr &atom_space, std::vector<z3::expr>&  omega_const_vec, std::vector<int>&  omega_const_eq_class_vec, std::vector<int> &omega_eq_to_eq_table) {
        for (int j=0; j<atom_space.num_args(); j++) {
                z3::expr psi_j = atom_space.arg(j);
                z3::expr phi_atom_j = m_ctx.phi_space.arg(paths[j]);
                std::vector<z3::expr> psi_vars;
                std::vector<z3::expr> phi_atom_vars;

                if (expr_tool::is_fun(psi_j, "pto")) {
                        // logger() << "atom_j: " << atom_j << std::endl;
                        // logger() << "phi_atom_j: " << phi_atom_j << std::endl;
                        psi_vars.push_back(psi_j.arg(0));
                        phi_atom_vars.push_back(phi_atom_j.arg(0));
                        expr_tool::get_all_field_of_pto(psi_j, psi_vars);
                        expr_tool::get_all_field_of_pto(phi_atom_j, phi_atom_vars);
                } else {
                        for (int i=0; i<psi_j.num_args(); i++) {
                                psi_vars.push_back(psi_j.arg(i));
                                phi_atom_vars.push_back(phi_atom_j.arg(i));
                        }
                }
                // match
                for (int i=0; i<psi_vars.size(); i++) {
                        z3::expr psi_v = psi_vars[i];
                        z3::expr phi_v = phi_atom_vars[i];

                        //std::cout << "psi_v: " << psi_v << ", phi_v: " << phi_v << std::endl;

                        int omega_cls = omega_const_eq_class_vec[expr_tool::index_of_exp(psi_v, omega_const_vec)];
                        int phi_cls = m_ctx.phi_const_eq_class_vec[ expr_tool::index_of_exp(phi_v, m_ctx.phi_const_vec)];
                        if (omega_eq_to_eq_table[omega_cls] != -1 && omega_eq_to_eq_table[omega_cls] != phi_cls) {
                                //std::cout << "omega return false.\n";
                                return false;
                        }
                        omega_eq_to_eq_table[omega_cls] = phi_cls;
                        // phi
                        int psi_idx = expr_tool::index_of_exp(psi_v, m_ctx.psi_const_vec);
                        int psi_cls = m_ctx.psi_const_eq_class_vec[psi_idx];
                        //std::cout << "psi class: " << psi_cls<<", phi class: "<< phi_cls << std::endl;
                        if (psi_idx != -1 && m_ctx.psi_eq_to_eq_table[psi_cls] != phi_cls) {
                                //std::cout << "global return false;\n";
                                return false;
                        }
                }
        }
        return true;
}

/**
 * match graph psi to omega_graph
 * @param g_psi
 * @param omega_g_i
 * @return true or false
 */
bool listsolver::match_graph(graph& g_psi, graph& omega_g_i) {

        //  get psi_edges
        std::vector<std::pair<std::pair<int, int>, int> > psi_edge_vec;
        g_psi.get_edges(psi_edge_vec);
        // get omega_edges
        std::vector<std::pair<std::pair<int, int>, int> > omega_edge_vec;
        omega_g_i.get_edges(omega_edge_vec);
        // std::vector<int> omega_edge_table(omega_edge_vec.size(), -1);
        std::map<int, int> omega_edge_table;
        for (int i=0; i<omega_edge_vec.size(); i++) {
                omega_edge_table[omega_edge_vec[i].second] = -1;
        }

        //CC
        std::vector<int> cc_cycle_num = omega_g_i.get_cc_cycle_num();
        std::vector<std::pair<int, int> > cc_cycle_table;
        for (int i=0; i<cc_cycle_num.size(); i++) {
                std::pair<int, int> selected(-1, -1);
                if (cc_cycle_num[i] > 0) {
                        selected.first = 0; // -1: no cycle; 0: no process; 1: candidate  2:selected
                }
                cc_cycle_table.push_back(selected);
        }

        logger() << std::endl;
        std::vector<z3::expr> psi_const_vec = m_ctx.psi_const_vec;
        std::vector<z3::expr> phi_const_vec = m_ctx.phi_const_vec;
        z3::expr psi_space = m_ctx.psi_space;
        z3::expr phi_space = m_ctx.phi_space;

        std::pair<std::pair<int, int>, int> edge;
        // for each edge match one path in omega_graph
        for (int i=0; i<psi_edge_vec.size(); i++) {
                logger() <<"psi edge: "<< m_ctx.psi_const_vec[psi_edge_vec[i].first.first] << "--" << psi_edge_vec[i].second << "--" << m_ctx.psi_const_vec[psi_edge_vec[i].first.second] << std::endl;

                edge = psi_edge_vec[i];
                z3::expr psi_atom = psi_space.arg(edge.second);
                int src = expr_tool::index_of_exp(psi_const_vec[edge.first.first], phi_const_vec);
                int dst = expr_tool::index_of_exp(psi_const_vec[edge.first.second], phi_const_vec);


                src = omega_g_i.get_vertex_id(src);
                dst = omega_g_i.get_vertex_id(dst);

                // std::cout << "src: " << src << ", dst: " << dst << std::endl;


                // src and dst are in the same cc
                int cc_id = omega_g_i.which_cc(src);
                if (cc_id != omega_g_i.which_cc(dst)) return false; // ?

                std::vector<graph::edge_descriptor> path = omega_g_i.get_path(src, dst);

                logger() << "path: \n";
                for (int j=0; j<path.size(); j++) {
                        logger() << omega_g_i.source(path[j]);
                        logger() << "---";
                        logger() << omega_g_i.get_edge_property(path[j]);
                        logger() << "---";
                        logger() << omega_g_i.target(path[j]) << std::endl;

                }

                std::vector<int> paths;
                for (int j=0; j<path.size(); j++) {
                        paths.push_back(omega_g_i.get_edge_property(path[j]));
                }

                // special case
                if (paths.size()==0 && src!=dst) return false;

                int edge_num = paths.size();
                if (expr_tool::is_fun(psi_atom, "pto")) {
                        // pto match pto
                        if (edge_num==1) {
                                z3::expr omega_phi_atom = phi_space.arg(paths[0]);
                                if (!expr_tool::is_fun(omega_phi_atom, "pto")) {
                                        return z3::unsat;
                                }
                                // match pto atom
                                if(!match_pto(psi_atom, omega_phi_atom)) return false;
                        } else {
                                return false;
                        }
                } else{
                        // pred_atom match path
                        if (cc_cycle_num[cc_id] == 0) {
                                logger() << "omega graph is dag. \n";
                                // dag
                                if(!match_path_to_atom_space(paths, psi_atom)) return false;
                        } else {
                                // dag_like (each cc has at most one cycle)
                                std::pair<int, int> coord(cc_id, 0);
                                std::vector<int> cycle = omega_g_i.get_cycle(coord);

                                // match paths
                                bool match_res1 = match_path_to_atom_space(paths, psi_atom);
                                // match paths+cycle
                                std::vector<graph::edge_descriptor> cycle_path = omega_g_i.get_path(dst);
                                for (int j=0; j<cycle_path.size(); j++) {
                                        logger() <<"cycle edge: "<< m_ctx.psi_const_vec[omega_g_i.source(cycle_path[j])] << "--" << (omega_g_i.get_edge_property(cycle_path[j])) << "--" << m_ctx.psi_const_vec[omega_g_i.target(cycle_path[j])] << std::endl;
                                }
                                for (int j=0; j<cycle_path.size(); j++) {
                                        paths.push_back(omega_g_i.get_edge_property(cycle_path[j]));
                                }
                                bool match_res2 = match_path_to_atom_space(paths, psi_atom);

                                logger() << "match_res1: " << match_res1 << ", match_res2: " << match_res2 << std::endl;

                                // whether dst and last_src are in cycle
                                int last_src = -1;
                                if (path.size() > 0) {
                                        last_src = omega_g_i.source(path[path.size()-1]);
                                }
                                if (index_of_int(dst, cycle) != -1 && index_of_int(last_src, cycle) == -1) {
                                        // dst in, last_src not in
                                        if (cc_cycle_table[cc_id].first != 2) {
                                                if (match_res1 && match_res2) {
                                                        cc_cycle_table[cc_id].first = 1;
                                                        cc_cycle_table[cc_id].second = i;
                                                } else if (!match_res1 && match_res2) {
                                                        cc_cycle_table[cc_id].first = 2;
                                                        cc_cycle_table[cc_id].second = i;
                                                        edge_num = paths.size(); // add edges
                                                } else if (!match_res1 && !match_res2) {
                                                        return false;
                                                }
                                        } else {
                                                if (!match_res1) return false;
                                        }
                                } else if(index_of_int(dst, cycle) != -1 && src==dst){
                                        // dst in, last_src in, src == dst
                                        if (cc_cycle_table[cc_id].first != 2 && match_res2) {
                                                cc_cycle_table[cc_id].first = 1;
                                                cc_cycle_table[cc_id].second = i;
                                        }
                                } else {
                                        if (!match_res1) return false;
                                        if (index_of_int(dst, cycle) != -1) {
                                                // dst in cycle
                                                cc_cycle_table[cc_id].first = 2;
                                        }
                                }
                        }
                }

                for (int j=0; j<edge_num; j++) {
                        omega_edge_table[paths[j]] ++;
                }
        }

        // check global info
        logger() <<"cc_cycle_table: \n";
        for (int i=0; i<cc_cycle_table.size(); i++) {

                logger() << "cc_cycle_num: " << i << " , status: " << cc_cycle_table[i].first << std::endl;

                if (cc_cycle_table[i].first==0) return false;
                if (cc_cycle_table[i].first==1) {
                        std::pair<int, int> coord(i, 0);
                        std::vector<int> cycle = omega_g_i.get_cycle(coord);
                        std::vector<graph::edge_descriptor> cycle_path = omega_g_i.get_path(cycle[0]);
                        for (int j=0; j<cycle_path.size(); j++) {
                                int path_idx = omega_g_i.get_edge_property(cycle_path[j]);
                                omega_edge_table[path_idx]++;
                        }
                }
        }

        //
        logger() << "omega_edges_table: \n";

        std::map<int, int>::iterator iter;
        int i=0;
        for (iter=omega_edge_table.begin(); iter!=omega_edge_table.end(); iter++, i++) {
                logger() << "edge: " << i <<", property: " <<iter->first << " , status: " << iter->second << std::endl;
                if (iter->second!=0) return false;
        }
        return true;
}


bool listsolver::match_path_to_atom_space(std::vector<int> &paths, z3::expr &psi_atom) {
        // path match pred atom
        if (paths.size() == 0) {
                // abs_omega_phi |= pred atom is empty
                z3::expr entl_empty_f = m_ctx.phi_abs;
                z3::expr eq_atom = z3_ctx().bool_val(true);
                int st_size = m_ctx.get_pred(0).size_of_static_parameters();
                int pars_size = psi_atom.num_args()-st_size;
                for (int i=0; i<pars_size/2; i++) {
                        eq_atom = eq_atom && expr_tool::eq_exp(z3_ctx(), psi_atom.arg(i), psi_atom.arg(i+pars_size/2));
                }
                entl_empty_f = entl_empty_f && !eq_atom;
                z3::solver ss(z3_ctx());
                ss.add(entl_empty_f);
                if (ss.check() == z3::unsat) return true;
                else return false;
        }
        // 1. psi_pred_atom - extend by path
        z3::expr omega_f(z3_ctx());
        z3::expr atom_space(z3_ctx());
        // z3::expr_vector new_vars(z3_ctx());
        unfold_by_path(paths, psi_atom, omega_f);
        z3::expr omega_f_abs(z3_ctx());
        // logger() << "omega_f: " << omega_f << std::endl;
        get_data_space(omega_f, omega_f_abs, atom_space);
        // omega_f_abs = get_abstraction(omega_f, atom_space, new_bools);
        logger() << "omega_f_abs data: " << omega_f_abs << std::endl;
        omega_f_abs = omega_f_abs && m_ctx.psi_abs;
        // logger() << "omega_f_abs: " << omega_f_abs <<std::endl;
        std::set<z3::expr, exprcomp> omega_const_set;
        expr_tool::get_consts(omega_f, omega_const_set);
        std::vector<z3::expr> oemga_const_vec;
        std::vector<int> omega_const_eq_class_vec(omega_const_set.size(), -1);
        int eq_count = get_const_vec_and_eq_class(omega_f, omega_f_abs, oemga_const_vec, omega_const_eq_class_vec);
        logger() << "eq_count: " << eq_count << std::endl;
        std::vector<int> omega_eq_to_eq_table(eq_count, -1);

        if(!match_path_to_atom_space(paths, atom_space, oemga_const_vec, omega_const_eq_class_vec, omega_eq_to_eq_table)) return false;
        return true;
}


/**
 * unfold predicate atom by path
 * @param path : match path
 * @param psi_atom : pred atom
 * @param omega_f : unfold formula
 */
void listsolver::unfold_by_path(std::vector<int> &path, z3::expr &psi_atom, z3::expr &omega_f) {
        z3::expr atom_data = z3_ctx().bool_val(true);
        std::vector<z3::expr> atom_spaces;
        atom_spaces.push_back(psi_atom);
        predicate pred = m_ctx.get_pred(0); // entl problem has only one predicate
        int st_par_size = pred.size_of_static_parameters();

        // unfold_by_path(path, psi_atom, atom_data, atom_space);
        for (int j=0; j<path.size(); j++) {
                z3::expr atom_j = m_ctx.phi_space.arg(path[j]);
                // logger() << "atom_j: " << atom_j << std::endl;
                if (expr_tool::is_fun(atom_j, "pto")) {
                        // extend one pto
                        unfold_pto(pred, atom_data, atom_spaces);
                        if (j==path.size()-1) {
                                z3::expr last_pred = atom_spaces.back();
                                int size = last_pred.num_args() - st_par_size;
                                for(int k=0; k<size/2; k++) {
                                        atom_data = atom_data && (last_pred.arg(k) == last_pred.arg(k+size/2));
                                }
                                atom_spaces.pop_back();
                        }
                } else if (j<path.size()-1) {
                        // extend one pred
                        unfold_pred(pred, atom_spaces);
                }
        }

        // make a space atom
        z3::expr atom_space = atom_spaces[0];
        if (atom_spaces.size() >= 2) {
                z3::sort range = z3_ctx().uninterpreted_sort("Space");
                z3::sort_vector domains(z3_ctx());
                for (unsigned i=0; i<atom_spaces.size(); i++) {
                        domains.push_back(range);
                }
                z3::func_decl ssep_f = z3_ctx().function("ssep", domains, range);
                z3::expr_vector args(z3_ctx());
                for (int j=0; j<atom_spaces.size(); j++) args.push_back(atom_spaces[j]);
                atom_space = ssep_f(args);
        }

        z3::sort domain = z3_ctx().uninterpreted_sort("Space");
        z3::sort range = z3_ctx().bool_sort();
        z3::func_decl tobool_f = z3_ctx().function("tobool", domain, range);
        atom_space = tobool_f(atom_space);
        omega_f = atom_data && atom_space;
}



/**
 * get const vector and eq_class by phi and phi_abs
 * @param phi : the formula phi
 * @param phi_abs : the abstraction of phi
 * @param const_vec : output const vector
 * @param const_eq_class : output const vector map eq_class
 * @return int: the eq_class_count
 */
int listsolver::get_const_vec_and_eq_class(z3::expr &phi, z3::expr phi_abs, std::vector<z3::expr> &const_vec, std::vector<int> &const_eq_class) {
        std::set<z3::expr, exprcomp> phi_lconst_set;
        expr_tool::get_lconsts(phi, phi_lconst_set);
        std::vector<z3::expr> phi_lconst_vec;
        expr_tool::expr_set_to_vec(phi_lconst_set, phi_lconst_vec);
        std::vector<std::set<int> > phi_location_eq_class_vec;
        std::vector<int> phi_lconst_class(phi_lconst_vec.size(), -1);
        get_eq_class(phi_abs, phi_lconst_vec, phi_location_eq_class_vec, phi_lconst_class);
        // get data eq_class_vec
        std::set<z3::expr, exprcomp> phi_dconst_set;
        expr_tool::get_dconsts(phi, phi_dconst_set);
        std::vector<z3::expr> phi_dconst_vec;
        expr_tool::expr_set_to_vec(phi_dconst_set, phi_dconst_vec);
        std::vector<std::set<int> > phi_data_eq_class_vec;
        std::vector<int> phi_dconst_class(phi_dconst_vec.size(), -1);
        get_eq_class(phi_abs, phi_dconst_vec, phi_data_eq_class_vec, phi_dconst_class);

        // logger() << "var size in get: " << phi_lconst_vec.size() + phi_dconst_vec.size() << std::endl;


        int loc_size = phi_lconst_vec.size();
        int loc_eq_size = phi_location_eq_class_vec.size();
        for (int i=0; i<phi_lconst_vec.size(); i++) {
                const_vec.push_back(phi_lconst_vec[i]);
                const_eq_class[i] = phi_lconst_class[i];
                // logger() << phi_lconst_vec[i] << std::endl;
        }
        for (int i=0; i<phi_dconst_vec.size(); i++) {
                const_vec.push_back(phi_dconst_vec[i]);
                const_eq_class[loc_size+i] = phi_dconst_class[i]+loc_eq_size;
                // logger() << phi_dconst_vec[i] << std::endl;
        }

        // logger() << "location eq class :" << phi_location_eq_class_vec.size() << std::endl;
        // logger() << "data eq class :" <<phi_data_eq_class_vec.size() << std::endl;


        return phi_location_eq_class_vec.size() + phi_data_eq_class_vec.size();
}



/**
 * extend predicate atom
 * @param pred : predicate definition
 * @parram atom_space : extend space atoms
 */
void listsolver::unfold_pred(predicate &pred, std::vector<z3::expr> &atom_space) {

        int unfold_idx = atom_space.size();
        z3::expr atom = atom_space[unfold_idx-1];
        int size = atom.num_args() - pred.size_of_static_parameters(); // size of source and destination paramaters
        atom_space.pop_back();
        z3::expr_vector pred1_args(z3_ctx());
        z3::expr_vector pred2_args(z3_ctx());
        for (int i=0; i<size/2; i++) {
                pred1_args.push_back(atom.arg(i));
                z3::sort st = atom.arg(i).get_sort();
                std::string new_name = logger().string_format("pred_var_%d_%d", i, unfold_idx);
                z3::expr new_var = z3_ctx().constant(new_name.c_str(), st);
                // new_vars.push_back(new_var);
                pred2_args.push_back(new_var);
        }
        for (int i=size/2; i<size; i++) {
                pred1_args.push_back(pred2_args[i-size/2]);
                pred2_args.push_back(atom.arg(i));
        }
        for (int i=size; i<atom.num_args(); i++) {
                pred1_args.push_back(atom.arg(i));
                pred2_args.push_back(atom.arg(i));
        }
        z3::func_decl pred_fun = pred.get_fun();
        z3::expr pred1 = pred_fun(pred1_args);
        z3::expr pred2 = pred_fun(pred2_args);
        atom_space.push_back(pred1);
        atom_space.push_back(pred2);
}

/**
 * extend one pto atom
 * @param pred : predicate definition
 * @param atom_data : extend data constraints
 * @param atom_space : extend space atoms
 */
void listsolver::unfold_pto(predicate &pred, z3::expr& atom_data, std::vector<z3::expr> &atom_space) {
        pred_rule rule = pred.get_rule(0);
        z3::expr data = rule.get_data();
        z3::expr pto = rule.get_pto();
        z3::expr rec_app = rule.get_rec_apps()[0];

        int unfold_idx = atom_space.size();
        z3::expr atom = atom_space[unfold_idx-1];
        atom_space.pop_back();

        z3::expr_vector args = pred.get_pars(); // predicate parameters, formal parameters
        z3::expr_vector f_args(z3_ctx());
        z3::expr_vector a_args(z3_ctx()); // actual parameters

        // init formla parameters and actual parameters
        for (int j=0; j<atom.num_args(); j++) {
                f_args.push_back(args[j]);
                a_args.push_back(atom.arg(j));
        }

        z3::expr_vector x_h(z3_ctx());
        rule.get_x_h(x_h);
        // z3::expr_vector x_h_cons(z3_ctx());
        for (int j=0; j<x_h.size(); j++) {
                f_args.push_back(x_h[j]);
                z3::sort st = x_h[j].get_sort();
                std::string name = x_h[j].to_string();
                name = name.replace(name.find(":"), 1, "");
                name = name.replace(name.find(" "), 1, "_");
                std::string ss = logger().string_format("%s_%d",   name.substr(1, name.length()-2).c_str(), unfold_idx);
                z3::expr new_var = z3_ctx().constant(ss.c_str(), st);
                // new_vars.push_back(new_var);
                a_args.push_back(new_var);
        }


        data = data.substitute(f_args, a_args);
        atom_data = atom_data && data;
        pto = pto.substitute(f_args, a_args);
        rec_app = rec_app.substitute(f_args, a_args);
        atom_space.push_back(pto);
        atom_space.push_back(rec_app);
}


/**
 * get omega_phi_abs
 * @param phi_abs : last omega_phi_abs
 * @param g : last omega_graph
 * @param omega : new pseudo-plan
 * @param omega_phi_abs: new omega_phi_abs
 */
void listsolver::get_omega_phi_abs(z3::expr &phi_abs, graph &g, std::vector<int> &omega, z3::expr& space, z3::expr &omega_phi_abs) {
        std::vector<int> cc_cycle_num = g.get_cc_cycle_num();
        std::pair<int,int> coords;
        std::vector<graph::edge_t> cycle;
        omega_phi_abs = phi_abs;
        int cc_num = cc_cycle_num.size();
        for (int i=0; i<cc_num; i++) {
                int omega_i =omega[i];
                if (omega_i==0) {
                        //
                        for (int j=0; j<cc_cycle_num[i]; j++) {
                                coords.first = i;
                                coords.second = j;
                                cycle = g.get_edge_cycle(coords);
                                int cycle_size = cycle.size();
                                // edge
                                for (int k=0; k<cycle_size; k++) {
                                        graph::edge_t edge = cycle[k];
                                        int atom_idx = edge.second;
                                        z3::expr E = space.arg(atom_idx).arg(0);
                                        std::string E_bool_name = logger().string_format("[%s,%d]", E.to_string().c_str(), atom_idx);
                                        z3::expr E_bool = z3_ctx().bool_const(E_bool_name.c_str());
                                        omega_phi_abs = omega_phi_abs && (!E_bool);
                                }
                        }
                } else {
                        //
                        coords.first = i;
                        coords.second = omega_i-1;
                        cycle = g.get_edge_cycle(coords);
                        int cycle_size = cycle.size();
                        z3::expr zeta(z3_ctx());
                        // edge
                        for (int k=0; k<cycle_size; k++) {
                                graph::edge_t edge = cycle[k];
                                int atom_idx = edge.second;
                                z3::expr E = space.arg(atom_idx).arg(0);
                                std::string E_bool_name = logger().string_format("[%s,%d]", E.to_string().c_str(), atom_idx);
                                z3::expr E_bool = z3_ctx().bool_const(E_bool_name.c_str());

                                if (Z3_ast(zeta) == 0) {
                                        zeta = E_bool;
                                } else {
                                        zeta = zeta || E_bool;
                                }
                        }
                        omega_phi_abs = omega_phi_abs && zeta;
                }
        }
}

/**
 * construct_graph by phi
 * @param phi_abs : abstraction of phi
 * @param lconsts : the location vars
 * @param space : the space part
 * @param g : the output
 */
void listsolver::construct_graph(z3::expr &phi_abs, std::vector<z3::expr> &phi_const_vec, z3::expr &phi_space, graph &g) {
        std::vector<std::set<int> > eq_class_vec;
        std::vector<z3::expr> phi_lconst_vec;
        for (int i=0; i<phi_const_vec.size(); i++) {
                if (!expr_tool::is_location(phi_const_vec[i])) break;
                phi_lconst_vec.push_back(phi_const_vec[i]);
        }
        get_eq_class(phi_abs, phi_lconst_vec, eq_class_vec);

        // logger() << "size of eq_class_vec: " << eq_class_vec.size() << std::endl;

        std::vector<std::pair<std::pair<int, int>, int> > edge_vec;
        z3::solver ss(z3_ctx());

        for (int i=0; i<phi_space.num_args(); i++) {
                std::pair<std::pair<int, int>, int> edge;
                edge.second = i;
                z3::expr atom = phi_space.arg(i);
                if (atom.decl().name().str()!="pto") {
                        // abs(\phi) \and [E,i]
                        z3::expr E = atom.arg(0);
                        std::string E_bool_name = logger().string_format("[%s,%d]", E.to_string().c_str(), i);
                        z3::expr E_bool = z3_ctx().bool_const(E_bool_name.c_str());
                        z3::expr f = phi_abs && E_bool;
                        ss.reset();
                        ss.add(f);
                        if (ss.check() == z3::unsat) continue;
                }
                get_edge_from_atom(atom, phi_lconst_vec, edge);
                edge_vec.push_back(edge);
        }


        // logger() << "size of edge_vec: " << edge_vec.size() << std::endl;
        g.init(eq_class_vec, edge_vec);
}

/**
 * get next omega, get next pseudo-plans
 * @param curr : current omega
 * @param target : target omega
 */
bool listsolver::get_next_omega(std::vector<int> &curr, std::vector<int> &target) {
        bool has = false;
        int size = curr.size();
        for (int i=0; i<size; i++) {
                if (curr[i] != target[i]) has = true;
        }
        if (has) {
                int c = 0;
                int i=size-1;
                while(i>=0 && target[i]==0) i--;

                if (i>=0) {
                        if (curr[i]+1>target[i]) c = 1;
                        curr[i] = (curr[i]+1) % (target[i]+1);
                }

                while(c>0 && i>=0) {
                        if (target[i] == 0) {
                                i--;
                        } else {
                                if (curr[i]+1 <= target[i]) c=0;
                                curr[i] = (curr[i]+1) % (target[i]+1);
                        }
                }
        }
        return has;
}

/**
 * get edge from atom
 * @param atom : the atom
 * @param lconsts : the location var
 * @param edge : output
 */
void listsolver::get_edge_from_atom(z3::expr &atom, std::vector<z3::expr> &lconsts, std::pair<std::pair<int, int>, int> &edge) {
        predicate pred = m_ctx.get_pred(0);
        z3::expr plfld = pred.get_plfld();
        int size = pred.get_pars().size() - pred.size_of_static_parameters();
        z3::expr source(z3_ctx());
        z3::expr dest(z3_ctx());

        if (atom.decl().name().str()=="pto") {
                source = atom.arg(0);
                z3::expr sref = atom.arg(1);
                if (sref.decl().name().str() == "sref") {
                        for (int i=0; i<sref.num_args(); i++) {
                                if (sref.arg(i).arg(0).to_string() == plfld.to_string()) {
                                        dest = sref.arg(i).arg(1);
                                        break;
                                }
                        }
                } else {
                        dest = sref.arg(1);
                }
        } else {
                source = atom.arg(0);
                dest = atom.arg(size/2);
        }
        edge.first.first = expr_tool::index_of_exp(source, lconsts);
        edge.first.second = expr_tool::index_of_exp(dest, lconsts);
}

/**
 * get equivalence class
 * @param: phi_abs : the abstraction of phi
 * @param: lconsts : the location vars
 * @param: eq_class_vec : the output
 */
void listsolver::get_eq_class(z3::expr &phi_abs, std::vector<z3::expr> &lconsts, std::vector<std::set<int> > &eq_class_vec) {
        std::vector<int> lconst_class(lconsts.size(), -1);
        get_eq_class(phi_abs, lconsts, eq_class_vec, lconst_class);
}

/**
 * get equivalence class
 * @param: phi_abs : the abstraction of phi
 * @param: lconsts : the location vars
 * @param: eq_class_vec : the output
 * @param: lconst_class : the output
 */
void listsolver::get_eq_class(z3::expr &phi_abs, std::vector<z3::expr> &lconsts, std::vector<std::set<int> > &eq_class_vec,  std::vector<int>& lconst_class) {
        std::set<int> eq_class;
        z3::solver sol(z3_ctx());
        // std::vector<int> lconst_class(lconsts.size(), -1);
        for (int i=0; i<lconsts.size(); i++) {
                for (int j=i+1; j<lconsts.size(); j++) {
                        z3::expr formula = phi_abs;
                        if (expr_tool::is_location(lconsts[i])) {
                                z3::expr X = z3_ctx().int_const(lconsts[i].to_string().c_str()) ;
                                z3::expr Y =  z3_ctx().int_const(lconsts[j].to_string().c_str());
                                formula = formula && (X!=Y);
                        } else {
                                formula = formula && (lconsts[i] != lconsts[j]);
                        }
                        sol.reset();
                        sol.add(formula);
                        // logger() << "eq class formula: " << formula << std::endl;
                        // logger() << "check sat: " << sol.check() << std::endl;
                        if(sol.check() == z3::unsat) {
                                // X == Y
                                if (lconst_class[i] != -1) {
                                        lconst_class[j] = lconst_class[i];
                                        eq_class_vec[lconst_class[i]].insert(j);
                                } else {
                                        lconst_class[i] = eq_class_vec.size();
                                        lconst_class[j] = lconst_class[i];
                                        eq_class.clear();
                                        eq_class.insert(i);
                                        eq_class.insert(j);
                                        eq_class_vec.push_back(eq_class);
                                }
                        } else {
                                // logger() << "model: " << sol.get_model() << std::endl;
                        }
                }
        }

        for (int i=0; i<lconsts.size(); i++) {
                if (lconst_class[i] == -1) {
                        lconst_class[i] = eq_class_vec.size();
                        eq_class.clear();
                        eq_class.insert(i);
                        eq_class_vec.push_back(eq_class);
                }
        }
}

/**
 * compute all predicate data  closure
 */
void listsolver::compute_all_data_closure() {
        for (int i=0; i<m_ctx.pred_size(); i++) {
                logger() << "compute predicate " << i << std::endl;
                predicate pred = m_ctx.get_pred(i);
                // 1. compute data closure (lfp)
                z3::expr phi_pd_abs = compute_data_closure(pred);
                logger() << "compute data closure: " << phi_pd_abs << std::endl;
                delta_ge1_predicates.push_back(phi_pd_abs);
        }
}

/**
 * compute predicate data closure
 * @param pred: predicate
 * @return phi_pd : data closure
 */
z3::expr listsolver::compute_data_closure(predicate &pred) {
        z3::expr_vector args = pred.get_pars();
        z3::expr_vector xi(z3_ctx());
        z3::expr_vector alpha(z3_ctx());
        z3::expr_vector beta(z3_ctx());
        z3::expr_vector gamma(z3_ctx());
        z3::expr rec_app = pred.get_rule(0).get_rec_apps()[0];

        int size = args.size();
        // 1. get xi
        int i=size-1;
        for (; i>=0; i--) {
                if (args[i].to_string().find("sta_")!=0) break;
                xi.push_back(args[i]);
        }
        size = i+1; // size of source and destination parameters
        // 2. get alpha beta
        for (i=1; i<size/2; i++) {
                alpha.push_back(args[i]);
                beta.push_back(args[i+size/2]);
                gamma.push_back(rec_app.arg(i));
        }

        // std::cout << "xi: " << xi << std::endl;
        // std::cout << "alpha: " << alpha << std::endl;
        // std::cout << "beta: " << beta << std::endl;
        // std::cout << "gamma: " << gamma << std::endl;

        std::vector<std::vector<std::vector<z3::expr>>> alpha_table;// alphai -> data items
        for (int i=0; i<alpha.size(); i++) {
                std::vector<std::vector<z3::expr>> data_items;
                for (int j=0; j<3; j++) {// 0:=, 1:<=, 2:>=
                        std::vector<z3::expr> data_item;
                        data_items.push_back(data_item);
                }
                alpha_table.push_back(data_items);
        }


        z3::expr data = pred.get_rule(0).get_data();
        // std::cout << "data: " << data << std::endl;
        for (int i=0; i<data.num_args(); i++) {
                z3::expr data_item = data.arg(i);
                z3::expr normal_item = normalize_item(data_item);
                // std::cout << "data_item: " << normal_item << std::endl;
                z3::expr alpha_i = normal_item.arg(0);
                z3::expr right_i = normal_item.arg(1);
                int idx_i = index_of_vec(alpha_i, alpha);

                std::string opa = normal_item.decl().name().str();
                if (opa == "=") {
                        alpha_table[idx_i][0].push_back(normal_item);
                } else if (opa == "<=") {
                        alpha_table[idx_i][1].push_back(normal_item);
                } else {
                        alpha_table[idx_i][2].push_back(normal_item);
                }
        }


        /*
          for (int i=0; i<alpha.size(); i++) {
          std::cout << "alpha :" << alpha[i] << std::endl;
          for (int j=0; j<3; j++) {// 0:=, 1:<=, 2:>=
          std::cout << " " << alpha_table[i][j].size() << ":";
          for (int k=0; k<alpha_table[i][j].size(); k++) {
          std::cout << alpha_table[i][j][k] << " ";
          }
          std::cout << std::endl;
          }
          std::cout << std::endl;
          }
        */



        z3::expr phi_pd = z3_ctx().bool_val(true);
        for (int i=0; i<alpha.size(); i++) {
                std::vector<std::vector<z3::expr>> data_items = alpha_table[i];
                z3::expr gamma_i = gamma[i];
                z3::expr beta_i = beta[i];
                z3::expr closure_item = compute_alpha_closure(data_items, xi, gamma_i, beta_i);
                // std::cout << "closure item: " << closure_item << std::endl;
                phi_pd = phi_pd && closure_item;
        }
        return phi_pd;
}


/**
 * compute alpha_i closure item by related data items
 * @param data_items: alpha_i related data items
 * @param xi : static parameters
 * @param gamma :
 * @return closure data item
 */
z3::expr listsolver::compute_alpha_closure(std::vector<std::vector<z3::expr> > &data_items, z3::expr_vector &xi, z3::expr &gamma_i, z3::expr& beta_i) {
        z3::expr closure_item = z3_ctx().bool_val(true);
        z3::expr k = z3_ctx().int_const("k");

        // 1. =
        for (int i=0; i<data_items[0].size(); i++) {
                z3::expr item = data_items[0][i];
                // 1.1 alpha_i = c
                if (item.arg(1).num_args()!=2) {
                        closure_item = closure_item && item;
                } else {
                        z3::expr op1 = item.arg(1).arg(0);

                        int idx_j = index_of_vec(op1, xi);
                        // 1.2 alpha_i = xi_j + c
                        if (idx_j != -1) {
                                closure_item = closure_item && item;
                        }
                        // 1.3 alpha_i = gamma_i + c
                        else if (gamma_i.hash()==op1.hash()) {
                                int c = get_numeral(item.arg(1).arg(1));
                                closure_item = closure_item && (item.arg(0) == beta_i + k*c);
                        }
                }

        }
        // std::cout << "== closure item: " << closure_item << std::endl;
        // 2. <=
        z3::expr_vector le_cs(z3_ctx());
        z3::expr_vector le_xi_cs(z3_ctx());
        z3::expr_vector le_gamma_cs(z3_ctx());
        for (int i=0; i<data_items[1].size(); i++) {
                z3::expr item = data_items[1][i];
                // 1.1 alpha_i = c
                if (item.arg(1).num_args()!=2) {
                        closure_item = closure_item && item;
                        le_cs.push_back(item);
                } else {
                        z3::expr op1 = item.arg(1).arg(0);
                        int idx_j = index_of_vec(op1, xi);
                        // 1.2 alpha_i = xi_j + c
                        if (idx_j != -1) {
                                closure_item = closure_item && item;
                                le_xi_cs.push_back(item);
                        }
                        // 1.3 alpha_i = gamma_i + c
                        else if (gamma_i.hash()==op1.hash()) {

                                int c = get_numeral(item.arg(1).arg(1));
                                closure_item = closure_item && (item.arg(0) <= beta_i + k*c);
                                le_gamma_cs.push_back(item);
                        }
                }
        }

        for (int i=0; i<le_gamma_cs.size(); i++) {
                z3::expr item = le_gamma_cs[i];
                int c = get_numeral(item.arg(1).arg(1));
                if (c < 0) {
                        for (int j=0; j<le_cs.size();j++) {
                                z3::expr con_item = le_cs[j];
                                closure_item = closure_item && (item.arg(0) <= con_item.arg(1) + (k-1)*c);
                        }
                        for (int j=0; j<le_xi_cs.size();j++) {
                                z3::expr con_item = le_xi_cs[j];
                                closure_item = closure_item && (item.arg(0) <= con_item.arg(1) + (k-1)*c);
                        }
                }
        }
        // std::cout << "<= closure item: " << closure_item << std::endl;


        // 3. >=
        z3::expr_vector ge_cs(z3_ctx());
        z3::expr_vector ge_xi_cs(z3_ctx());
        z3::expr_vector ge_gamma_cs(z3_ctx());
        for (int i=0; i<data_items[2].size(); i++) {
                z3::expr item = data_items[2][i];
                // 1.1 alpha_i = c
                if (item.arg(1).num_args()!=2) {
                        closure_item = closure_item && item;
                        ge_cs.push_back(item);
                } else {
                        z3::expr op1 = item.arg(1).arg(0);
                        int idx_j = index_of_vec(op1, xi);
                        // 1.2 alpha_i = xi_j + c
                        if (idx_j != -1) {
                                closure_item = closure_item && item;
                                ge_xi_cs.push_back(item);
                        }
                        // 1.3 alpha_i = gamma_i + c
                        else if (gamma_i.hash()==op1.hash()) {

                                int c = get_numeral(item.arg(1).arg(1));
                                closure_item = closure_item && (item.arg(0) >= beta_i + k*c);
                                ge_gamma_cs.push_back(item);
                        }
                }
        }
        // std::cout << ">= closure item: " << closure_item << std::endl;

        for (int i=0; i<ge_gamma_cs.size(); i++) {
                z3::expr item = ge_gamma_cs[i];
                int c = get_numeral(item.arg(1).arg(1));
                if (c > 0) {
                        for (int j=0; j<ge_cs.size();j++) {
                                z3::expr con_item = ge_cs[j];
                                closure_item = closure_item && (item.arg(0) >= con_item.arg(1) + (k-1)*c);
                        }
                        for (int j=0; j<ge_xi_cs.size();j++) {
                                z3::expr con_item = ge_xi_cs[j];
                                closure_item = closure_item && (item.arg(0) >= con_item.arg(1) + (k-1)*c);
                        }
                }
        }
        // std::cout << ">= closure item: " << closure_item << std::endl;


        return closure_item;
}

int listsolver::index_of_vec(z3::expr x, z3::expr_vector &vec) {
        for (int i=0; i<vec.size(); i++)
                if (x.hash() == vec[i].hash()) return i;
        return -1;
}

/**
 * normalize data item: x > c -> x >= c+1 x<c -> x<c-1
 * @param x ; expr
 * @return normal expr
 */
z3::expr listsolver::normalize_item(z3::expr x) {
        std::string opa = x.decl().name().str();
        if (opa == ">") {
                if (x.arg(1).num_args()!=2) {
                        int c = get_numeral(x.arg(1))+1;
                        return x.arg(0) >= c;
                } else {
                        int c = get_numeral(x.arg(1).arg(1))+1;
                        return x.arg(0) >= x.arg(1).arg(0)+c;
                }
        }
        if (opa == "<") {
                if (x.arg(1).num_args()!=2) {
                        int c = get_numeral(x.arg(1))-1;
                        return x.arg(0) <= c;
                } else {
                        int c = get_numeral(x.arg(1).arg(1))-1;
                        return x.arg(0) <= x.arg(1).arg(0)+c;
                }
        }
        return x;
}

int listsolver::get_numeral(z3::expr x) {
        if (x.is_numeral()) {return x.get_numeral_int();}
        if (x.is_app() && x.decl().name().str()=="-" && x.num_args()==1 && x.arg(0).is_numeral()) return -x.arg(0).get_numeral_int();
        if (x.is_app()
            && (x.decl().name().str() == "to_real" || x.decl().name().str() == "to_int")) return get_numeral(x.arg(0));
        return 0;
}


/**
 * atom in formula to abstraction
 * @param  atom [the atom in formula, like p(Z1, mu; Z2, nu, chi) or (pto Z (*))]
 * @param  i    [the index in formula]
 * @param new_bools [new bool vars]
 * @return      [the abstraction]
 */
z3::expr listsolver::pred2abs(z3::expr &atom, int i, z3::expr_vector& new_bools){
        // logger() << "listsolver::pred2abs \n";
        // logger() << "atom: " << atom << std::endl;
        // logger() << "i: " << i << std::endl;

        std::string source = atom.arg(0).to_string();
        std::string new_name = m_ctx.logger().string_format("[%s,%d]", source.c_str(), i);
        // 1 introduce new vars
        z3::expr source_bool = z3_ctx().bool_const(new_name.c_str()); // [Z1,i]
        new_bools.push_back(source_bool);
        z3::expr source_int = z3_ctx().int_const(source.c_str()); // Z1

        z3::expr atom_f(z3_ctx());
        if (atom.decl().name().str() == "pto") {
                // 1.1 pto atom
                atom_f = (source_bool && source_int > 0);
        } else {
                std::string pred_name = atom.decl().name().str();
                int index = index_of_pred(pred_name);
                predicate pred = m_ctx.get_pred(index); // get predicate definition
                int size = atom.num_args() - pred.size_of_static_parameters(); // size of source and destination paramaters
                // 1.2 predicate atom
                // 1.2.1 supposing atom is empty
                std::string k_name = m_ctx.logger().string_format("[k,%d]", i);
                z3::expr k_i_int = z3_ctx().int_const(k_name.c_str()); // k_i

                z3::expr or_0(z3_ctx());
                z3::expr dest_int = z3_ctx().int_const(atom.arg(size/2).to_string().c_str());
                or_0 = !source_bool && (k_i_int == 0) && (source_int == dest_int);
                for (int j=1; j<size/2;j++) {
                        if (atom.arg(j).get_sort().sort_kind() == Z3_UNINTERPRETED_SORT) {
                                z3::expr arg_j_int = z3_ctx().int_const(atom.arg(j).to_string().c_str());
                                z3::expr arg_j2_int = z3_ctx().int_const(atom.arg(j+size/2).to_string().c_str());
                                or_0 = or_0 && (arg_j_int == arg_j2_int);
                        } else {
                                or_0 = or_0 && (atom.arg(j)==atom.arg(j+size/2));
                        }
                }

                // logger() << "or_0: " << or_0 << std::endl;

                // 1.2.2 supposing atom is not emtpy
                z3::expr phi_pd = delta_ge1_predicates[index]; // the predicate data closure
                z3::expr_vector args = pred.get_pars();
                z3::expr_vector f_args(z3_ctx()); // predicate parameters, formal parameters
                z3::expr_vector a_args(z3_ctx()); // actual parameters

                // init formla parameters and actual parameters
                for (int i=0; i<atom.num_args(); i++) {
                        if (atom.arg(i).get_sort().sort_kind() != Z3_UNINTERPRETED_SORT) {
                                f_args.push_back(args[i]);
                                a_args.push_back(atom.arg(i));
                        }
                }
                z3::expr k_int = z3_ctx().int_const("k"); // k is in data closure
                f_args.push_back(k_int);

                a_args.push_back(k_i_int);

                // logger() <<"formal pars: " << f_args << std::endl;
                // logger() <<"actual pars: " << a_args << std::endl;

                z3::expr or_1(z3_ctx()); // by ufld_1
                z3::expr or_2(z3_ctx()); // by ufld_ge_2

                int idx = pred.idx_E_gamma(); // check whether E ouccus in gamma
                logger() << "idx: " << idx << std::endl;

                if (idx != -1) {
                        // E occurs in gamma TOCHECK
                        z3::expr E = atom.arg(0);
                        z3::expr beta_idx = atom.arg(size/2+idx+1);
                        z3::expr beta_idx_int = z3_ctx().int_const(beta_idx.to_string().c_str());

                        std::string beta_idx_name = m_ctx.logger().string_format("[%s,%d]", beta_idx.to_string().c_str(), i);
                        z3::expr beta_idx_bool = z3_ctx().bool_const(beta_idx_name.c_str());
                        new_bools.push_back(beta_idx_bool); // new bool var

                        // ufld_1
                        z3::expr ufld_1 = (source_int == beta_idx_int && k_int == 1 && phi_pd);
                        // logger() << "ufld_1: " << ufld_1 << std::endl;
                        or_1 = ((source_bool && source_int>0 && beta_idx_bool && beta_idx_int>0) && ufld_1.substitute(f_args, a_args));
                        // logger() << "or_1: " << or_1 << std::endl;
                        // ufld_ge_2
                        z3::expr ufld_ge_2 = (source_int != beta_idx_int && k_int >= 2 && phi_pd);
                        or_2 = ((source_bool && source_int>0 && beta_idx_bool && beta_idx_int>0) && ufld_ge_2.substitute(f_args, a_args));
                        // logger() << "or_2: " << or_2 << std::endl;
                } else {
                        // E does not occur in gamma
                        // ufld_1
                        z3::expr ufld_1 = (k_int == 1 && phi_pd);
                        // std::cout << "ufld_1: " << ufld_1 << std::endl;
                        or_1 =  source_bool && source_int>0 && ufld_1.substitute(f_args, a_args);
                        // logger() << "or_1: " << or_1 << std::endl;
                        // ufld_ge_2
                        z3::expr ufld_ge_2 = (k_int >= 2 && phi_pd);
                        or_2 = source_bool && source_int>0 && ufld_ge_2.substitute(f_args, a_args);
                        // logger() << "or_2: " << or_2 << std::endl;
                }

                // 1.3 or
                atom_f = or_0 || or_1 || or_2;
        }
        return atom_f;
}


/**
 * atom in m -> dot string
 * @param m: the model of abstraction
 * @param atom : the space atom in sigam
 * @param i : the index
 * @param n : the size of sigam
 * @return str in dot
 */
std::string listsolver::get_model_of_atom(z3::model &m, z3::expr &atom, int i, int n) {
        std::string s = "";
        if (atom.decl().name().str() == "pto") {
                // 1.1 pto atom
                std::string node_str="";
                std::string edge_str="";

                write_pto(m, atom, i, n, node_str, edge_str);

                // std::cout << "node_str: " << node_str << std::endl;
                // std::cout << "edge_str: \n" << edge_str << std::endl;

                s = node_str + "\n" + edge_str + "\n";

        } else {
                //1.2 predicate atom
                // 1.2.1 get k
                std::string node_str="";
                std::string edge_str="";
                std::string k_name = m_ctx.logger().string_format("[k,%d]", i);
                z3::expr k_i_int = z3_ctx().int_const(k_name.c_str()); // k_i
                z3::expr k_i_interp = get_interp(m, k_i_int);
                // std::cout << "model: " << m << std::endl;
                int k = 0;
                if (k_i_interp.to_string() != "nil") {
                        k = k_i_interp.get_numeral_int();
                }
                // std::cout << "k: " << k << std::endl;
                if (k > 0) {
                        // 1.2.2 get predicate
                        std::string pred_name = atom.decl().name().str();
                        int index = index_of_pred(pred_name);
                        predicate pred = m_ctx.get_pred(index); // get predicate definition
                        int size = atom.num_args() - pred.size_of_static_parameters(); // size of source and destination paramaters
                        pred_rule rule = pred.get_rule(0);
                        z3::expr data = rule.get_data();
                        z3::expr pto = rule.get_pto();
                        z3::expr rec_app = rule.get_rec_apps()[0];
                        z3::expr plfld = pred.get_plfld();

                        // std::cout << "plfld: " << pred.get_plfld() << std::endl;

                        z3::expr_vector f_args = pred.get_pars(); // predicate parameters, formal parameters
                        z3::expr_vector a_args(z3_ctx()); // actual parameters

                        // init formla parameters and actual parameters
                        for (int j=0; j<atom.num_args(); j++) {
                                a_args.push_back(atom.arg(j));
                        }

                        z3::expr_vector x_h(z3_ctx());
                        rule.get_x_h(x_h);
                        // z3::expr_vector x_h_cons(z3_ctx());
                        for (int j=0; j<x_h.size(); j++) {
                                f_args.push_back(x_h[j]);
                                z3::sort st = x_h[j].get_sort();
                                std::string name = x_h[j].to_string();
                                name = name.replace(name.find(":"), 1, "");
                                name = name.replace(name.find(" "), 1, "_");
                                std::string ss = logger().string_format("%s_%s_%d_%d",   name.substr(1, name.length()-2).c_str(), pred_name.c_str(), i, 1);
                                a_args.push_back(z3_ctx().constant(ss.c_str(), st));
                        }

                        // std::cout << "f_args: " << f_args << std::endl;
                        // std::cout << "a_args: " << a_args << std::endl;

                        //
                        int idx = pred.idx_E_gamma(); // check whether E ouccus in gamma
                        logger() << "idx: " << idx << std::endl;

                        int node_i = 1;
                        pto = pto.substitute(f_args, a_args);

                        std::string node_name = "";

                        z3::solver sol(z3_ctx());
                        sol.add(z3_ctx().bool_val(true));
                        sol.check();
                        z3::model data_m = sol.get_model();
                        z3::expr data_eval = data;


                        while(node_i <= k) {
                                // node_1
                                z3::expr plfld_interp(z3_ctx());

                                if (node_i == k) {
                                        plfld_interp = get_interp(m, a_args[size/2]);
                                } else if(node_i==k-1 && idx != -1){
                                        plfld_interp = get_interp(m, a_args[size/2+1]);
                                }

                                if (node_i == 1) {
                                        // E ->
                                        write_pred_pto(m, data_m, pto, i, n, plfld_interp, plfld, node_i, k, node_str, edge_str);

                                        // std::cout << "node_str: " << node_str << std::endl;
                                        // std::cout << "edge_str: " << edge_str << std::endl;
                                        s += node_str + "\n" + edge_str + "\n";

                                } else {
                                        node_str = "";
                                        edge_str = "";

                                        // recompute f_args and a_args
                                        f_args.resize(0);
                                        for (int j=0; j<a_args.size(); j++) {
                                                f_args.push_back(a_args[j]);
                                        }
                                        a_args.resize(0);
                                        for (int j=0; j<rec_app.num_args(); j++) {
                                                a_args.push_back(rec_app.arg(j));
                                        }

                                        for (int j=0; j<x_h.size(); j++) {
                                                z3::sort st = x_h[j].get_sort();
                                                std::string name = x_h[j].to_string();
                                                name = name.replace(name.find(":"), 1, "");
                                                name = name.replace(name.find(" "), 1, "_");
                                                std::string ss =  logger().string_format("%s_%s_%d_%d",  name.substr(1, name.length()-2).c_str(), pred_name.c_str(), i, node_i);
                                                a_args.push_back(z3_ctx().constant(ss.c_str(), st));
                                        }

                                        // std::cout << "f_args: " << f_args << std::endl;
                                        // std::cout << "a_args: " << a_args << std::endl;

                                        pto = pto.substitute(f_args, a_args);

                                        sol.reset();
                                        sol.add(data_eval);
                                        sol.check();
                                        data_m = sol.get_model();

                                        if (node_i == k && idx!=-1) {
                                                z3::expr_vector args1(z3_ctx());
                                                args1.push_back(pto.arg(0));
                                                z3::expr_vector args2(z3_ctx());
                                                args2.push_back(a_args[size/2+1]);
                                                pto = pto.substitute(args1, args2);
                                        }

                                        // std::cout << "pto: " << pto << std::endl;
                                        // std::cout << "data: " << data << std::endl;
                                        // std::cout << "rec_app: " << rec_app << std::endl;
                                        write_pred_pto(m, data_m, pto, i, n, plfld_interp, plfld, node_i, k, node_str, edge_str);

                                        // std::cout << "node_str: " << node_str << std::endl;
                                        // std::cout << "edge_str: " << edge_str << std::endl;
                                        s += node_str + "\n" + edge_str + "\n";
                                }
                                data = data.substitute(f_args, a_args);
                                data_eval = m.eval(data);
                                rec_app = rec_app.substitute(f_args, a_args);

                                node_i ++;
                        }
                }
        }
        return s;
}

/**
 * check whether the source is allocated
 * @param m : the model of abstraction
 * @params source : the source
 * @params n : the atom size
 * @return true or false
 */
bool listsolver::is_allocated(z3::model &m, z3::expr &source, int n) {
        if (source.get_sort().sort_kind() == Z3_UNINTERPRETED_SORT) {
                if (source.to_string().find("var_") == 0) return true;

                for (int i=0; i<n; i++) {
                        std::string source_name = logger().string_format("[%s,%d]", source.to_string().c_str(), i);
                        z3::expr source_bool = z3_ctx().bool_const(source_name.c_str());
                        if (m.has_interp(source_bool.decl())) {
                                z3::expr bool_interp = m.get_const_interp(source_bool.decl());
                                return bool_interp.to_string() == "true";
                        }
                }
        }
        return false;
}

/**
 * translate pto into dot_str
 * @param m : the model of abstraction
 * @param pto : the pto atom
 * @param n : the atom num
 * @param node_str the output
 * @param edge_str the output
 */
void listsolver::write_pto(z3::model& m, z3::expr& pto, int i, int n, std::string& node_str, std::string& edge_str) {
        z3::expr source = pto.arg(0);
        z3::expr source_interp = get_interp(m, source);
        std::string node_name = logger().string_format("\"node_%s\"", source_interp.to_string().c_str());
        node_str = logger().string_format("%s [label=\"atom_%d|<f0>(%s)", node_name.c_str(), i, source_interp.to_string().c_str());

        z3::expr sref = pto.arg(1);
        if (sref.decl().name().str() == "sref") {
                for (int j=0; j<sref.num_args(); j++) {
                        z3::expr ref = sref.arg(j);
                        std::string flag_str = "";
                        z3::expr dest = ref.arg(1);
                        z3::expr dest_interp = get_interp(m, dest);


                        flag_str = logger().string_format("<f%d>%s", (j+1), ref.arg(0).to_string().c_str());

                        if (is_allocated(m, dest, n)) {
                                edge_str = logger().string_format("%s%s:f%d->\"node_%s\":f0;\n", edge_str.c_str(), node_name.c_str(), (j+1), dest_interp.to_string().c_str());
                        }

                        node_str +=  logger().string_format("|%s:(%s)",  flag_str.c_str(),  dest_interp.to_string().c_str());
                }
        } else {
                std::string flag_str = "";
                z3::expr dest = sref.arg(1);
                z3::expr dest_interp = get_interp(m, dest);
                flag_str = logger().string_format("<f%d>%s", 1, sref.arg(0).to_string().c_str());

                if (is_allocated(m, dest, n)) {
                        edge_str = logger().string_format("%s%s:f%d->\"node_%s\":f0;\n", edge_str.c_str(), node_name.c_str(), 1, dest_interp.to_string().c_str());
                }

                node_str +=  logger().string_format("|%s:(%s)",  flag_str.c_str(),  dest_interp.to_string().c_str());
        }
        node_str += "\"];\n";
}

/**
 * translate pred_pto into dot_str
 * @param m : the model of abstraction
 * @param pto : the pto atom
 * @param n : the atom num
 * @param plfld_interp : plfld_interp (the last two)
 * @param plfld : plfld
 * @param node_i : node_i times
 * @param k : the predicate times
 * @param node_str the output
 * @param edge_str the output
 */
void listsolver::write_pred_pto(z3::model& m, z3::model& data_m, z3::expr& pto, int i, int n, z3::expr& plfld_interp, z3::expr& plfld, int node_i, int k, std::string& node_str, std::string& edge_str) {
        z3::expr source = pto.arg(0);
        z3::expr source_interp = get_interp(m, source);
        std::string node_name = logger().string_format("\"node_%s\"",  source_interp.to_string().c_str());
        node_str = logger().string_format("%s [label=\"atom_%d|<f0>(%s)", node_name.c_str(), i,  source_interp.to_string().c_str());
        z3::expr sref = pto.arg(1);
        for (int j=0; j<sref.num_args(); j++) {
                z3::expr ref = sref.arg(j);
                std::string flag_str = "";
                z3::expr dest = ref.arg(1);
                z3::expr dest_interp = get_interp(m, dest);

                if (dest.get_sort().sort_kind() == Z3_UNINTERPRETED_SORT) {
                        if (plfld.to_string() == ref.arg(0).to_string() && Z3_ast(plfld_interp)!=0) {
                                dest_interp = plfld_interp;
                        }
                } else {
                        dest_interp = get_interp(data_m, dest);
                }

                flag_str = logger().string_format("<f%d>%s", (j+1), ref.arg(0).to_string().c_str());

                if (is_allocated(m, dest, n) && dest_interp.to_string()!="nil") {
                        edge_str = logger().string_format("%s%s:f%d->\"node_%s\":f0;\n", edge_str.c_str(), node_name.c_str(), (j+1), dest_interp.to_string().c_str());
                }

                node_str +=  logger().string_format("|%s:(%s)",  flag_str.c_str(),  dest_interp.to_string().c_str());
        }
        node_str += "\"];\n";
}


void listsolver::init_int_vector(std::vector<int> &vec, int size) {
        vec.clear();
        for (int i=0; i<size; i++) {
                vec.push_back(-1);
        }
}

int listsolver::index_of_int(int x, std::vector<int> &vec) {
        for (int i=0; i<vec.size(); i++) {
                if (vec[i] == x) return i;
        }
        return -1;
}
