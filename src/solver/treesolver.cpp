#include "treesolver.h"

/**
 *###################### treesolver ####################################
 */
/**
 * check sat, negf in m_ctx
 * or check entl, negf |= posf
 * @return z3::check_result
 */
z3::check_result treesolver::check_sat() {
        compute_all_delta_ge1_p();
        logger() << "tree sat problem: " << std::endl;
        z3::expr formula = m_ctx.get_negf();
        // 2.2.1 formula -> (delta \and sigma)
        z3::expr data(z3_ctx());
        z3::expr space(z3_ctx());
        get_data_space(formula, data, space);
        z3::expr f_abs = data;
        // 2.2.2 space part
        f_abs = f_abs && abs_space(space);

        // 2.2.3 sep (\phi_star)
        f_abs = f_abs && abs_phi_star();

        z3::solver s(z3_ctx());
        s.add(f_abs);
        z3::check_result result = s.check();
        return result;
}


/**
 * check sat, negf in m_ctx
 * or check entl, negf |= posf
 * @return z3::check_result
 */
z3::check_result treesolver::check_entl() {
        // TODO ....
        logger() << "tree entl problem:\n";
        z3::solver s(z3_ctx());
        z3::expr f_abs = z3_ctx().bool_val(true);
        s.add(f_abs);
        z3::check_result result = s.check();
        return result;
}

/**
 * check whether all predicate definitions are corresponding to userdef constraints
 */
void treesolver::check_preds() {
        for (int i=0; i<m_ctx.pred_size(); i++) {
                predicate pred = m_ctx.get_pred(i);
                if (pred.is_tree()) {
                        treechecker tc(pred);
                        tc.check_args();
                        tc.check_rec_rules();
                }
        }

}

z3::expr treesolver::pred2abs(z3::expr &atom, int i) {
        std::string source = atom.arg(0).to_string();
        std::string new_name = m_ctx.logger().string_format("[%s,%d]", source.c_str(), i);
        // 1.2 introduce new boolean var
        z3::expr source_bool = z3_ctx().bool_const(new_name.c_str());
        new_bools.push_back(source_bool);
        z3::expr source_int = z3_ctx().int_const(source.c_str());

        z3::expr atom_f(z3_ctx());
        if (atom.decl().name().str() == "pto") {
                // 1.3 pto atom
                atom_f = (source_bool && source_int > 0);
        } else {
                // 1.3 predicate atom
                int size = atom.num_args();
                std::string dest = atom.arg(size/2).to_string();
                z3::expr dest_int = z3_ctx().int_const(dest.c_str());

                // supposing atom is empty
                z3::expr or_1(z3_ctx());
                or_1 = !source_bool && (source_int == dest_int);
                for (int j=1; j<size/2;j++) {
                        or_1 = or_1 && (atom.arg(j)==atom.arg(j+size/2));
                }

                // supposing atom is not emtpy
                z3::expr or_2(z3_ctx());
                or_2 = source_bool && source_int>0;

                // 1.4 substitute formal args by actual args
                std::string pred_name = atom.decl().name().str();
                int index = index_of_pred(pred_name);
                z3::expr phi_pd = delta_ge1_predicates[index];
                z3::expr_vector f_args = m_ctx.get_pred(index).get_pars();
                z3::expr_vector a_args(z3_ctx());
                for (int i=0; i<atom.num_args(); i++) {
                        a_args.push_back(atom.arg(i));
                }
                z3::expr pred_abs = phi_pd.substitute(f_args, a_args);
                or_2 = or_2 && pred_abs;

                atom_f = or_1 || or_2;
        }

        return atom_f;
}


/**
 * compute all predicate delta_ge1_p (delta_ge1_predicates)
 */
void treesolver::compute_all_delta_ge1_p() {
        logger() << "compute all delta ge1 predicate. \n";
        for (int i=0; i<m_ctx.pred_size(); i++) {
                logger() << "compute predicate " << i << std::endl;
                predicate pred = m_ctx.get_pred(i);
                // 1. compute phi_pd_abs (lfp)
                z3::expr phi_pd_abs = compute_delta_phi_pd(pred);
                logger() << "compute phi_pd: " << phi_pd_abs << std::endl;
                // 2. compute delta_ge1_p
                z3::expr delta_ge1_p_abs = z3_ctx().bool_val(false);

                // 2.1 for all rec rules
                for (int i=0; i<pred.rec_rule_size(); i++) {
                        pred_rule rule = pred.get_rule(i);
                        z3::expr delta_ge1_r_abs = compute_delta_ge1_rule(rule, pred, phi_pd_abs);
                        delta_ge1_p_abs = delta_ge1_p_abs || delta_ge1_r_abs;
                }
                delta_ge1_predicates.push_back(delta_ge1_p_abs);
        }
}

/**
 * compute delta_ge1_r
 * @param rule : the rule R
 * @param pred : the predicate
 * @param delta_phi_pd : the formula of least fixed point
 * @return expr
 */
z3::expr treesolver::compute_delta_ge1_rule(pred_rule &rule, predicate &pred, z3::expr &delta_phi_pd) {
        logger() << "compute delta ge1 rule : " << std::endl;
        // compute exists expr_vector formula
        // 1. expr_vector by rule
        z3::expr_vector x_h = get_x_h(rule);
        // 2. formula
        z3::expr formula = rule.get_data();
        // 2.1 alpha, beta by pred
        z3::expr_vector alpha(z3_ctx());
        z3::expr_vector beta(z3_ctx());
        get_alpha_beta(pred, alpha, beta);
        // 2.2 gamma, delta, epsilon by rule
        z3::expr_vector gamma(z3_ctx());
        z3::expr_vector delta(z3_ctx());
        z3::expr_vector epsilon(z3_ctx());
        get_gamma_delta_epsilon(rule, gamma, delta, epsilon);
        // 2.3 substitute alpha by delta
        z3::expr phi_pd1 = delta_phi_pd.substitute(alpha, delta);
        formula = formula && phi_pd1;
        // 2.4 substitute alpha, beta by gamma,epsilon
        for (int i=0; i<beta.size(); i++) {
                alpha.push_back(beta[i]);
                gamma.push_back(epsilon[i]);
        }
        z3::expr phi_pd2 = delta_phi_pd.substitute(alpha, gamma);
        formula = formula && phi_pd2;
        return exists(x_h, formula);
}


/**
 * compute the delta_phi_pd
 * @param pred : predicate
 * @return expr
 */
z3::expr treesolver::compute_delta_phi_pd(predicate &pred) {
        logger() << "compute delta phi predicate. \n";
        z3::expr_vector args = pred.get_pars();
        int num_of_args = args.size();
        if (num_of_args == 2) {
                // P(E,F)
                return z3_ctx().bool_val(true);
        } else if (args[num_of_args/2-1].get_sort().to_string() == "Int") {
                if (num_of_args > 4) {
                        // TODO data and size type
                        return z3_ctx().bool_val(true);

                } else {
                        // TODO only size type
                        return z3_ctx().bool_val(true);
                }
        } else {
                // only data type
                z3::expr phi_pd_abs(z3_ctx());
                // 1. compute least fixed point (Order Graph)
                OrderGraphSet ogset = lfp(pred);
                // std::cout << "ogset size: " << ogset.size() << std::endl;
                // 2. Graph to expr
                for (int i=0; i<ogset.size(); i++) {
                        OrderGraph og = ogset.at(i);
                        std::string f_name = logger().string_format("G%d.dot", i);
                        og.printAsDot(f_name);
                        z3::expr og_e = graph2exp(og);
                        // std::cout << "og expr: " << og_e << std::endl;
                        if (Z3_ast(phi_pd_abs) == 0) {
                                phi_pd_abs = og_e;
                        } else {
                                phi_pd_abs = phi_pd_abs || og_e;
                        }
                }

                return phi_pd_abs;
        }
}


/**
 * compute lfp(pred)
 * @param pred: the predicate definition
 * @return ogset: the least fixed point: order graph set
 */
OrderGraphSet treesolver::lfp(predicate &pred) {
        OrderGraph g0;
        z3::expr base_rule = pred.get_base_rule();
        // 1. G0
        expr2graph(base_rule, g0);

        // 2. iterate
        OrderGraphSet ogset;
        ogset.addOrderGraph(g0);
        OrderGraphSet ogset_new;
        // 2.1 get alpha, beta
        std::vector<Vertex> alpha;
        std::vector<Vertex> beta;
        get_alpha_beta(pred, alpha, beta);


        std::set<z3::expr, exprcomp> const_exps;
        get_constants(pred, const_exps);
        std::vector<Vertex> constants;
        exp2vertex(const_exps, constants);


        while(!(ogset == ogset_new)) {
                ogset_new = ogset;
                // for each recursive rule
                for (int i=0; i<pred.rec_rule_size(); i++) {
                        pred_rule rule = pred.get_rule(i);
                        z3::expr data = rule.get_data();
                        OrderGraph og_cons;
                        expr2graph(data, og_cons);
                        std::vector<Vertex> delta;
                        std::vector<Vertex> gamma;
                        std::vector<Vertex> epsilon;

                        get_gamma_delta_epsilon(rule, gamma, delta, epsilon);


                        // T_R(G)
                        for (int i=0; i<ogset.size(); i++) {
                                for (int j=0; j<ogset.size(); j++) {
                                        OrderGraph og1 = ogset.at(i);
                                        OrderGraph og2 = ogset.at(j);

                                        // g_delta constructed by recursive rule (data constraint)
                                        OrderGraph g_delta = og_cons;
                                        // substitution1
                                        og1.substitution(alpha, delta);

                                        std::vector<Vertex> old_vs2 = alpha;
                                        old_vs2.insert(old_vs2.end(), beta.begin(), beta.end());
                                        std::vector<Vertex> new_vs2 = gamma;
                                        new_vs2.insert(new_vs2.end(), epsilon.begin(), epsilon.end());

                                        // substitution2
                                        og2.substitution(old_vs2, new_vs2);

                                        //union
                                        g_delta.unionGraph(og1);
                                        g_delta.unionGraph(og2);

                                        //saturate
                                        g_delta.saturate();

                                        if (g_delta.isConsistent()) {
                                                // restriction
                                                std::set<Vertex> v_set;
                                                old_vs2.insert(old_vs2.end(), constants.begin(), constants.end()); // add constant_set
                                                vector2set(old_vs2, v_set);
                                                g_delta.restriction(v_set);
                                                ogset.addOrderGraph(g_delta);
                                        }
                                }
                        }
                }
        }

        return ogset;
}


/**
 * get constants from expr
 * @param exp : the expression
 * @param constants : the set of constant expr
 */
void treesolver::get_constants(const z3::expr &exp, std::set<z3::expr, exprcomp> &constants) {
        if (exp.is_app()) {
                if (exp.is_numeral()) {
                        constants.insert(exp);
                } if((exp.decl().name().str() == "to_real" || exp.decl().name().str() == "to_int")){
                        constants.insert(exp.arg(0));
                }else {
                        for (unsigned i=0; i<exp.num_args(); i++) {
                                get_constants(exp.arg(i), constants);
                        }
                }
        } else if(exp.is_quantifier()) {
                get_constants(exp.body(), constants);
        }
}


/**
 * get constants from pred
 * @param pred : the predicate
 * @param constants : the set of constant expr
 */
void treesolver::get_constants(predicate& pred, std::set<z3::expr, exprcomp> &constants) {
        int size = pred.rec_rule_size();
        for (int i=0; i<size; i++) {
                z3::expr data = pred.get_rule(i).get_data();

                get_constants(data, constants);
                z3::expr_vector rec_apps = pred.get_rule(i).get_rec_apps();
                for (int i=0; i<rec_apps.size(); i++) {
                        z3::expr app = rec_apps[i];
                        get_constants(app, constants);
                }
        }
}

/**
 * get alpha and beta parameters by predicate
 * @param pred : the predicate
 * @param alpha : the result alpha
 * @param beta : the reuslt beta
 */
void treesolver::get_alpha_beta(predicate &pred, z3::expr_vector &alpha, z3::expr_vector &beta) {
        z3::expr_vector args = pred.get_pars();
        int size = args.size();
        for (int i=1; i<size/2; i++) {
                alpha.push_back(args[i]);
                beta.push_back(args[i+size/2]);
        }
}

/**
 * get alpha and beta parameters by predicate
 * @param pred : the predicate
 * @param alpha : the result alpha vertex vector
 * @param beta : the reuslt beta vertex vector
 */
void treesolver::get_alpha_beta(predicate &pred, std::vector<Vertex> &alpha, std::vector<Vertex> &beta) {
        z3::expr_vector alpha_e(z3_ctx());
        z3::expr_vector beta_e(z3_ctx());
        get_alpha_beta(pred, alpha_e, beta_e);
        exp2vertex(alpha_e, alpha);
        exp2vertex(beta_e, beta);
}

/**
 * get delta, gamma and epsilone by pred_rule
 * @param rule : the predicate rule
 * @param gamma : the result gamma
 * @param delta : the result delta
 * @param epsilon : the result epsilon
 */
void treesolver::get_gamma_delta_epsilon(pred_rule &rule, z3::expr_vector &gamma, z3::expr_vector &delta, z3::expr_vector &epsilon) {
        z3::expr app1 = rule.get_rec_apps()[0];
        z3::expr app2 = rule.get_rec_apps()[1];
        int size = app1.num_args();
        bool is_nil1 = app1.arg(size/2).to_string() == "nil";
        if (is_nil1) {
                for (int i=1; i<size/2; i++) {
                        gamma.push_back(app1.arg(i));
                        epsilon.push_back(app1.arg(i+size/2));
                        delta.push_back(app2.arg(i));
                }
        } else {
                for (int i=1; i<size/2; i++) {
                        gamma.push_back(app2.arg(i));
                        epsilon.push_back(app2.arg(i+size/2));
                        delta.push_back(app1.arg(i));
                }
        }
}

/**
 * get delta, gamma and epsilone by pred_rule
 * @param rule : the predicate rule
 * @param gamma : the result gamma vertex vector
 * @param delta : the result delta vertex vector
 * @param epsilon : the result epsilon vertex vector
 */
void treesolver::get_gamma_delta_epsilon(pred_rule& rule, std::vector<Vertex>& gamma, std::vector<Vertex>&  delta, std::vector<Vertex>& epsilon) {
        z3::expr_vector gamma_e(z3_ctx());
        z3::expr_vector delta_e(z3_ctx());
        z3::expr_vector epsilon_e(z3_ctx());
        get_gamma_delta_epsilon(rule, gamma_e, delta_e, epsilon_e);
        exp2vertex(gamma_e, gamma);
        exp2vertex(delta_e, delta);
        exp2vertex(epsilon_e, epsilon);
}

/**
 * get x_h of predicate rule
 * @param rule : the predicate rule
 * @return expr_vector : the x_h vector (maybe include redundant const)
 */
z3::expr_vector treesolver::get_x_h(pred_rule &rule) {
        z3::expr_vector x_h(z3_ctx());
        rule.get_x_h(x_h);
        z3::expr_vector x_h_const(z3_ctx());
        for (int i=0; i<x_h.size(); i++) {
                z3::expr exp = x_h[i];
                if (exp.get_sort().is_arith()) {
                        x_h_const.push_back(z3_ctx().real_const(simplify_var_name(exp.to_string()).c_str()));
                }
        }
        return x_h_const;
}


/**
 * expr to OrderGraph
 * @param exp : the expression
 * @param og : the OrderGraph
 */
void treesolver::expr2graph(z3::expr &exp, OrderGraph &og) {
        // std::cout << "graph expr: " << exp << std::endl;
        for (int i=0; i<exp.num_args(); i++) {
                z3::expr item = exp.arg(i);
                if (item.num_args() == 2 && item.arg(0).get_sort().is_arith()) {
                        Vertex v1(get_exp_name(item.arg(0)));
                        Vertex v2(get_exp_name(item.arg(1)));
                        og.addVertex(v1);
                        og.addVertex(v2);
                        std::string app = item.decl().name().str();
                        if(app == "=") {
                                Edge edge(v1, LABEL_LE, v2);
                                og.addEdge(edge);
                                Edge edge1(v2, LABEL_LE, v1);
                                og.addEdge(edge1);
                        } else if (app == "<=") {
                                Edge edge(v1, LABEL_LE, v2);
                                og.addEdge(edge);
                        } else if (app == "<") {
                                Edge edge(v1, LABEL_LT, v2);
                                og.addEdge(edge);
                        } else if (app == ">=") {
                                Edge edge(v2, LABEL_LE, v1);
                                og.addEdge(edge);
                        } else if (app == ">") {
                                Edge edge(v2, LABEL_LT, v1);
                                og.addEdge(edge);
                        }
                }
        }
}


/**
 * transform expr vector into vertex vector
 * @param exp_vec : the expr vector
 * @param ver_vec : the vertex vector
 */
void treesolver::exp2vertex(z3::expr_vector &exp_vec, std::vector<Vertex> &ver_vec) {
        for (int i=0; i<exp_vec.size(); i++) {
                z3::expr exp = exp_vec[i];
                Vertex v(get_exp_name(exp));
                ver_vec.push_back(v);
        }
}

/**
 * transform expr set into vertex vector
 * @param exp_set : the expr set
 * @param ver_vec : the vertex vector
 */
void treesolver::exp2vertex(std::set<z3::expr, exprcomp> &exp_set, std::vector<Vertex> &ver_vec) {
        for (auto exp : exp_set) {
                Vertex v(get_exp_name(exp));
                ver_vec.push_back(v);
        }
}

/**
 * transform vertex vector into vertex set
 * @param ver_vec : the vertex vector
 * @param ver_set : the vertex set
 */
void treesolver::vector2set(std::vector<Vertex> &ver_vec, std::set<Vertex> &ver_set) {
        for (int i=0; i<ver_vec.size(); i++) {
                ver_set.insert(ver_vec[i]);
        }
}


std::string treesolver::get_exp_name(z3::expr exp) {
        if (exp.is_app()) {
                std::string app = exp.decl().name().str();
                if (app == "to_real") {
                        return get_exp_name(exp.arg(0));
                } else if (app == "to_int") {
                        std::string dec_str = get_exp_name(exp.arg(0));
                        int index_dot = dec_str.find(".");
                        if (index_dot > -1) {
                                return dec_str.substr(0, index_dot);
                        }
                        return dec_str;
                } else {
                        if (app == "-" && exp.num_args() == 1 && exp.arg(0).is_numeral()) {
                                std::string str = "-";
                                str.append(exp.arg(0).to_string());
                                return str;
                        }
                        return exp.to_string();
                }
        } else {
                if (exp.is_var()) {
                        return simplify_var_name(exp.to_string());
                }
                return "";
        }
}

/**
 * simplify exist variable name in z3 expr
 * @param str : like (:var 0)
 * @return str : like var0
 */
std::string treesolver::simplify_var_name(std::string str){
        std::string short_name = "var";
        //        std::cout << "before simplify: "<<str << std::endl;
        short_name.append(str.substr(6, str.length()-7));
        //        std::cout << "after simplify: "<<short_name << std::endl;
        return short_name;
}

/**
 *transform vertex  into expr
 *@param v : vertex
 *@return exp : real_const or real_val
 */
z3::expr treesolver::vertex2exp(Vertex v) {
        std::locale local;
        std::string name = v.getName();
        if (isdigit(name[0], local)) {
                // digit
                return z3_ctx().real_val(name.c_str());
        } else {
                return z3_ctx().real_const(name.c_str());
        }
}

/**
 * transform Edge into expr
 * @param e : the edge (a, <, b)
 * @return exp : the expr (< a b)
 */
z3::expr treesolver::edge2exp(Edge e) {
        if (e.getLabel() == LABEL_LE) {
                return vertex2exp(e.getSource()) <= vertex2exp(e.getDest());
        } else {
                return vertex2exp(e.getSource()) < vertex2exp(e.getDest());
        }
}

/**
 * transform Graph inot expr
 * @param og : the OrderGraph
 * @return exp : the expr
 */
z3::expr treesolver::graph2exp(OrderGraph &og) {
        std::set<Edge> edges = og.getEdges();
        z3::expr graph_e(z3_ctx());
        for (auto edge : edges) {
                z3::expr edge_e = edge2exp(edge);
                if (Z3_ast(graph_e) == 0) {
                        graph_e = edge_e;
                } else {
                        graph_e = graph_e && edge_e;
                }
        }
        return graph_e;
}
