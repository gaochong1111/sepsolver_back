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
        // 1.1 compute all phi_p TODO.
        compute_all_data_closure();
        z3::expr formula = m_ctx.get_negf();
        // 2.2.1 formula -> (delta \and sigma)
        z3::expr data(z3_ctx());
        z3::expr space(z3_ctx());
        // get_data_space(formula, data, space);
        z3::expr f_abs = data;
        // 2.2.2 space part
        if (Z3_ast(f_abs) == 0) {
                // f_abs = abs_space(space);
        } else {
                // f_abs = f_abs && abs_space(space);
        }
        // 2.2.3 sep (\phi_star)
        // f_abs = f_abs && abs_phi_star();
        f_abs = z3_ctx().bool_val(true);

        z3::solver s(z3_ctx());
        s.add(f_abs);
        z3::check_result result = s.check();
        std::cout << "result: " << result << std::endl;
        return result;
}

/**
 * check sat, negf in m_ctx
 * or check entl, negf |= posf
 * @return z3::check_result
 */
z3::check_result listsolver::check_entl() {
        // TODO ....
        logger() << "list entl problem:\n";
        z3::solver s(z3_ctx());
        z3::expr f_abs = z3_ctx().bool_val(true);
        s.add(f_abs);
        z3::check_result result = s.check();
        return result;
}

/**
 * compute all predicate data  closure
 * @return : expr data closure
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
                                z3::expr con_item = le_cs[j];
                                closure_item = closure_item && (item.arg(0) <= con_item.arg(1) + (k-1)*c);
                        }
                }
        }

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

        for (int i=0; i<ge_gamma_cs.size(); i++) {
                z3::expr item = ge_gamma_cs[i];
                int c = get_numeral(item.arg(1).arg(1));
                if (c > 0) {
                        for (int j=0; j<ge_cs.size();j++) {
                                z3::expr con_item = ge_cs[j];
                                closure_item = closure_item && (item.arg(0) >= con_item.arg(1) + (k-1)*c);
                        }
                        for (int j=0; j<ge_xi_cs.size();j++) {
                                z3::expr con_item = ge_cs[j];
                                closure_item = closure_item && (item.arg(0) >= con_item.arg(1) + (k-1)*c);
                        }
                }
        }

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

z3::expr listsolver::pred2abs(z3::expr &atom, int i){
        std::string source = atom.arg(0).to_string();
        std::string new_name = m_ctx.logger().string_format("[%s,%d]", source.c_str(), i);
        std::string k_name = m_ctx.logger().string_format("[k,%d]", i);
        // 1.2 introduce new boolean var
        z3::expr source_bool = z3_ctx().bool_const(new_name.c_str());
        new_bools.push_back(source_bool);
        z3::expr source_int = z3_ctx().int_const(source.c_str());

        z3::expr atom_f(z3_ctx());
        if (atom.decl().name().str() == "pto") {
                // 1.3 pto atom
                atom_f = (source_bool && source_int > 0);
        } else {
                std::string pred_name = atom.decl().name().str();
                int index = index_of_pred(pred_name);
                predicate pred = m_ctx.get_pred(index);
                int idx = pred.idx_E_gamma();

                // 1.3 predicate atom
                int size = atom.num_args();
                std::string dest = atom.arg(size/2).to_string();
                z3::expr dest_int = z3_ctx().int_const(dest.c_str());

                // supposing atom is empty
                z3::expr or_1(z3_ctx());
                or_1 = !source_bool && (source_int == dest_int);
                for (int j=1; j<size/2;j++) {
                        if (atom.arg(j).get_sort().sort_kind() == Z3_UNINTERPRETED_SORT) {
                                z3::expr arg_j_int = z3_ctx().int_const(atom.arg(j).to_string().c_str());
                                z3::expr arg_j2_int = z3_ctx().int_const(atom.arg(j+size/2).to_string().c_str());
                                or_1 = or_1 && (arg_j_int == arg_j2_int);
                        } else {
                                or_1 = or_1 && (atom.arg(j)==atom.arg(j+size/2));
                        }
                }

                // supposing atom is not emtpy
                if (idx != -1) {
                        // E occurs in gamma TODO

                } else {
                        // E does not occur in gamma TODO

                }
                z3::expr or_2(z3_ctx());
                or_2 = source_bool && source_int>0;

                // 1.4 substitute formal args by actual args

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
