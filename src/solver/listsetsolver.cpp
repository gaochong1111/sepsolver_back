#include "listsetsolver.h"
#include <climits>
#include <fstream>

/**
 *###################### listsetsolver ####################################
 */
/**
 * check whether all predicate definitions are corresponding to userdef constraints
 */
void listsetsolver::check_preds() {
        for (int i=0; i<m_ctx.pred_size(); i++) {
        }
}

/**
 * check sat, negf in m_ctx
 * or check entl, negf |= posf
 * @return z3::check_result
 */
z3::check_result listsetsolver::check_sat() {
        std::cout << "listsetsolver: \n";
        logger() << "formula: " << m_ctx.get_negf() << std::endl;

        compute_all_tr_closure();

        z3::expr data(z3_ctx());
        z3::expr space(z3_ctx());
        z3::expr formula = m_ctx.get_negf();

        get_data_space(formula, data, space);

        // std::cout << "data: " << data << std::endl;
        // std::cout << "space: " << space << std::endl;


        return z3::sat;
}



/**
 * check sat, negf in m_ctx
 * or check entl, negf |= posf
 * @return z3::check_result
 */
z3::check_result listsetsolver::check_entl() {
        // TODO ....
        return z3::sat;
}


/**
 * atom in formula to abstraction
 * @param  atom [the atom in formula, like p(Z1, mu; Z2, nu, chi) or (pto Z (*))]
 * @param  i    [the index in formula]
 * @param new_bools [new bool vars]
 * @return      [the abstraction]
 */
z3::expr listsetsolver::pred2abs(z3::expr &atom, int i, z3::expr_vector& new_bools){
        // TODO ..

        return z3_ctx().bool_val(true);
}


/**
 * compute all predicate tr closure
 *
 */
void listsetsolver::compute_all_tr_closure() {
        std::cout << "compute all tr closure\n";
        // std::cout << "pred size: " << m_ctx.pred_size() << std::endl;
        for (int i=0; i<m_ctx.pred_size(); i++) {
                logger() << "compute predicate " << i << std::endl;
                predicate pred = m_ctx.get_pred(i);
                // 1. compute data closure (lfp)
                z3::expr phi_pd_abs = compute_tr_closure(pred);
                logger() << "compute data closure: " << phi_pd_abs << std::endl;
                delta_ge1_predicates.push_back(phi_pd_abs);
        }
}


/**
 * compute predicate data closure
 * @param pred: predicate
 * @return phi_pd : data closure
 */
z3::expr listsetsolver::compute_tr_closure(predicate &pred) {

        z3::expr delta = pred.get_rule(0).get_data();
        int st_size = pred.size_of_static_parameters();
        int size = pred.get_pars().size();
        pred_rule rule = pred.get_rule(0);
        z3::expr rec_app = rule.get_rec_apps()[0];

        z3::expr_vector src_pars(z3_ctx());
        z3::expr_vector dst_pars(z3_ctx());
        for (int i=0; i<size/2; i++) {
                src_pars.push_back(rec_app.arg(i));
                dst_pars.push_back(rec_app.arg(i+size/2));
        }
        delta = delta.substitute(src_pars, dst_pars); // delta = phi_r1 && phi_r2
        std::cout << "phi_r: " << delta << std::endl;

        // 1. get strt(delta)
        z3::expr strt_phi_r2 = z3_ctx().bool_val(true);
        z3::expr_vector set_vars(z3_ctx());
        z3::expr_vector phi_r2_items(z3_ctx());
        int case_i = get_strt(delta, strt_phi_r2, set_vars, phi_r2_items);

        if (strt_phi_r2.to_string() == "false") {
                std::cout << "strt_phi_r2 is false\n";
                return z3_ctx().bool_val(false);
        }

        std::cout << "strt_phi_r2: " << strt_phi_r2 << std::endl;
        std::cout << "case_i: " << case_i << std::endl;
        std::cout << "set_vars: " << set_vars << std::endl;
        // 2. case by case tr
        z3::expr phi_r1 = delta.arg(0);
        std::cout << "phi_r1: " << phi_r1 << std::endl;

        z3::expr phi_pd = z3_ctx().bool_val(true);

        phi_pd = compute_tr_by_case(case_i, phi_r1, strt_phi_r2, phi_r2_items, set_vars);

        std::cout << "TR: " << phi_pd << std::endl;

        return phi_pd;
}

/**
 * compute tr closure case by case
 * @param case_i : [-1, 0, 1, 2, 3, 4]
 * @param phi_r1 : S1 = S2 union {min(S1)}
 * @param strt_phi_r2 : phi_r2
 * @param setvars : S1, S2
 */
z3::expr listsetsolver::compute_tr_by_case(int case_i, z3::expr &phi_r1, z3::expr &strt_phi_r2, z3::expr_vector& phi_r2_items, z3::expr_vector &set_vars) {

        z3::expr phi_pd = z3_ctx().bool_val(true);


        z3::expr emptyset = expr_tool::mk_emptyset(z3_ctx());


        if (case_i == -1) {
                // S1 = S2
                phi_pd = phi_r1 && strt_phi_r2;
        } else if (case_i < 2) {
                // S2 is possible empty

                z3::expr E_S = expr_tool::mk_set_var(z3_ctx(), "E_S");
                z3::expr_vector pars(z3_ctx());
                pars.push_back(E_S);
                // substitute
                z3::expr_vector src(z3_ctx());
                z3::expr_vector dst(z3_ctx());
                src.push_back(set_vars[0]);
                dst.push_back(E_S);
                z3::expr tr_f = phi_r1.substitute(src, dst); // phi_r1[E_S/S]

                tr_f = tr_f && strt_phi_r2; // phi_r2
                tr_f = tr_f && strt_phi_r2.substitute(src, dst); // phi_r2[E_S/S]
                tr_f = tr_f && (set_vars[0] != emptyset); // S != \empty
                tr_f = tr_f && expr_tool::mk_binary_bool(z3_ctx(), "subset", E_S, set_vars[0]); // E_S \subset S

                z3::expr minus_set = expr_tool::mk_binary_set(z3_ctx(), "setminus", set_vars[0], E_S);
                z3::expr pre_f = (minus_set != emptyset);
                z3::expr exp1(z3_ctx());
                z3::expr exp2(z3_ctx());
                if (case_i == 0) {
                        // S1 = S2 union {min(S1)} , S2 possible empty
                        exp1 = minus_set;
                        exp2 = E_S;
                } else {
                        // S1 = S2 union {max(S1)}, S2 possible empty
                        exp1 = E_S;
                        exp2 = minus_set;
                }

                z3::expr pos_f = expr_tool::mk_min_max(z3_ctx(), 1, exp1) < expr_tool::mk_min_max(z3_ctx(), 0, exp2);
                z3::expr imply_f = z3::implies(pre_f, pos_f); // S\E_S != \empty && E_S != \empty -> max(S\E_S)<min(E_S)
                tr_f = tr_f && imply_f;
                phi_pd = (set_vars[0] == set_vars[1]) ||  z3::exists(pars, tr_f); // S1=S2 || exists

        } else if (case_i < 4) {
                // S1 = S2 union {min(S1)}, S2 surely empty
                z3::expr E_S1 = expr_tool::mk_set_var(z3_ctx(), "E_S1");
                z3::expr E_S2 = expr_tool::mk_set_var(z3_ctx(), "E_S2");
                z3::expr_vector pars(z3_ctx());
                pars.push_back(E_S1);
                pars.push_back(E_S2);

                phi_pd = (set_vars[0] == set_vars[1]); // S1 = S2
                phi_pd = phi_pd && (phi_r1 && strt_phi_r2); // phi_r

                z3::expr_vector src(z3_ctx());
                z3::expr_vector dst(z3_ctx());
                src.push_back(set_vars[1]);
                dst.push_back(E_S1);
                z3::expr tr_f = phi_r1.substitute(src, dst); // phi_r1[E_S1/S2]

                z3::expr_vector src1(z3_ctx());
                z3::expr_vector dst1(z3_ctx());
                src1.push_back(set_vars[0]);
                dst1.push_back(E_S2);
                tr_f = tr_f && phi_r1.substitute(src1, dst1); // phi_r1[E_S2/S1]

                tr_f = tr_f && expr_tool::mk_binary_bool(z3_ctx(), "subset", E_S2, E_S1); // E_S2 \subset E_S1
                tr_f = tr_f && (set_vars[1] != emptyset); // S2 != \empty

                z3::expr minus_set = expr_tool::mk_binary_set(z3_ctx(), "setminus", E_S1, E_S2);
                z3::expr pre_f = (minus_set != emptyset);

                z3::expr exp1(z3_ctx());
                z3::expr exp2(z3_ctx());

                z3::expr item(z3_ctx());

                z3::expr item_set(z3_ctx());
                z3::expr_vector src3(z3_ctx());
                z3::expr all_body(z3_ctx());



                z3::expr phi_r2_01 = phi_r2_items[0]; // min(S1) min(S2)
                z3::expr phi_r2_23 = phi_r2_items[5]; // max(S1) max(S2)

                if (case_i == 2) {
                        // S1 = S2 union {min(S1)} , S2 surely nonempty
                        exp1 = minus_set;
                        exp2 = E_S2;

                        // item
                        item = (phi_r2_01.substitute(src, dst)) &&  (phi_r2_01.substitute(src1, dst1));

                        // {min(S2)}
                        item_set = expr_tool::mk_single_set(z3_ctx(), expr_tool::mk_min_max(z3_ctx(), 0, set_vars[1]));

                        // src3(min(S1), min(S2))
                        src3.push_back(expr_tool::mk_min_max(z3_ctx(), 0, set_vars[0]));
                        src3.push_back(expr_tool::mk_min_max(z3_ctx(), 0, set_vars[1]));

                        all_body = phi_r2_01;


                } else {
                        // S1 = S2 union {max(S1)}, S2 surely nonempty
                        exp1 = E_S2;
                        exp2 = minus_set;

                        // item
                        item = (phi_r2_23.substitute(src, dst)) &&  (phi_r2_23.substitute(src1, dst1));

                        // {max(S2)}
                        item_set = expr_tool::mk_single_set(z3_ctx(), expr_tool::mk_min_max(z3_ctx(), 1, set_vars[1]));

                        // src3(max(S1), max(S2))
                        src3.push_back(expr_tool::mk_min_max(z3_ctx(), 1, set_vars[0]));
                        src3.push_back(expr_tool::mk_min_max(z3_ctx(), 1, set_vars[1]));

                        all_body = phi_r2_23;

                }

                z3::expr pos_f = expr_tool::mk_min_max(z3_ctx(), 1, exp1) < expr_tool::mk_min_max(z3_ctx(), 0, exp2);

                z3::expr imply_f = z3::implies(pre_f, pos_f);

                tr_f = tr_f && imply_f; // E_S1\E_S2 != \empty -> max() < min

                /*

                z3::expr phi_r2_01 = phi_r2_items[0]; // min(S1) min(S2)

                // tr_f = tr_f && (phi_r2_01.substitute(src, dst));
                // tr_f = tr_f && (phi_r2_01.substitute(src1, dst1));

                z3::expr phi_r2_23 = phi_r2_items[5]; // max(S1) max(S2)

                if (case_i == 2) {
                        item = (phi_r2_01.substitute(src, dst)) &&  (phi_r2_01.substitute(src1, dst1));
                } else {
                        item = (phi_r2_23.substitute(src, dst)) &&  (phi_r2_23.substitute(src1, dst1));
                }
                */
                tr_f = tr_f && item;

                z3::expr phi_r2_02 = phi_r2_items[1]; // min(S1) max(S1)
                tr_f = tr_f && phi_r2_02; // ?
                tr_f = tr_f && phi_r2_02.substitute(src1, dst1);

                z3::expr phi_r2_13 = phi_r2_items[4]; // min(S2) max(S2)
                tr_f = tr_f && phi_r2_13; // ?
                tr_f = tr_f && phi_r2_13.substitute(src, dst);


                z3::expr_vector pars1(z3_ctx());
                z3::expr_vector pars2(z3_ctx());
                z3::expr x = z3_ctx().int_const("x");
                z3::expr y = z3_ctx().int_const("y");
                z3::expr z = z3_ctx().int_const("z");
                pars1.push_back(x);
                pars1.push_back(y);
                pars2.push_back(z);

                z3::expr set_u = expr_tool::mk_binary_set(z3_ctx(), "setunion", minus_set, item_set);// E_S1\E_S2 \union {min(S1)}
                z3::expr succ_f = expr_tool::mk_belongsto(z3_ctx(), x, set_u);
                succ_f = succ_f && expr_tool::mk_belongsto(z3_ctx(), y, set_u);
                z3::expr all2_f = z3::implies(expr_tool::mk_belongsto(z3_ctx(), z, set_u), ((z <= x) || (y <= z)) );
                // x \in set_u && y \in set_u && forall(z). (z \in set_u -> z<=x && y<=z)
                succ_f = succ_f && z3::forall(pars2, all2_f);

                z3::expr all1_f = z3::implies(succ_f, all_body.substitute(src3, pars1));

                tr_f = tr_f && z3::forall(pars1, all1_f);

                phi_pd = phi_pd && tr_f;

        }

        return phi_pd;
}

/**
 * saturated of phi_r
 * @param phi_r
 * @param strt_phi_r2 : strt(phi_r2)
 * @param set_vars : S1, S2
 * @return int : case i [-1(S1=S2), 0, 1, 2, 3]
 */
int listsetsolver::get_strt(z3::expr phi_r, z3::expr& strt_phi_r2, z3::expr_vector& set_vars,  z3::expr_vector& phi_r2_items) {
        std::cout << "get strt \n";
        z3::expr phi_r1 = phi_r.arg(0);
        // z3::expr_vector set_vars(z3_ctx()); // S1, S2
        set_vars.push_back(phi_r1.arg(0));


        int case_i = 0; // case index
        int matrix[4][4]; // 0: min(set_vars[0]), 1: min(set_vars[1]), 2:max(set_vars[0]), 3:max(set_vars[1])

        // init
        for (int i=0; i<4; i++) {
                for (int j=0; j<4; j++) {
                        matrix[i][j] = INT_MAX;
                }
        }

        z3::expr term_s(z3_ctx());
        if (phi_r1.arg(1).is_const())  {
                set_vars.push_back(phi_r1.arg(1));
                // min(S1) = min(S2) max(S1)=max(S2)
                matrix[0][1] = 0;
                matrix[1][0] = 0;
                matrix[2][3] = 0;
                matrix[3][2] = 0;
                case_i = -1; // S1 = S2

        } else {
                set_vars.push_back(phi_r1.arg(1).arg(0));
                term_s = phi_r1.arg(1).arg(1).arg(0);
                if (expr_tool::is_fun(term_s, "max")) {
                        case_i = 1;
                }
        }

        bool has_s2 = false;
        bool has_s1 = false;
        // add phi_r2
        for (int i=1; i<phi_r.num_args(); i++) {
                z3::expr phi_r2_i = phi_r.arg(i);
                if (phi_r2_i.is_app()) {
                        int c = 0; // c is constant
                        z3::expr item1 = phi_r2_i.arg(0);
                        z3::expr item2 = phi_r2_i.arg(1);

                        if (item2.is_app()) {
                                if (expr_tool::is_fun(item2, "+")) {
                                        c = item2.arg(1).get_numeral_int();
                                        item2 = item2.arg(0);
                                } else if (expr_tool::is_fun(item2, "-")) {
                                        c = -item2.arg(1).get_numeral_int();
                                        item2 = item2.arg(0);
                                }
                        }

                        int row = get_card(item1, set_vars);
                        int col = get_card(item2, set_vars);

                        if (((row|col)&1) == 1) has_s2 = true;
                        else has_s1 = true;

                        if(expr_tool::is_fun(phi_r2_i, "=")) {
                                set_matrix(matrix, row, col, c);
                                set_matrix(matrix, col, row, -c);
                        } else if (expr_tool::is_fun(phi_r2_i, "<")) {
                                set_matrix(matrix, row, col, c-1);
                        } else if (expr_tool::is_fun(phi_r2_i, ">")) {
                                set_matrix(matrix, col, row,-(c+1));
                        } else if (expr_tool::is_fun(phi_r2_i, "<=")) {
                                set_matrix(matrix, row, col, c);
                        } else if (expr_tool::is_fun(phi_r2_i, ">=")) {
                                set_matrix(matrix, col, row, -c);
                        }
                }
        }


        if (has_s1)
                // add min(S1) <= max(S2)
                set_matrix(matrix, 0, 2, 0);
        // add if has_s2
        if (has_s2) {
                // min(S2) <= max(S2)
                set_matrix(matrix, 1, 3, 0);

                if (case_i != -1)
                        case_i += 2;
                // add by term_s
                if (Z3_ast(term_s) != 0) {
                        if (expr_tool::is_fun(term_s, "min")) {
                                // add max(S1) == max(S2)
                                set_matrix(matrix, 2, 3, 0);
                                set_matrix(matrix, 3, 2, 0);
                        } else {
                                // add min(S1) == min(S2)
                                set_matrix(matrix, 0, 1, 0);
                                set_matrix(matrix, 1, 0, 0);
                        }
                }
        }


        // display(matrix, set_vars, "phi_r.dot");

        // compute strt(phi_r)
        bool is_sat = floyd(matrix);

        if (is_sat) {

                z3::expr phi_01 = get_ij_expr(matrix, 0, 1, set_vars); // min(S1) min(S2)
                z3::expr phi_02 = get_ij_expr(matrix, 0, 2, set_vars); // min(S1) max(S1)
                z3::expr phi_03 = get_ij_expr(matrix, 0, 3, set_vars); // min(S1) max(S2)
                z3::expr phi_12 = get_ij_expr(matrix, 1, 2, set_vars); // min(S2) max(S1)
                z3::expr phi_13 = get_ij_expr(matrix, 1, 3, set_vars); // min(S2) max(S2)
                z3::expr phi_23 = get_ij_expr(matrix, 2, 3, set_vars); // max(S1) max(S2)

                phi_r2_items.push_back(phi_01);
                phi_r2_items.push_back(phi_02);
                phi_r2_items.push_back(phi_03);
                phi_r2_items.push_back(phi_12);
                phi_r2_items.push_back(phi_13);
                phi_r2_items.push_back(phi_23);

                std::cout << "phi_01: " << phi_01 << std::endl;
                std::cout << "phi_02: " << phi_02 << std::endl;
                std::cout << "phi_03: " << phi_03 << std::endl;
                std::cout << "phi_12: " << phi_12 << std::endl;
                std::cout << "phi_13: " << phi_13 << std::endl;
                std::cout << "phi_23: " << phi_23 << std::endl;



                strt_phi_r2 = (phi_01) && (phi_02) && phi_03 && phi_12 && phi_13 && phi_23;

                /*
                  for (int i=0; i<4; i++) {
                  for (int j=0; j<4; j++) {
                  if (i!=j && matrix[i][j] != INT_MAX) {
                  strt_phi_r2 = strt_phi_r2 && (get_card(i, set_vars) <= get_card(j, set_vars) + z3_ctx().int_val(matrix[i][j]));
                  }
                  }
                  }
                */
                // strt_phi_r = phi_r1 && strt_phi_r2;
        } else {
                strt_phi_r2 =  z3_ctx().bool_val(false);
        }



        // display(matrix, set_vars, "str_phi_r.dot");
        return case_i;
}

/**
 * get phi_ij
 * @param i: 0, 1
 * @param j: 0, 1
 * @set_vars : S1, S2
 * @return matrix[i][j] && matrix[j][i]
 */
z3::expr listsetsolver::get_ij_expr(int (*matrix)[4], int i, int j, z3::expr_vector &set_vars) {
        z3::expr phi_ij = z3_ctx().bool_val(true);
        if (i!=j) {
                if (matrix[i][j] != INT_MAX) {
                        phi_ij = phi_ij && (get_card(i, set_vars) <= get_card(j, set_vars) + z3_ctx().int_val(matrix[i][j]));
                }
                if (matrix[j][i] != INT_MAX) {
                        phi_ij = phi_ij && (get_card(j, set_vars) <= get_card(i, set_vars) + z3_ctx().int_val(matrix[j][i]));
                }
        }
        return phi_ij;
}

/**
 * get item in matrix index
 * @param: item : min(S)
 * @param: set_vars : S1, S2
 * @return index
 */
int listsetsolver::get_card(z3::expr item, z3::expr_vector &set_vars) {
        int index = 0;
        if (expr_tool::is_fun(item, "max")) {
                index += 2;
        }

        if (item.arg(0).hash() == set_vars[1].hash()) {
                index += 1;
        }

        return index;
}

/**
 * get item of index
 * @param i : index, 0, 1, 2, 3
 * @param set_vars : S1, S2
 * @return expr
 */
z3::expr listsetsolver::get_card(int i, z3::expr_vector &set_vars) {
        return expr_tool::mk_min_max(z3_ctx(), (i>>1)&1, set_vars[i&1]);
}

/**
 * set matrix[i][j] = val
 * @param matrix
 * @param (i, j)
 * @param val
 */
void listsetsolver::set_matrix(int (&matrix)[4][4], int i, int j, int val) {
        if (matrix[i][j] > val) {
                matrix[i][j] = val;
        }
}



/**
 * compute saturation use by floyd method
 * @param matrix : the matrix representation
 * @return false, if has negative cycle
 */
bool listsetsolver::floyd(int (&matrix)[4][4]) {

        std::cout << "floyd.\n";
        int path[4][4];
        int dist[4][4];

        // init path and dist
        for (int i=0; i<4; i++) {
                for (int j=0; j<4; j++){
                        path[i][j] = j;
                        dist[i][j] = matrix[i][j];
                }
        }


        // compute the shortest path
        int tmp;
        for (int i=0; i<4; i++) {
                for (int row=0; row<4; row++) {
                        for (int col=0; col<4; col++) {
                                tmp = (dist[row][i] == INT_MAX || dist[i][col]==INT_MAX)? INT_MAX : dist[row][i] + dist[i][col];
                                if (dist[row][col] > tmp) {
                                        dist[row][col] = tmp;
                                        path[row][col] = path[row][i];
                                }
                        }
                }
        }

        // check whether negative cycle exists or not
        for (int i=0; i<4; i++) {
                for (int row=0; row<4; row++) {
                        for (int col=0; col<4; col++) {
                                tmp = (dist[row][i] == INT_MAX || dist[i][col]==INT_MAX)? INT_MAX : dist[row][i] + dist[i][col];
                                if (dist[row][col] > tmp) {
                                        return false;
                                }
                        }
                }
        }




        for (int i=0; i<4; i++) {
                for (int j=0; j<4; j++){
                        matrix[i][j] = dist[i][j];
                }
        }
        return true;
}

/**
 * diplay matrix in file
 */
void listsetsolver::display(int (*matrix)[4], z3::expr_vector& set_vars, std::string file_name) {
        std::ofstream out(file_name);

        out << "digraph g {\n";

        out << "node_0 [label=\"min("<< set_vars[0] <<")\"];\n";
        out << "node_1 [label=\"min("<< set_vars[1] <<")\"];\n";
        out << "node_2 [label=\"max("<< set_vars[0] <<")\"];\n";
        out << "node_3 [label=\"max("<< set_vars[1] <<")\"];\n";



        for (int i=0; i<4; i++) {
                for (int j=0; j<4; j++) {
                        // if (i==j) continue;
                        if (matrix[i][j] == INT_MAX) {
                                //out << "node_"<< i << "->" << "node_" << j
                                //    <<"[label=\"" << "INF" <<"\"];"<< std::endl;
                        } else {
                                out << "node_"<< i << "->" << "node_" << j
                                    <<"[label=\"" << matrix[i][j] <<"\"];"<< std::endl;
                        }
                }
        }

        out << "}\n";

        out.close();
}


void listsetsolver::display(int matrix[4][4]) {
        for (int i=0; i<4; i++) {
                for (int j=0; j<4; j++) {
                        if (matrix[i][j] == INT_MAX) std::cout << "INF";
                        else std::cout << matrix[i][j];
                        std::cout << "\t";

                }
                std::cout << "\n";
        }
        std::cout << "\n";
}
