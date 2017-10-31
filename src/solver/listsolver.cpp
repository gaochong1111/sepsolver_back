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
                if (pred.is_tree()) {
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
        // compute_all_phi_p();
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

z3::expr listsolver::pred2abs(z3::expr &atom, int i){
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
