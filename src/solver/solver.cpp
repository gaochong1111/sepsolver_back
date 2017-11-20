#include "solver.h"
#include <sys/time.h>


/**
 *###################### solver ####################################3
 */
void solver::solve() {
    // 1. check_preds
    check_preds();
    struct timeval tvBegin, tvEnd, tvDiff;
    // 2. start timer
    gettimeofday (&tvBegin, NULL);

    // 3. check sat or entl
    if (m_ctx.is_sat()) {
        std::cout << "Checking satisfiability.\n";
        z3::check_result result = check_sat();
        std::cout << "The result: " << result << std::endl;
    } else {
        std::cout << "Checking entailment.\n";
        z3::check_result result = check_entl();
        std::cout << "The result: " << result << std::endl;
    }
    // 4. end timers
    gettimeofday (&tvEnd, NULL);
    long int diff = (tvEnd.tv_usec + 1000000 * tvEnd.tv_sec)
        - (tvBegin.tv_usec + 1000000 * tvBegin.tv_sec);
    tvDiff.tv_sec = diff / 1000000;
    tvDiff.tv_usec = diff % 1000000;
    std::string info = logger().string_format("\nTotal time (sec): %ld.%06ld\n\n", tvDiff.tv_sec, tvDiff.tv_usec);
    std::cout << info;
}


z3::model solver::get_model() {
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
z3::expr solver::get_interp(z3::model &m, z3::expr exp) {

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
 * get data and space part by formula
 * @param formula : the formula
 * @param data : the result data part (translate to abstraction)
 * @param space : the result space part
 */
void solver::get_data_space(z3::expr &formula, z3::expr &data, z3::expr &space) {
    int i=0;

    if (formula.decl().name().str() == "tobool") {
        // only space part
        data = z3_ctx().bool_val(true);
        space = formula;
    } else {
        // data and space
        z3::expr_vector data_items(z3_ctx());
        for (; i<formula.num_args(); i++) {
            if (formula.arg(i).is_app() && formula.arg(i).decl().name().str() == "tobool") {
                break;
            }
            // (= Z1 Z2) or (distinct Z1 Z2) ==> abs
            if (formula.arg(i).num_args()==2 && formula.arg(i).arg(0).get_sort().sort_kind() == Z3_UNINTERPRETED_SORT) {
                z3::expr item = formula.arg(i);
                z3::expr z1_int = z3_ctx().int_const(item.arg(0).to_string().c_str());
                z3::expr z2_int = z3_ctx().int_const(item.arg(1).to_string().c_str());
                if (item.decl().name().str() == "distinct") {
                    data_items.push_back(z1_int != z2_int);
                } else {
                    data_items.push_back(z1_int == z2_int);
                }
            } else {
                data_items.push_back(formula.arg(i));
            }
        }
        //
        if (data_items.size() > 0) {
            data = mk_and(data_items);
        } else {
            data = z3_ctx().bool_val(true);
        }

        if (i != formula.num_args()) {
            space = formula.arg(i);
        }
    }

    if (space.decl().name().str() == "tobool") {
        if (space.arg(0).decl().name().str() == "ssep") space = space.arg(0);
    }
}

/**
 * index of the predicate in preds
 * @param: pred_name : the predicate name
 * @return: the index, if exist
 *          -1       , otherwise
 */
int solver::index_of_pred(std::string &pred_name) {
    for (int i=0; i<m_ctx.pred_size(); i++) {
        if (pred_name == m_ctx.get_pred(i).get_pred_name()) {
            return i;
        }
    }
    return -1;
}

/**
 * compute abstraction of space part
 * @param space : the space part
 * @param new_bools : new bools var
 * @return the abstraction of space part
 */
z3::expr solver::abs_space(z3::expr &space, z3::expr_vector& new_bools) {
    // 1.space atoms -> abs (\phi_sigma)
    z3::expr f_abs(z3_ctx());
    for (int i=0; i<space.num_args(); i++) {
        //1.1 fetch atom
        z3::expr atom = space.arg(i);

        z3::expr atom_f = pred2abs(atom, i, new_bools);

        // 1.5 add atom_f to f_abs
        if (Z3_ast(f_abs) == 0) {
            f_abs = atom_f;
        } else {
            f_abs = f_abs && atom_f;
        }
    }

    return f_abs;
}


/**
 * compute phi_star by new_bools
 * @param new_bools : new bool vars
 * @return the phi_star
 */
z3::expr solver::abs_phi_star(z3::expr_vector& new_bools) {
    z3::expr phi_star = z3_ctx().bool_val(true);
    // phi_star
    for (int i=0; i<new_bools.size(); i++) {
        for (int j=i+1; j<new_bools.size(); j++) {
            std::string b1_name = new_bools[i].to_string();
            std::string b2_name = new_bools[j].to_string();
            int i1 = b1_name.find(",");
            int i2 = b2_name.find(",");
            std::string z1_name = b1_name.substr(2, i1-2);
            std::string z1_i = b1_name.substr(i1+1, b1_name.length()-i1-3);
            std::string z2_name = b2_name.substr(2, i2-2);
            std::string z2_i = b2_name.substr(i2+1, b2_name.length()-i2-3);

            if (z1_i != z2_i) {
                // add imply atom
                z3::expr imply = implies((z3_ctx().int_const(z1_name.c_str()) == z3_ctx().int_const(z2_name.c_str()) && new_bools[i]), !new_bools[j]);
                // if (Z3_ast(phi_star) == 0) {
                //    phi_star = imply;
                // } else {
                phi_star = phi_star && imply;
                //}
            }
        }
    }
    return phi_star;
}
