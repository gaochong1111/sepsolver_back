#include "listsetsolver.h"
#include <climits>
#include <fstream>

#include "qgdbs_translator.h"
#include "mona_translator.h"
#include "mona_executor.h"

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
 * check data whether contains Tm op 0 and min(S) op c
 * @param data
 * @return true, if no min(S) op c
 */
bool listsetsolver::check_data(z3::expr& data) {
        // 1. check min(S) op c
        // 2. check Tm op 0
        // std::cout << "check data: " << data << std::endl;
        z3::expr_vector items(z3_ctx());
        for (int i=0; i<data.num_args(); i++) {
                z3::expr item = data.arg(i);
                if (item.num_args() == 2) {
                        // Ti op Ti + c
                        if (item.arg(0).num_args() == 2) {
                                // Tm op c
                                m_free_items.push_back(item);
                        } else {
                                // Ti op Ti + c
                                std::string op = item.decl().name().str();
                                z3::expr item1 = item.arg(1);
                                if (item1.num_args() == 2) {
                                        if (!expr_tool::is_constant(item1.arg(1))) {
                                                return false;
                                        }
                                        if (expr_tool::is_fun(item1, "-")) {
                                                if (op == "=") {
                                                        item = item1.arg(0) == item.arg(0) + item1.arg(1);
                                                } else if (op == ">=") {
                                                        item = item1.arg(0) <= item.arg(0) + item1.arg(1);

                                                } else if (op == "<=") {
                                                        item = item1.arg(0) >= item.arg(0) + item1.arg(1);
                                                }
                                        }
                                } else {
                                        if (expr_tool::is_constant(item1)) {
                                                std::string name = item.arg(0).decl().name().str();
                                                if (name == "min" || name == "max") {
                                                        return false;
                                                }
                                        }
                                }
                        }
                }
                items.push_back(item);
        }
        return true;
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

        z3::expr phi_pd = delta_ge1_predicates[0];
        // expr_tool::write_file("tr.smt", phi_pd);

        z3::expr data(z3_ctx());
        z3::expr space(z3_ctx());
        z3::expr formula = m_ctx.get_negf();



        std::set<z3::expr, exprcomp> fo_vars_set;
        std::set<z3::expr, exprcomp> so_vars_set;
        std::set<z3::expr, exprcomp> bool_vars_set;
        // std::cout << "m_formula: " << m_formula << std::endl;

        expr_tool::get_first_order_vars(formula, fo_vars_set);
        expr_tool::get_second_order_vars(formula, so_vars_set);


        get_data_space(formula, data, space);


        // std::cout << "data: " << data << std::endl;
        // std::cout << "space: " << space << std::endl;

        // get abstraction
        z3::expr f_abs = data;

        // check data

        bool is_data = check_data(f_abs);
        if (!is_data) {
                std::cout << "THE DATA FORMULA IS NOT SUPPORTED!\n";
                exit(-1);
        }


        z3::expr space_abs = z3_ctx().bool_val(true);
        z3::expr star_abs = z3_ctx().bool_val(true);
        if (Z3_ast(space) != 0) {
                z3::expr_vector new_bools(z3_ctx());
                space_abs = abs_space(space, new_bools);
                z3::expr b_false = z3_ctx().bool_val(false);
                if (space_abs.hash() == b_false.hash()) {
                        std::cout << "Abstraction of formula is false. \n";
                        return z3::unsat;
                }

                // std::cout << "new bool: " << new_bools << std::endl;
                star_abs = abs_phi_star(new_bools);
                // std::cout << "star_abs: " << star_abs << std::endl;
        }

        // std::cout << "space_abs: " << space_abs << std::endl;

        f_abs = f_abs && space_abs && star_abs;

        std::set<z3::expr, exprcomp> fo_vars_set1;
        // get bool vars in model
        expr_tool::get_zero_order_vars(f_abs, bool_vars_set);
        expr_tool::get_first_order_vars(f_abs, fo_vars_set1);

        expr_tool::write_file("f_abs.smt", f_abs);

        std::set<z3::expr, exprcomp> mm_items;
        expr_tool::get_min_max_items(f_abs, mm_items);
        if (mm_items.size() > 0) {
                std::cout << "substitute .....\n";
                z3::expr_vector srcs(z3_ctx());
                z3::expr_vector dsts(z3_ctx());
                z3::expr_vector and_items(z3_ctx());
                int idx=0;
                for (auto item : mm_items) {
                        std::string name = logger().string_format("GE_%d", idx);
                        z3::expr ge_i = expr_tool::mk_set_var(z3_ctx(), name);

                        srcs.push_back(item);
                        dsts.push_back(ge_i);
                        and_items.push_back(ge_i == item);

                }
                z3::expr add_item = z3::mk_and(and_items);
                f_abs = f_abs.substitute(srcs, dsts);
                f_abs = f_abs && add_item;
                // f_abs = !z3::forall(dsts, !f_abs);

                expr_tool::write_file("f_abs.smt", f_abs);

        }

        if (m_free_items.size() == 0) {
                // simple case

                mona_translator mona_tl(z3_ctx(), f_abs);

                mona_tl.write_to_file("test.mona");
                std::map<std::string, std::string> model;
                mona_executor mona_exe;
                mona_exe.set_args("-q");
                mona_exe.set_name("test.mona");
                std::cout << "execute mona -q test.mona\n";
                bool is_sat = mona_exe.execute(model);
                // std::cout << "sat: " << is_sat << std::endl;

                if (is_sat)
                        display_model(bool_vars_set, fo_vars_set1, so_vars_set, model);
                else {
                        return z3::unsat;
                }
        } else {
                // complex case
                std::cout << "free_items size: "  << m_free_items.size() << std::endl;
                for (int i=0; i<m_free_items.size(); i++) {
                        std::cout << m_free_items[i] << std::endl;
                }
                int MAX_CTX = 1 << m_free_items.size();
                int ctx = 0;
                z3::expr_vector src(z3_ctx());

                for (int i=0; i<m_free_items.size(); i++) {
                        src.push_back(m_free_items[i]);
                }

                while(ctx < MAX_CTX) {
                        z3::expr_vector dst(z3_ctx());
                        z3::expr_vector phi_count_items(z3_ctx());

                        for (int i=0; i<m_free_items.size(); i++) {
                                if((ctx & (1<<i))) {
                                        // true
                                        dst.push_back(z3_ctx().bool_val(true));
                                        phi_count_items.push_back(m_free_items[i]);
                                } else {
                                        dst.push_back(z3_ctx().bool_val(false));
                                        phi_count_items.push_back(!m_free_items[i]);
                                }
                        }
                        ctx++;

                        z3::expr phi_core = f_abs.substitute(src, dst);
                        z3::expr phi_count = z3::mk_and(phi_count_items);

                        // 1. phi_core --> dfa
                        mona_translator mona_tl(z3_ctx(), phi_core);

                        mona_tl.write_to_file("phi_core.mona");
                        std::map<std::string, std::string> model;
                        mona_executor mona_exe;
                        mona_exe.set_args("-q");
                        mona_exe.set_name("phi_core.mona");
                        bool is_sat = mona_exe.execute(model);
                        if (!is_sat) {
                                continue;
                        } else {
                                mona_exe.set_args("-w -u -q");
                                mona_exe.set_name("phi_core.mona");
                                std::cout << "execute mona -w -u phi_core.mona\n";
                                mona_exe.execute("phi_core.dfa");
                                // construct PA


                                break;
                        }



                        // std::cout << "phi_core: " << phi_core << std::endl;

                        // std::cout << "phi_count: " << phi_count << std::endl;
                }




        }




/*
// translate into N
qgdbs_translator translator(z3_ctx(), f_abs);
std::set<z3::expr, exprcomp> so_vars_set1;
expr_tool::get_second_order_vars(f_abs, so_vars_set1);

translator.set_first_order_vars(fo_vars_set);
translator.set_second_order_vars(so_vars_set1);
translator.prepare();
z3::expr f_ps_qgdbs_n(z3_ctx());
int count = 0;
std::map<std::string, std::string> model;

int total_ctx = 0;
int valid_ctx = 0;



while(translator.get_next()) {

// std::cout << "f_ps_qgdbs_n: " << f_ps_qgdbs_n << std::endl;

translator.print_ctx();
total_ctx++;
// f_ps_qgdbs_n = f_abs;
int skip_flag = false;

for (int i=0; i<m_set_pairs.size(); i++) {

int ctx_1 = translator.get_ctx(m_set_pairs[i].first);
int ctx_2 = translator.get_ctx(m_set_pairs[i].second);
// std::cout << "ctx_1: " << ctx_1 << ", " << ctx_2 << std::endl;
if (ctx_2 != 2 && ctx_2 != ctx_1) {
skip_flag = true;
}
}

std::cout << "skip: " << skip_flag << std::endl;
// continue;

if (!skip_flag) {
valid_ctx++;

translator.translate_formula_ctx(f_ps_qgdbs_n);
// continue;
mona_translator mona_tl(z3_ctx(), f_ps_qgdbs_n);

expr_tool::write_file("f_ps_qgdbs_n.smt", f_ps_qgdbs_n);
mona_tl.write_to_file("test.mona");

mona_executor mona_exe;
mona_exe.set_args("-q");
mona_exe.set_name("test.mona");
std::cout << "execute mona -q test.mona\n";
bool is_sat = mona_exe.execute(model);
// std::cout << "sat: " << is_sat << std::endl;

if (is_sat) {
// translator.print_ctx();
display_model(bool_vars_set, fo_vars_set1, so_vars_set, model);
count ++;
break;
// return z3::sat;
} else {
translator.print_ctx();
}
}

}

std::cout << "total_ctx: " << total_ctx << std::endl;
std::cout << "valid_ctx: " << valid_ctx << std::endl;
std::cout << "sat count: " << count << std::endl;
*/
        return z3::sat;
}


/**
 * display model of f_abs
 * @param bool_vars, fo_vars, so_vars
 * @param model : mona model
 */
void listsetsolver::display_model(std::set<z3::expr, exprcomp> &bool_vars, std::set<z3::expr, exprcomp> &fo_vars, std::set<z3::expr, exprcomp> &so_vars, std::map<std::string, std::string> &model) {
        std::cout << "model: \n";
        std::string key;
        std::string value;
        for (auto b_var : bool_vars) {
                key = expr_tool::get_mona_name(b_var);
                value = model[key];
                std::cout << b_var << " = " << value << std::endl;
        }

        for (auto fo_var : fo_vars) {
                key = fo_var.to_string();

                std::cout << key << " = " << model[key] << std::endl;
        }

        for (auto so_var : so_vars) {
                key = so_var.to_string();

                std::cout << key << " = " << model[key] << std::endl;
        }

        /*
          std::string key_minus;
          std::string key_plus;

          std::string val1;
          std::string val2;
          std::string val;
          for (auto fo_var : fo_vars) {
          key = fo_var.to_string();
          key_minus = key;
          key_minus.append("_minus");
          key_plus = key;
          key_plus.append("_plus");

          val1 = model[key_minus];
          val2 = model[key_plus];

          // std::cout << "val1: " << (val1=="") << std::endl;

          val = merge_model_val(val1, val2);
          std::cout << fo_var << " = " << val << std::endl;
          }

          for (auto so_var : so_vars) {
          key = so_var.to_string();
          key_minus = key;
          key_minus.append("_minus");
          key_plus = key;
          key_plus.append("_plus");

          val1 = model[key_minus];
          val2 = model[key_plus];
          val = merge_model_val(val1, val2);
          std::cout << so_var << " = " << val << std::endl;

          }
        */
        std::cout << std::endl;

}

std::string listsetsolver::merge_model_val(std::string &minus_val, std::string &plus_val) {
        std::string result="";
        if (minus_val.find('{') != -1) {
                result.append("{");
                int index = minus_val.find('{')+1;
                int end = minus_val.find('}');
                if (index < end){
                        result.append(minus_val.substr(index, end-index));
                }
                index = plus_val.find('{')+1;
                end = plus_val.find('}');
                if (index < end) {
                        if (result.length()>1)  result.append(",");
                        result.append(plus_val.substr(index, end-index));
                }

                result.append("}");

        } else {
                if (minus_val == "") {
                        result = plus_val;
                } else if (minus_val == "0") {
                        result = plus_val;
                } else {
                        result = minus_val;
                }
        }
        return result;

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
z3::expr listsetsolver::pred2abs(z3::expr &atom, int i, z3::expr_vector& new_bools) {
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
        if (expr_tool::is_fun(atom, "pto")) {
                // 1.1 pto atom
                atom_f = (source_bool && source_int > 0);
        } else {
                std::string pred_name = atom.decl().name().str();
                int index = index_of_pred(pred_name);
                predicate pred = m_ctx.get_pred(index); // get predicate definition
                int size = atom.num_args() - pred.size_of_static_parameters(); // size of source and destination paramaters
                // 1.2 predicate atom
                // 1.2.1 supposing atom is empty

                z3::expr phi_pd = delta_ge1_predicates[index]; // the predicate data closure
                z3::expr phi_pd_tms = m_pred_tms[index]; // Tm op 0 terms

                z3::expr b_false = z3_ctx().bool_val(false);
                if (phi_pd.hash() == b_false.hash()) return b_false;

                z3::expr_vector args = pred.get_pars();

                z3::expr phi_p = pred.get_phi_p(z3_ctx());
                std::vector<int> sub_r; // sub_r[i]=1 -> alpha_i sub beta_i
                pred.get_subset_relation(sub_r);



                z3::expr_vector gamma_1(z3_ctx()); // new variables
                z3::expr_vector gamma_2(z3_ctx());
                z3::expr_vector gamma_12(z3_ctx());

                z3::expr_vector alpha(z3_ctx());
                z3::expr_vector beta(z3_ctx());

                z3::expr or_0(z3_ctx());
                z3::expr dest_int = z3_ctx().int_const(atom.arg(size/2).to_string().c_str());
                or_0 = !source_bool && (source_int == dest_int);
                for (int j=1; j<size/2;j++) {
                        // compute or_0
                        if (expr_tool::is_location(atom.arg(j))) {
                                z3::expr arg_j_int = z3_ctx().int_const(atom.arg(j).to_string().c_str());
                                z3::expr arg_j2_int = z3_ctx().int_const(atom.arg(j+size/2).to_string().c_str());
                                or_0 = or_0 && (arg_j_int == arg_j2_int);
                        } else {
                                or_0 = or_0 && (atom.arg(j)==atom.arg(j+size/2));

                                // introduce new set vars
                                alpha.push_back(args[j]);
                                beta.push_back(args[j+size/2]);
                                std::string gamma1_name = atom.arg(j).to_string();
                                gamma1_name.append("_1");
                                z3::expr gamma1_j = z3_ctx().constant(gamma1_name.c_str(), atom.arg(j).get_sort());
                                gamma_1.push_back(gamma1_j);

                                std::string gamma2_name = atom.arg(j).to_string();
                                gamma2_name.append("_2");
                                z3::expr gamma2_j = z3_ctx().constant(gamma2_name.c_str(), atom.arg(j).get_sort());
                                gamma_2.push_back(gamma2_j);


                                // set sub pair
                                if (sub_r[j-1] != -1) {


                                        if (sub_r[j-1] == 0) {

                                                // alpha_j supersub beta_j
                                                // m_set_pairs.push_back(std::pair<z3::expr, z3::expr>(atom.arg(j+size/2), atom.arg(j)));
                                                m_set_pairs.push_back(std::pair<z3::expr, z3::expr>(gamma1_j, atom.arg(j)));
                                                m_set_pairs.push_back(std::pair<z3::expr, z3::expr>(gamma2_j, gamma1_j));
                                                m_set_pairs.push_back(std::pair<z3::expr, z3::expr>(atom.arg(j+size/2), gamma2_j));


                                        } else {
                                                // m_set_pairs.push_back(std::pair<z3::expr, z3::expr>(atom.arg(j), atom.arg(j+size/2)));
                                                m_set_pairs.push_back(std::pair<z3::expr, z3::expr>(atom.arg(j), gamma1_j));
                                                m_set_pairs.push_back(std::pair<z3::expr, z3::expr>(gamma1_j, gamma2_j));
                                                m_set_pairs.push_back(std::pair<z3::expr, z3::expr>(gamma2_j, atom.arg(j+size/2)));





                                        }
                                }
                        }
                }

                for (int i=0; i<gamma_1.size(); i++) gamma_12.push_back(gamma_1[i]);
                for (int i=0; i<gamma_2.size(); i++) gamma_12.push_back(gamma_2[i]);

                z3::expr_vector f_args(z3_ctx()); // predicate parameters, formal parameters
                z3::expr_vector a_args(z3_ctx()); // actual parameters

                // init formla parameters and actual parameters
                for (int i=0; i<atom.num_args(); i++) {
                        if (!expr_tool::is_location(atom.arg(i))) {
                                f_args.push_back(args[i]);
                                a_args.push_back(atom.arg(i));
                        }
                }


                // logger() << "or_0: " << or_0 << std::endl;

                // 1.2.2 supposing atom is not emtpy



                // logger() <<"formal pars: " << f_args << std::endl;
                // logger() <<"actual pars: " << a_args << std::endl;

                z3::expr or_1(z3_ctx()); // by ufld_1
                z3::expr or_2(z3_ctx()); // by ufld_ge_2

                int idx = pred.idx_E_gamma(); // check whether E ouccus in gamma
                // logger() << "idx: " << idx << std::endl;

                // std::cout << "phi_p: " << phi_p << std::endl;
                // std::cout << "alpah: " << alpha << std::endl;
                // std::cout << "beta: " << beta << std::endl;

                z3::expr phi_pd_1 = phi_p.substitute(beta, gamma_1);
                z3::expr phi_pd_2 =  phi_p.substitute(f_args, gamma_12);
                z3::expr phi_pd_3 = phi_pd.substitute(alpha, gamma_2);

                // std::cout << "phi_pd_1: " << phi_pd_1 << std::endl;
                // std::cout << "phi_pd_2: " << phi_pd_2 << std::endl;
                // std::cout << "phi_pd_3: " << phi_pd_3 << std::endl;
                z3::expr phi_pd_ge_2 =  phi_pd_1 && phi_pd_2  && phi_pd_3;

                if (idx != -1) {
                        // E occurs in gamma TOCHECK
                        z3::expr E = atom.arg(0);
                        z3::expr beta_idx = atom.arg(size/2+idx+1);
                        z3::expr beta_idx_int = z3_ctx().int_const(beta_idx.to_string().c_str());

                        std::string beta_idx_name = m_ctx.logger().string_format("[%s,%d]", beta_idx.to_string().c_str(), i);
                        z3::expr beta_idx_bool = z3_ctx().bool_const(beta_idx_name.c_str());
                        new_bools.push_back(beta_idx_bool); // new bool var

                        // ufld_1
                        z3::expr ufld_1 = (source_int == beta_idx_int && phi_p);
                        // logger() << "ufld_1: " << ufld_1 << std::endl;
                        or_1 = ((source_bool && source_int>=1 && beta_idx_bool && beta_idx_int>=1) && ufld_1.substitute(f_args, a_args));
                        // logger() << "or_1: " << or_1 << std::endl;
                        // ufld_ge_2
                        z3::expr ufld_ge_2 = (!(source_int == beta_idx_int) && phi_pd_ge_2);

                        or_2 = ((source_bool && source_int>=1 && beta_idx_bool && beta_idx_int>=1) && ufld_ge_2.substitute(f_args, a_args));
                        // logger() << "or_2: " << or_2 << std::endl;
                } else {
                        // E does not occur in gamma
                        // ufld_1
                        z3::expr ufld_1 = phi_p;
                        // std::cout << "ufld_1: " << ufld_1 << std::endl;
                        or_1 =  source_bool && source_int>=1 && ufld_1.substitute(f_args, a_args);
                        // logger() << "or_1: " << or_1 << std::endl;
                        z3::expr ufld_2 = phi_pd_ge_2;
                        or_2 = source_bool && source_int>=1 && ufld_2.substitute(f_args, a_args);
                        // .........................
                        // or_2 = !z3::forall(gamma_12, !or_2);
                        //or_2 = z3_ctx().bool_val(false);
                }

                if (phi_pd_tms.to_string() != "true") {
                        phi_pd_tms = phi_pd_tms.substitute(alpha, gamma_2).substitute(f_args, a_args);
                        for (int i=0; i<phi_pd_tms.num_args(); i++) {
                                m_free_items.push_back(phi_pd_tms.arg(i));
                        }
                }

                // 1.3 or
                atom_f = !(!or_0 && !or_1 && !or_2);

        }
        return atom_f;
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

        z3::expr delta = pred.get_phi_p(z3_ctx()); // delta = phi_r1 && phi_r2
        // std::cout << "phi_r: " << delta << std::endl;

        // 1. get strt(delta)
        z3::expr strt_phi_r2 = z3_ctx().bool_val(true);
        z3::expr_vector set_vars(z3_ctx());
        z3::expr_vector phi_r2_items(z3_ctx());
        int case_i = get_strt(delta, strt_phi_r2, set_vars, phi_r2_items);

        if (strt_phi_r2.to_string() == "false") {
                std::cout << "strt_phi_r2 is false\n";
                return z3_ctx().bool_val(false);
        }

        // std::cout << "strt_phi_r2: " << strt_phi_r2 << std::endl;
        // std::cout << "case_i: " << case_i << std::endl;
        // std::cout << "set_vars: " << set_vars << std::endl;
        // exit(0);
        // 2. case by case tr
        z3::expr phi_r1 = delta.arg(0);
        // std::cout << "phi_r1: " << phi_r1 << std::endl;

        z3::expr phi_pd = z3_ctx().bool_val(true);

        phi_pd = compute_tr_by_case(case_i, phi_r1, strt_phi_r2, phi_r2_items, set_vars);

        expr_tool::write_file("tr.smt", phi_pd);

        // std::cout << "TR: " << phi_pd << std::endl;
        // exit(0);

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

        if (case_i > 5){
                std::cout << "case is not supported!\n";
                exit(-1);
        }


        if (case_i == -1) {
                // S1 = S2
                phi_pd = phi_r1;
        } else if (case_i % 2 == 0) {
                // S2 is possible empty
                if (case_i != 4)
                        phi_pd = compute_tr_by_case_02(case_i, phi_r1, strt_phi_r2, phi_r2_items, set_vars);
                else{
                        phi_pd = compute_tr_by_case4(phi_r1, strt_phi_r2, phi_r2_items, set_vars);
                }
        } else {
                if (case_i != 5) {
                        phi_pd = compute_tr_by_case_13(case_i, phi_r1, strt_phi_r2, phi_r2_items, set_vars);
                } else {
                        phi_pd = compute_tr_by_case5(phi_r1, strt_phi_r2, phi_r2_items, set_vars);
                }
        }
        if (case_i != 5) m_pred_tms.push_back(z3_ctx().bool_val(true)); // pred_tms
        return phi_pd;
}

/**
 * compute tr closure case by case 0 or 2, S2 is possible empty
 * @param case_i : [0, 2]
 * @param phi_r1 : S1 = S2 union {min(S1)} or  S1 = S2 union {max(S1)}
 * @param strt_phi_r2 : phi_r2
 * @param setvars : S1, S2
 */
z3::expr listsetsolver::compute_tr_by_case_02(int case_i, z3::expr &phi_r1, z3::expr &strt_phi_r2, z3::expr_vector &phi_r2_items, z3::expr_vector &set_vars) {
        assert(case_i == 0 || case_i == 2);
        z3::expr phi_pd = z3_ctx().bool_val(true);

        z3::expr emptyset = expr_tool::mk_emptyset(z3_ctx());

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
        tr_f = tr_f && !(set_vars[0] == emptyset); // S != \empty
        tr_f = tr_f && expr_tool::mk_binary_bool(z3_ctx(), "subset", E_S, set_vars[0]); // E_S \subset S

        z3::expr minus_set = expr_tool::mk_binary_set(z3_ctx(), "setminus", set_vars[0], E_S);
        z3::expr pre_f = (!(minus_set == emptyset) && !(E_S == emptyset));
        z3::expr exp1(z3_ctx());
        z3::expr pos_f(z3_ctx());
        z3::expr_vector ex_pars(z3_ctx());
        z3::expr es_x = expr_tool::mk_set_var(z3_ctx(), "ES_X");
        ex_pars.push_back(es_x);
        if (case_i == 0) {
                // S1 = S2 union {min(S1)} , S2 possible empty
                exp1 = es_x == minus_set;
                pos_f = expr_tool::mk_min_max(z3_ctx(), 0, E_S) >= expr_tool::mk_min_max(z3_ctx(), 1, es_x) + 1;

        } else if(case_i == 2){
                // S1 = S2 union {max(S1)}, S2 possible empty
                exp1 = es_x == minus_set;
                pos_f = expr_tool::mk_min_max(z3_ctx(), 0, es_x) >= expr_tool::mk_min_max(z3_ctx(), 1, E_S) + 1;
        } else if (case_i == 4) {
        }
        pos_f = pos_f && exp1;
        pos_f = !z3::forall(ex_pars, !pos_f);

        // z3::expr imply_f = z3::implies(pre_f, pos_f); // S\E_S != \empty && E_S != \empty -> max(S\E_S)<min(E_S)
        z3::expr imply_f = !(pre_f && !pos_f);
        tr_f = tr_f && imply_f;
        phi_pd = !(!(set_vars[0] == set_vars[1]) &&  z3::forall(pars, !tr_f)); // S1=S2 || exists
        return phi_pd;
}


/**
 * compute tr closure case by case 1 or 3, S2 is surely  nonempty
 * @param case_i : [1, 3]
 * @param phi_r1 : S1 = S2 union {min(S1)} or  S1 = S2 union {max(S1)}
 * @param strt_phi_r2 : phi_r2
 * @param setvars : S1, S2
 */
z3::expr listsetsolver::compute_tr_by_case_13(int case_i, z3::expr &phi_r1, z3::expr &strt_phi_r2, z3::expr_vector &phi_r2_items, z3::expr_vector &set_vars) {

        assert(case_i == 1 || case_i == 3);

        z3::expr phi_pd = z3_ctx().bool_val(true);
        z3::expr emptyset = expr_tool::mk_emptyset(z3_ctx());

        // S1 = S2 union {min(S1)}, S2 surely empty
        z3::expr E_S1 = expr_tool::mk_set_var(z3_ctx(), "E_S1");
        z3::expr E_S2 = expr_tool::mk_set_var(z3_ctx(), "E_S2");
        z3::expr_vector pars(z3_ctx());
        pars.push_back(E_S1);
        pars.push_back(E_S2);

        z3::expr or_0 = (set_vars[0] == set_vars[1]); // S1 = S2
        z3::expr or_1 = (phi_r1 && strt_phi_r2); // phi_r


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
        tr_f = tr_f && !(set_vars[1] == emptyset); // S2 != \empty

        z3::expr minus_set = expr_tool::mk_binary_set(z3_ctx(), "setminus", E_S1, E_S2);
        z3::expr pre_f = !(minus_set == emptyset);

        z3::expr exp1(z3_ctx());
        z3::expr exp2(z3_ctx());

        z3::expr item(z3_ctx());

        z3::expr item_set(z3_ctx());
        z3::expr_vector src3(z3_ctx());
        z3::expr all_body(z3_ctx());



        z3::expr phi_r2_01 = phi_r2_items[0]; // min(S1) min(S2)
        z3::expr phi_r2_23 = phi_r2_items[5]; // max(S1) max(S2)

        z3::expr_vector ex_pars(z3_ctx());
        z3::expr pos_f(z3_ctx());
        z3::expr es_x = expr_tool::mk_set_var(z3_ctx(), "ES_X");
        ex_pars.push_back(es_x);
        if (case_i == 1) {
                // S1 = S2 union {min(S1)} , S2 surely nonempty
                exp1 = es_x == minus_set;
                pos_f = expr_tool::mk_min_max(z3_ctx(), 0, E_S2)  >= expr_tool::mk_min_max(z3_ctx(), 1, es_x) + 1;
                // boundary
                item = (phi_r2_01.substitute(src, dst)) &&  (phi_r2_01.substitute(src1, dst1));

                // {min(S2)}
                item_set = expr_tool::mk_single_set(z3_ctx(), expr_tool::mk_min_max(z3_ctx(), 0, E_S2));

                // src3(min(S1), min(S2))
                src3.push_back(expr_tool::mk_min_max(z3_ctx(), 0, set_vars[0]));
                src3.push_back(expr_tool::mk_min_max(z3_ctx(), 0, set_vars[1]));

                all_body = phi_r2_01;


        } else if(case_i == 3){
                // S1 = S2 union {max(S1)}, S2 surely nonempty
                exp1 = es_x == minus_set;
                pos_f = expr_tool::mk_min_max(z3_ctx(), 0, es_x)  >= expr_tool::mk_min_max(z3_ctx(), 1, E_S2) + 1;

                // boundary
                item = (phi_r2_23.substitute(src, dst)) &&  (phi_r2_23.substitute(src1, dst1));



                // {max(S2)}
                item_set = expr_tool::mk_single_set(z3_ctx(), expr_tool::mk_min_max(z3_ctx(), 1, E_S2));

                // src3(max(S1), max(S2))
                src3.push_back(expr_tool::mk_min_max(z3_ctx(), 1, set_vars[1]));
                src3.push_back(expr_tool::mk_min_max(z3_ctx(), 1, set_vars[0]));

                all_body = phi_r2_23;

        }

        pos_f = pos_f && exp1;
        pos_f = !z3::forall(ex_pars, !pos_f);

        //std::cout << "pos_f: " << pos_f << std::endl;


        // std::cout << "pre_f : " << pre_f << std::endl;
        // z3::expr imply_f = z3::implies(pre_f, pos_f);
        z3::expr imply_f = !(pre_f && !pos_f);
        // std::cout << "imply_f : " << imply_f << std::endl;

        // imply_f []
        tr_f = tr_f && imply_f; // E_S1\E_S2 != \empty -> max() < min

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

        z3::expr set_u = expr_tool::mk_binary_set(z3_ctx(), "setunion", minus_set, item_set);// E_S1\E_S2 \union {min(E_S2)}
        z3::expr succ_f = expr_tool::mk_belongsto(z3_ctx(), x, set_u);
        succ_f = succ_f && expr_tool::mk_belongsto(z3_ctx(), y, set_u) && y>=x+1;
        // z3::expr all2_f = z3::implies(expr_tool::mk_belongsto(z3_ctx(), z, set_u), !((z > x) && (y > z)) );
        z3::expr all2_f = !(expr_tool::mk_belongsto(z3_ctx(), z, set_u) && ((z >= x+1) && (y >= z+1)));
        // x \in set_u && y \in set_u && forall(z). (z \in set_u -> z<=x && y<=z)
        succ_f = succ_f && z3::forall(pars2, all2_f);

        // z3::expr all1_f = z3::implies(succ_f, all_body.substitute(src3, pars1));
        z3::expr all1_f = !(succ_f && !all_body.substitute(src3, pars1));

        //std::cout << "forall: " << all1_f << std::endl;

        // forall []
        tr_f = tr_f && z3::forall(pars1, all1_f);

        tr_f = !z3::forall(pars, !tr_f);

        phi_pd = !(!or_0 && !or_1 && !tr_f);
        return phi_pd;

}


/**
 * compute tr closure case by case 4, S2 is possible empty
 * @param phi_r1 : S1 = S2 union {min(S1), max(S1)}
 * @param strt_phi_r2 : phi_r2
 * @param setvars : S1, S2
 */
z3::expr listsetsolver::compute_tr_by_case4(z3::expr &phi_r1, z3::expr &strt_phi_r2, z3::expr_vector &phi_r2_items, z3::expr_vector &set_vars) {
        z3::expr phi_pd = z3_ctx().bool_val(true);
        z3::expr emptyset = expr_tool::mk_emptyset(z3_ctx());

        // S1 = S2 union {min(S1), max(S1)}, S2 possible empty
        z3::expr E_S1 = expr_tool::mk_set_var(z3_ctx(), "E_S1");
        z3::expr E_S2 = expr_tool::mk_set_var(z3_ctx(), "E_S2");
        z3::expr E_S3 = expr_tool::mk_set_var(z3_ctx(), "E_S3");
        z3::expr_vector pars(z3_ctx());
        pars.push_back(E_S1);
        pars.push_back(E_S2);
        pars.push_back(E_S3);

        //substitute
        z3::expr_vector src(z3_ctx());
        z3::expr_vector dst(z3_ctx());
        src.push_back(set_vars[0]);
        dst.push_back(E_S2);
        z3::expr tr_f = phi_r1.substitute(src, dst); // phi_r1[E_S/S]

        z3::expr E_S1_S2 = expr_tool::mk_binary_set(z3_ctx(), "setunion", E_S1, E_S2);
        z3::expr E_S1_S2_S3 = expr_tool::mk_binary_set(z3_ctx(), "setunion", E_S1_S2, E_S3);
        z3::expr item1 = (set_vars[0] == E_S1_S2_S3);
        tr_f = tr_f && item1;

        tr_f = tr_f && strt_phi_r2;
        tr_f = tr_f && strt_phi_r2.substitute(src, dst);

        z3::expr pre1 = !(E_S1 == emptyset);
        z3::expr n_pos1 = expr_tool::mk_min_max(z3_ctx(), 1, E_S1) >= expr_tool::mk_min_max(z3_ctx(), 0, E_S2);
        z3::expr imp1 = !(pre1 && n_pos1);

        z3::expr pre2 = !(E_S3 == emptyset);
        z3::expr n_pos2 = expr_tool::mk_min_max(z3_ctx(), 1, E_S2) >= expr_tool::mk_min_max(z3_ctx(), 0, E_S3);
        z3::expr imp2 = !(pre2 && n_pos2);

        tr_f = tr_f && imp1 && imp2;

        phi_pd = !(!(set_vars[0] == set_vars[1]) &&  z3::forall(pars, !tr_f)); // S1=S2 || exists

        return phi_pd;
}

/**
 * compute tr closure case by case 5, S2 is surely  nonempty
 * @param phi_r1 : S1 = S2 union {min(S1), max(S1)}
 * @param strt_phi_r2 : phi_r2
 * @param setvars : S1, S2
 */
z3::expr listsetsolver::compute_tr_by_case5(z3::expr &phi_r1, z3::expr &strt_phi_r2, z3::expr_vector &phi_r2_items, z3::expr_vector &set_vars) {
        z3::expr phi_pd = z3_ctx().bool_val(true);
        z3::expr emptyset = expr_tool::mk_emptyset(z3_ctx());


        z3::expr or_0 = (set_vars[0] == set_vars[1]); // S1 = S2
        z3::expr or_1 = (phi_r1 && strt_phi_r2); // phi_r


        // S1 = S2 union {min(S1), max(S1)}, S2 possible empty
        z3::expr E_S1 = expr_tool::mk_set_var(z3_ctx(), "E_S1");
        z3::expr E_S2 = expr_tool::mk_set_var(z3_ctx(), "E_S2");
        z3::expr E_S3 = expr_tool::mk_set_var(z3_ctx(), "E_S3");
        z3::expr E_S4 = expr_tool::mk_set_var(z3_ctx(), "E_S4");
        z3::expr_vector pars(z3_ctx());
        pars.push_back(E_S1);
        pars.push_back(E_S2);
        pars.push_back(E_S3);
        pars.push_back(E_S4);

        //substitute
        z3::expr_vector src(z3_ctx());
        z3::expr_vector dst(z3_ctx());
        src.push_back(set_vars[0]);
        dst.push_back(E_S2);

        z3::expr_vector src1(z3_ctx());
        z3::expr_vector dst1(z3_ctx());
        src1.push_back(set_vars[1]);
        dst1.push_back(E_S1);

        z3::expr item1 = phi_r1.substitute(src1, dst1); // phi_r1[E_S1/S']

        z3::expr E_S2_S3 = expr_tool::mk_binary_set(z3_ctx(), "setunion", E_S2, E_S3);
        z3::expr E_S2_S3_S4 = expr_tool::mk_binary_set(z3_ctx(), "setunion", E_S2_S3, E_S4);
        z3::expr item2 = (E_S1 == E_S2_S3_S4);

        z3::expr item3 = phi_r1.substitute(src, dst); // phi_r1[E_S2/S]

        z3::expr pre1 = !(E_S3 == emptyset);
        z3::expr n_pos1 = expr_tool::mk_min_max(z3_ctx(), 1, E_S3) >= expr_tool::mk_min_max(z3_ctx(), 0, E_S2);
        z3::expr item4 = !(pre1 && n_pos1);

        z3::expr pre2 = !(E_S4 == emptyset);
        z3::expr n_pos2 = expr_tool::mk_min_max(z3_ctx(), 1, E_S2) >= expr_tool::mk_min_max(z3_ctx(), 0, E_S4);
        z3::expr item5 = !(pre2 && n_pos2);

        z3::expr phi_r2_01 = phi_r2_items[0];
        z3::expr phi_r2_02 = phi_r2_items[1];

        z3::expr item6 = phi_r2_items[0].substitute(src, dst) && phi_r2_items[0].substitute(src1, dst1) &&
                phi_r2_items[1] && phi_r2_items[1].substitute(src, dst) &&
                phi_r2_items[2].substitute(src, dst) && phi_r2_items[2].substitute(src1, dst1) &&
                phi_r2_items[3].substitute(src, dst) && phi_r2_items[3].substitute(src1, dst1) &&
                phi_r2_items[4] && phi_r2_items[4].substitute(src1, dst1) &&
                phi_r2_items[5].substitute(src, dst) && phi_r2_items[5].substitute(src1, dst1);

        z3::expr_vector pars1(z3_ctx());
        z3::expr_vector pars2(z3_ctx());
        z3::expr x = z3_ctx().int_const("x");
        z3::expr y = z3_ctx().int_const("y");
        z3::expr z = z3_ctx().int_const("z");
        pars1.push_back(x);
        pars1.push_back(y);
        pars2.push_back(z);

        z3::expr_vector src3(z3_ctx());
        // src3(min(S1), min(S2))
        src3.push_back(expr_tool::mk_min_max(z3_ctx(), 0, set_vars[0]));
        src3.push_back(expr_tool::mk_min_max(z3_ctx(), 0, set_vars[1]));
        z3::expr_vector src4(z3_ctx());
        // src4(max(S2), max(S1))
        src4.push_back(expr_tool::mk_min_max(z3_ctx(), 1, set_vars[1]));
        src4.push_back(expr_tool::mk_min_max(z3_ctx(), 1, set_vars[0]));


        z3::expr set_u = expr_tool::mk_set_var(z3_ctx(), "SS");
        z3::expr_vector src5(z3_ctx());
        src5.push_back(set_u);
        //expr_tool::mk_binary_set(z3_ctx(), "setunion", E_S3, set_min_e_s2);// E_S3 \union {min(E_S2)}
        z3::expr succ_f = expr_tool::mk_belongsto(z3_ctx(), x, set_u);
        succ_f = succ_f && expr_tool::mk_belongsto(z3_ctx(), y, set_u) && y>=x+1;
        z3::expr all2_f = !(expr_tool::mk_belongsto(z3_ctx(), z, set_u) && ((z >= x+1) && (y >= z+1)));
        // x \in set_u && y \in set_u && forall(z). (z \in set_u -> z<=x && y<=z)
        succ_f = succ_f && z3::forall(pars2, all2_f);
        z3::expr min_e_s2 = expr_tool::mk_min_max(z3_ctx(), 0, E_S2);
        z3::expr set_min_e_s2 = expr_tool::mk_single_set(z3_ctx(), min_e_s2);
        z3::expr set_u1 = expr_tool::mk_binary_set(z3_ctx(), "setunion", E_S3, set_min_e_s2);// E_S3 \union {min(E_S2)}
        // z3::expr all1_f = z3::implies(succ_f, all_body.substitute(src3, pars1));
        z3::expr_vector dst5_1(z3_ctx());
        dst5_1.push_back(set_u1);
        z3::expr all_f1 = !(succ_f.substitute(src5, dst5_1) && !phi_r2_items[0].substitute(src3, pars1));

        z3::expr max_e_s2 = expr_tool::mk_min_max(z3_ctx(), 1, E_S2);
        z3::expr set_max_e_s2 = expr_tool::mk_single_set(z3_ctx(), max_e_s2);
        z3::expr set_u2 = expr_tool::mk_binary_set(z3_ctx(), "setunion", E_S4, set_max_e_s2);
        z3::expr_vector dst5_2(z3_ctx());
        dst5_2.push_back(set_u2);
        z3::expr all_f2 = !(succ_f.substitute(src5, dst5_2) && !phi_r2_items[5].substitute(src4, pars1));

        z3::expr item7 = z3::forall(pars1, all_f1) && z3::forall(pars1, all_f2);

        z3::expr_vector tms(z3_ctx());
        for(int i=0; i<phi_r2_items[0].num_args(); i++) {
                if (phi_r2_items[0].arg(i).to_string() != "true") {
                        tms.push_back(phi_r2_items[0].arg(i));
                }
        }
        for(int i=0; i<phi_r2_items[5].num_args(); i++) {
                if (phi_r2_items[5].arg(i).to_string() != "true") {
                        tms.push_back(phi_r2_items[5].arg(i));
                }
        }

        z3::expr item8 = z3_ctx().bool_val(true); // quantElmt

        if (tms.size() > 1) {
                z3::expr_vector quant_elmts(z3_ctx());
                quant_elmt(tms, quant_elmts);
                if (quant_elmts.size() > 0) {
                        item8 = z3::mk_and(quant_elmts);
                }
        }

        m_pred_tms.push_back(item8);
        // std::cout << "item8: " << item8 << std::endl;
        // exit(0);

        z3::expr tr_f = item1 && item2 && item3 && item4 && item5 && item6 && item7 && item8;

        phi_pd = !(!or_0 && !or_1 && z3::forall(pars, !tr_f));

        return phi_pd;
}

/**
 * quant elmt of (tms)
 * @param tms : terms
 * @param quant_elmts : result
 */
void listsetsolver::quant_elmt(z3::expr_vector &tms, z3::expr_vector& quant_elmts) {
        assert(tms.size() > 1);
        for (int i=0; i<tms.size(); i++) {
                for (int j=i+1; j<tms.size(); j++) {
                        z3::expr tm1 = tms[i];
                        z3::expr tm2 = tms[j];
                        z3::expr result = expr_tool::get_quant_elmt(z3_ctx(), tm1, tm2);
                        // std::cout << "result: " << result<< std::endl;
                        if (result.to_string() != "true") {
                                quant_elmts.push_back(result);
                        }
                }
        }
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
        z3::expr phi_r1 = phi_r.arg(0); // S = S2 union {min(S)} or S = S2 union {max(S)} or S = S2 union {min(S), max(S)}
        set_vars.push_back(phi_r1.arg(0));


        int case_i = 0; // case index
        int matrix[4][4]; // 0: min(set_vars[0]), 1: min(set_vars[1]), 2:max(set_vars[0]), 3:max(set_vars[1])

        // init
        for (int i=0; i<4; i++) {
                for (int j=0; j<4; j++) {
                        matrix[i][j] = INT_MAX;
                }
        }

        // std::cout << "phi_r1: " << phi_r1 << std::endl;
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
                term_s = phi_r1.arg(1).arg(1);
                if (expr_tool::is_fun(term_s, "setunion")) {
                        case_i = 4;
                } else if (expr_tool::is_fun(term_s.arg(0), "max")) {
                        case_i = 2;
                }
        }

        bool has_s2 = false;
        bool has_s1 = false;
        // add phi_r2
        for (int i=1; i<phi_r.num_args(); i++) {
                z3::expr phi_r2_i = phi_r.arg(i);
                // std::cout << "phi_r2_i : " << phi_r2_i << std::endl;
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

                        // std::cout << "row: " << row << ", col: " << col << std::endl;

                        if ( ((row&1) | (col&1)) == 1) has_s2 = true;
                        if( ((row&1) & (col&1)) == 0) has_s1 = true;

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


        // std::cout <<"has_s1: " << has_s1 << std::endl;


        if (has_s1)
                // min(S1) <= max(S1)
                set_matrix(matrix, 0, 2, 0);
        // add if has_s2
        if (has_s2) {
                // min(S2) <= max(S2)
                set_matrix(matrix, 1, 3, 0);

                if (case_i != -1)
                        case_i += 1;
                // add by term_s
                if (Z3_ast(term_s) != 0) {
                        set_matrix(matrix, 0, 1, 0); // min(S1) <= min(S2)
                        set_matrix(matrix, 3, 2, 0); // max(S2) <= max(S1)
                        if ((case_i & 6) == 0) {
                                // add max(S1) == max(S2)
                                set_matrix(matrix, 2, 3, 0); // max(S1) <= max(S2)
                                // set_matrix(matrix, 3, 2, 0);
                        } else if ((case_i & 6) == 2){
                                // add min(S1) == min(S2)
                                // set_matrix(matrix, 0, 1, 0);
                                set_matrix(matrix, 1, 0, 0); // min(S2) <= min(S1)
                        }
                }
        }


        // display(matrix);
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

                /*
                  std::cout << "phi_01: " << phi_01 << std::endl;
                  std::cout << "phi_02: " << phi_02 << std::endl;
                  std::cout << "phi_03: " << phi_03 << std::endl;
                  std::cout << "phi_12: " << phi_12 << std::endl;
                  std::cout << "phi_13: " << phi_13 << std::endl;
                  std::cout << "phi_23: " << phi_23 << std::endl;
                */


                strt_phi_r2 = (phi_01) && (phi_02) && phi_03 && phi_12 && phi_13 && phi_23;

        } else {
                strt_phi_r2 =  z3_ctx().bool_val(false);
        }



        //display(matrix, set_vars, "str_phi_r.dot");
        // exit(-1);
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
                if (matrix[i][j] != INT_MAX && -matrix[i][j] == matrix[j][i]) {
                        if (matrix[i][j] < 0) {
                                phi_ij = phi_ij && (get_card(j, set_vars) == get_card(i, set_vars) + z3_ctx().int_val(-matrix[i][j]));
                        } else {
                                phi_ij = phi_ij && (get_card(i, set_vars) == get_card(j, set_vars) + z3_ctx().int_val(matrix[i][j]));
                        }
                } else {
                        if (matrix[i][j] != INT_MAX) {
                                if (matrix[i][j] < 0) {
                                        phi_ij = phi_ij && (get_card(j, set_vars) >= get_card(i, set_vars) + z3_ctx().int_val(-matrix[i][j]));
                                } else {
                                        phi_ij = phi_ij && (get_card(i, set_vars) <= get_card(j, set_vars) + z3_ctx().int_val(matrix[i][j]));
                                }
                        }
                        if (matrix[j][i] != INT_MAX) {
                                if (matrix[j][i] < 0) {
                                        phi_ij = phi_ij && (get_card(i, set_vars) >= get_card(j, set_vars) + z3_ctx().int_val(-matrix[j][i]));
                                } else {
                                        phi_ij = phi_ij && (get_card(j, set_vars) <= get_card(i, set_vars) + z3_ctx().int_val(matrix[j][i]));
                                }
                        }
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

        // std::cout << "floyd.\n";
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
