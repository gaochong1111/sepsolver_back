#include "sat_rqspa.h"

/**
 * get line content :
 * @param str : format "  : content "
 */
void sat_rqspa::get_content(std::string& str) {
        int start = str.find(":");
        str = str.substr(start+2, str.size());
        boost::trim(str);
}

/**
 * get transition
 * @param str : format : "State $src :0XXX -> State $dst"
 */
void sat_rqspa::get_transition(std::string& str, transition& tr) {
        int start = str.find(" ");
        int end = str.find(":");
        std::string src = str.substr(start+1, end-start-1);
        tr.src = boost::lexical_cast<int>(src);

        start = end;
        end = str.find("->");

        std::string info = str.substr(start+2, end-start-3);
        for (int i=0; i<info.size(); i++) {
                tr.info.push_back(info.substr(i, 1));
        }

        start = str.find("state", end);
        end = str.size()-1;

        std::string dst = str.substr(start+6, end-start-5);
        tr.dst = boost::lexical_cast<int>(dst);
}

/**
 * read file, create fa
 * @param fa
 * @param file_name
 * @param prefix : the state prefix
 */
void sat_rqspa::read_file(FA& fa, std::string file_name, std::string prefix) {
        std::ifstream fin(file_name);

        std::string str;
        getline(fin, str);// first blank line
        // read vars
        std::vector<std::string> vars;
        getline(fin, str);
        get_content(str);
        boost::split(vars, str, boost::is_any_of(" "));

        fa.set_alphabet_set(vars);

        // read init state
        getline(fin, str);
        get_content(str);
        int i_state = boost::lexical_cast<int>(str);
        fa.set_init_state(i_state);

        // read accept states
        getline(fin, str);
        get_content(str);
        std::vector<std::string> fstr_states;
        boost::split(fstr_states, str, boost::is_any_of(" "));
        std::vector<int> f_states;
        for (int i=0; i<fstr_states.size(); i++) {
                f_states.push_back(boost::lexical_cast<int>(fstr_states[i]));
        }
        fa.set_accept_states(f_states);

        // skip 2 lines
        getline(fin, str); getline(fin, str);

        // get number of states
        getline(fin, str);
        int start = str.find("has");
        int end = str.find("states");
        str = str.substr(start+3, end-start-3);
        boost::trim(str);
        int number = boost::lexical_cast<int>(str);

        fa.add_states(number, prefix);

        // read transitions
        getline(fin, str);

        // int t_count = 0;
        while(getline(fin, str)) {
                if (str.find("State") != 0) break;
                transition tr;
                get_transition(str, tr);
                fa.add_transition(tr);
                // std::cout << "transition: " << tr.src << "-> " <<  tr.dst << " : " << tr.info[0] << std::endl;
                // t_count ++;
        }
        // std::cout << "tr count: " << t_count << std::endl;

        fin.close();
}

/**
 * var in phi_count -> NFA
 * @param : var
 * @param : nfa [with alphabet]
 */
void sat_rqspa::generate_NFA(z3::expr var, FA& nfa) {
        int total = nfa.get_alphabet().size();
        int idx = nfa.get_pos(var.to_string());
        std::string prefix = var.to_string();
        prefix.append("_");

        transition tr;
        for (int i=0; i<total; i++) {
                tr.info.push_back("X");
        }

        std::vector<int> accept_states;

        if (expr_tool::is_setint(var)) {
                nfa.add_states(4, prefix);
                accept_states.push_back(3);

                // add transitions
                // 0->1 : X
                tr.src = 0; tr.dst = 1; tr.info[idx] = "X";
                nfa.add_transition(tr);

                tr.src = 1; tr.dst = 1; tr.info[idx] = "0";
                nfa.add_transition(tr); // 1->1
                tr.dst = 2; tr.info[idx] = "1";
                nfa.add_transition(tr); // 1->2
                tr.dst = 3;
                nfa.add_transition(tr); // 1->3
                tr.src = 2;
                nfa.add_transition(tr); // 2->3
                tr.dst = 2; tr.info[idx] = "X";
                nfa.add_transition(tr); // 2->2
                tr.src = 3; tr.dst=3; tr.info[idx] = "0";
                nfa.add_transition(tr); // 3->3

        } else {
                nfa.add_states(3, prefix);
                accept_states.push_back(2);
                // add transitions
                tr.src = 0; tr.dst = 1; tr.info[idx] = "X";
                nfa.add_transition(tr);

                tr.src = 1; tr.dst = 1; tr.info[idx] = "0";
                nfa.add_transition(tr); // 1->1
                tr.dst = 2; tr.info[idx] = "1";
                nfa.add_transition(tr); // 1->2
                tr.src = 2; tr.info[idx] = "0";
                nfa.add_transition(tr); // 2->2
        }

        nfa.set_accept_states(accept_states);
}

/**
 * gnerate first order var relation with new vars
 * @param idx : index in vars of phi_count
 */
z3::expr sat_rqspa::generate_fovar_expr(int idx) {

        z3::expr_vector sum_items(m_ctx);
        for (int cur : m_new_ids) {
                // i-th
                int temp = cur % m_factors[idx];
                temp = temp / m_factors[idx+1];
                if (temp == 0) {
                        std::string x_name = "x_";
                        x_name.append(std::to_string(cur));
                        sum_items.push_back(m_ctx.int_const(x_name.c_str()));
                }
        }
        return m_vars[idx] == (z3::sum(sum_items)-1);
}

/**
 * gnerate second order var relation with new vars
 * @param idx : index in vars of phi_count
 */
z3::expr sat_rqspa::generate_sovar_expr(int idx) {
        z3::expr result = m_ctx.bool_val(true);

        z3::expr_vector sum0_items(m_ctx);
        z3::expr_vector sum1_items(m_ctx);
        sum1_items.push_back(m_ctx.int_val(0));
        for (int cur : m_new_ids) {
                // i-th
                int temp = cur % m_factors[idx];
                temp = temp / m_factors[idx+1];
                std::string x_name = "x_";
                x_name.append(std::to_string(cur));
                if (temp == 1) {
                        sum0_items.push_back(m_ctx.int_const(x_name.c_str()));
                } else if (temp == 2) {
                        sum1_items.push_back(m_ctx.int_const(x_name.c_str()));
                }
        }

        std::string var_name = "min_";
        var_name.append(m_vars[idx].to_string());
        z3::expr min_var = m_ctx.int_const(var_name.c_str());
        var_name = "max_";
        var_name.append(m_vars[idx].to_string());
        z3::expr max_var = m_ctx.int_const(var_name.c_str());

        z3::expr sigma0 = z3::sum(sum0_items);
        // std::cout << "sigma0: " << sigma0 << std::endl;
        // exit(0);
        result = (min_var == sigma0 - 1) && (max_var == min_var + z3::sum(sum1_items));

        return result;
}

/**
 * get vars in phi_count -> m_vars
 *
 */
void sat_rqspa::get_vars() {
        std::set<z3::expr, exprcomp> fovs;
        std::set<z3::expr, exprcomp> sovs;
        expr_tool::get_first_order_vars(m_phi_count, fovs);
        expr_tool::get_second_order_vars(m_phi_count, sovs);
        m_vars.insert(m_vars.end(), fovs.begin(), fovs.end());
        m_vars.insert(m_vars.end(), sovs.begin(), sovs.end());
}


FA sat_rqspa::generate_PA() {

        FA phi_core;
        read_file(phi_core, m_file_name, "q_");

        std::cout << "accept: " << phi_core.get_accept_states().size() << ", states: " << phi_core.get_state_num() << std::endl;

        phi_core = phi_core.get_flow(); // get nfa with one accept state

        phi_core.print("phi_core.dot");


        // state_code
        std::vector<int> state_code;
        int total = phi_core.get_state_num();
        state_code.push_back(total);
        //
        get_vars();
        // std::cout << "get vars : " << m_vars.size() << std::endl;
        // generate nfa for var in phi_count
        std::vector<FA> nfas;
        for (int i=0; i<m_vars.size(); i++) {
                FA t_fa;
                t_fa.set_alphabet_set(phi_core.get_alphabet());
                generate_NFA(m_vars[i], t_fa);
                nfas.push_back(t_fa);
                // t_fa.print("t_fa.dot");
                state_code.push_back(t_fa.get_state_num());
        }

        // compute factors by state_code
        int acc = 1;
        // std::vector<int> factors;
        m_factors.push_back(1);

        for (int i=state_code.size()-1; i>0; i--) {
                acc *= state_code[i];
                m_factors.insert(m_factors.begin(), acc);
        }

        // compute product of all nfa
        FA fa_result = phi_core;
        for (int i=0; i<nfas.size(); i++) {
                // std::string fa_name = "fa_result_produce_";
                // fa_name.append(std::to_string(i)).append(".dot");
                fa_result = fa_result.product(nfas[i]);
                // fa_result.print(fa_name);
        }
        m_result = fa_result;
        fa_result.print("fa_result.dot");
        FA pa = fa_result.state_as_edge();

        pa.print("pa_before.dot");

        return pa;

}

/**
 * pa -> z3 expr
 *
 */
z3::expr sat_rqspa::generate_expr(FA& pa) {
        // henuristic

        // pa = pa.get_subgraph();

        // pa.print("pa.dot");


        // std::set<int> x_ids;
        int accept_state = pa.get_accept_states()[0];

        std::cout << "compute flow : 0 -> " << accept_state << std::endl;

        // pa.print_flow(accept_state);
        m_new_ids.clear();
        z3::expr pa_phi = pa.to_expr(m_ctx, accept_state, m_new_ids, m_tpaq_set);


        // generate expr relation with vars in phi_count and new vars

        z3::expr_vector var_items(m_ctx);

        for (int i=0; i<m_vars.size(); i++) {
                if (expr_tool::is_setint(m_vars[i])) {
                        var_items.push_back(generate_sovar_expr(i));

                } else {
                        var_items.push_back(generate_fovar_expr(i));
                }
        }

        z3::expr var_item = z3::mk_and(var_items);

        // expr_tool::write_file("var_item.smt", var_item);

        z3::expr flow_item = pa_phi && var_item;


        // std::cout << "phi_count: " << phi_count << std::endl;

        z3::expr_vector ge_zero_items(m_ctx);

        std::cout << "tpaq size: " << m_tpaq_set.size() << std::endl;

        for (z3::expr tpaq : m_tpaq_set) {
                ge_zero_items.push_back(tpaq >= 0);
        }
        z3::expr ge_zero = z3::mk_and(ge_zero_items);

        // z3::expr result = flow_items[1]  && phi_count; //  phi_count &&
        z3::expr result = flow_item && ge_zero; //  && phi_count;


        return result;
}

z3::expr sat_rqspa::sub_phi_count() {
        // substitute phi_count
        z3::expr_vector src(m_ctx);
        z3::expr_vector dst(m_ctx);
        for (int i=0; i<m_vars.size(); i++) {
                if (expr_tool::is_setint(m_vars[i])) {
                        z3::expr min_var = expr_tool::mk_min_max(m_ctx, 0, m_vars[i]);
                        z3::expr max_var = expr_tool::mk_min_max(m_ctx, 1, m_vars[i]);
                        src.push_back(min_var);
                        src.push_back(max_var);
                        std::string var_name = "min_";
                        var_name.append(m_vars[i].to_string());
                        z3::expr min_v = m_ctx.int_const(var_name.c_str());
                        var_name = "max_";
                        var_name.append(m_vars[i].to_string());
                        z3::expr max_v = m_ctx.int_const(var_name.c_str());
                        dst.push_back(min_v);
                        dst.push_back(max_v);
                }
        }

        z3::expr phi_count = m_phi_count.substitute(src, dst);
        return phi_count;
}


/**
 * check sat the phi of pa
 * @param vars : vars in model
 * @param m_model : m_model
 * @return check_result
 */
z3::check_result sat_rqspa::check_sat(std::vector<z3::expr>& vars, std::map<std::string, std::string>& m_model) {
        FA pa = generate_PA();
        z3::expr phi_count = sub_phi_count();

        int N = 1;
        FA sub_pa;
        for (int i=1; i<=N+1; i++) {
                if (i <= N) {
                        sub_pa = pa.get_subgraph(i);
                        sub_pa.print("pa_henuristic_"+std::to_string(i)+".dot");
                } else {
                        sub_pa = pa;
                }

                z3::expr pa_phi = generate_expr(sub_pa) && phi_count;

                z3::solver solver(m_ctx);
                solver.add(pa_phi);
                std::cout << "z3 is checking .....\n";
                z3::check_result result = solver.check();

                if (result == z3::sat) {

                        std::cout << "the result is sat! get models ....\n";
                        // get model
                        z3::model model = solver.get_model();

                        display_model(model, vars, m_model);

                        return z3::sat;
                }
        }


        // std::cout << "check result: " << result << std::endl;
        return z3::unsat;
}


void sat_rqspa::display_model(z3::model& model, std::vector<z3::expr>& vars, std::map<std::string, std::string>& m_model) {



        // std::cout << "tpaq size: " << m_tpaq_set.size() << std::endl;
        std::map<std::string, int> edge_to_count; // edge -> times
        for (z3::expr tpaq : m_tpaq_set) {
                if (model.has_interp(tpaq.decl())) {
                        z3::expr val = model.get_const_interp(tpaq.decl());
                        if (val.get_numeral_int() < 0) {
                                std::cout << tpaq << "  LESS THAN 0!\n";
                                exit(-1);
                        }
                        edge_to_count[tpaq.to_string()] = val.get_numeral_int();

                } else {
                        std::cout<< tpaq << "   NO TPAQ.\n";
                        exit(-1);
                }
        }


        std::vector< std::vector< std::string> > word;
        m_result.print_model("sat_model.dot", m_new_ids, edge_to_count, model, m_ctx, word);

        /*
          for (int i=0; i<word.size(); i++) {
          std::cout << m_result.vec_to_str(word[i], ", ") << std::endl;
          }
          std::cout << std::endl;
        */

        // std::cout << "word len: " <<  word.size() << std::endl;
        for (int i=0; i<vars.size(); i++) {
                z3::expr var = vars[i];
                std::string key = expr_tool::get_mona_name(var);
                int pos = m_result.get_pos(key);

                // std::cout << "var: "<< var << ", pos: "<< pos << ", sort: " << var.get_sort() <<std::endl;


                if (var.is_bool()) {
                        // std::cout << "word[0]: " <<  m_result.vec_to_str(word[0], ", ") << std::endl;
                        // std::cout << "word[0][pos]: " << word[0][pos] << std::endl;
                        // key = expr_tool::get_mona_name(var);
                        if (word[0][pos] == "0") {
                                m_model[key] = "false";
                        } else {
                                m_model[key] = "true";
                        }
                        // std::cout << key << ": " << m_model[key] << std::endl;
                } else {
                        std::string val;
                        std::vector<std::string> val_vec;
                        for (int j=1; j<word.size(); j++) {
                                if (word[j][pos] == "1") {
                                        val = std::to_string(j-1);
                                        if (var.is_int()) {
                                                break;
                                        } else {
                                                val_vec.push_back(val);
                                        }
                                }
                        }

                        //
                        if (val_vec.size() == 0) {
                                m_model[key] = val;
                        } else {
                                std::string val_str = "{";
                                val_str.append(m_result.vec_to_str(val_vec, ", ")).append("}");
                                m_model[key] = val_str;
                        }
                }


                // std::cout << key << "->"  << m_model[key] << std::endl;

        }


        for (int i=0; i<m_vars.size(); i++) {
                z3::expr sov = m_vars[i];
                std::string var_name = "min_";
                var_name.append(sov.to_string());
                z3::expr min_v = m_ctx.int_const(var_name.c_str());
                var_name = "max_";
                var_name.append(sov.to_string());
                z3::expr max_v = m_ctx.int_const(var_name.c_str());
                z3::expr min_val = model.get_const_interp(min_v.decl());
                z3::expr max_val = model.get_const_interp(max_v.decl());


                std::cout << min_v << ": " << min_val << std::endl;
                std::cout << max_v << ": " << max_val << std::endl;
        }



        /*
        // x_i
        for (int id : m_new_ids) {
        std::string pre = "x_";
        pre.append(std::to_string(id));
        z3::expr x_i = m_ctx.int_const(pre.c_str());
        if (model.has_interp(x_i.decl())) {
        z3::expr val = model.get_const_interp(x_i.decl());
        if (val.get_numeral_int() > 0) {
        std::cout << x_i << ": " << val << std::endl;
        } else {
        if (val.get_numeral_int() < 0) {
        std::cout << x_i << " LESS THAN 0!\n";
        exit(-1);
        }
        }
        }
        }
        */
}
