#ifndef SAT_RQSPA_H
#define SAT_RQSPA_H

#include "fa.h"
#include "expr_tool.h"

#include <z3++.h>
#include <fstream>
#include <vector>
#include <boost/algorithm/string.hpp>
#include <boost/lexical_cast.hpp>


class sat_rqspa {
private:
        z3::expr m_phi_count;
        z3::context& m_ctx;
        std::string m_file_name;
        std::vector<z3::expr> m_vars;
        FA m_result;
        std::set<int> new_ids;
        std::set<z3::expr, exprcomp> m_tpaq_set;
public:
sat_rqspa(std::string file_name, z3::expr phi_count, z3::context& ctx) :m_file_name(file_name), m_phi_count(phi_count), m_ctx(ctx){}
        void get_content(std::string& str);
        void get_transition(std::string& str, transition& tr);
        void read_file(FA& fa, std::string file_name, std::string prefix);
        void generate_NFA(z3::expr var, FA& nfa);
        z3::expr generate_fovar_expr(int idx, std::vector<int> factors, std::set<int>& x_ids);
        z3::expr generate_sovar_expr(int idx, std::vector<int> factors, std::set<int>& x_ids);
        void get_vars();
        z3::expr generate_expr();
        z3::check_result check_sat(std::vector<z3::expr>& vars, std::map<std::string, std::string>& model);

};



#endif /* SAT_RQSPA_H */
