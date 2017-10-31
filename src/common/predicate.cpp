#include "predicate.h"

bool predicate::is_tree() {
        for (int i=0; i<m_rec_rules.size(); i++) {
                if (!m_rec_rules[i].is_tree_rule()) return false;
        }
        return true;
}

bool predicate::is_list() {
        return m_rec_rules.size() == 1 && m_rec_rules[0].is_list_rule();
}

std::ostream& operator<<(std::ostream& out, predicate& p) {
        out << "pars: \n" << p.m_pars << std::endl;
        out << "base rule: \n" << p.m_base_rule << std::endl;
        out << "m_rec_rules: \n";
        for (int i=0; i<p.m_rec_rules.size(); i++) {
                out << "index: " << i << " :\n" << p.m_rec_rules[i] << std::endl;
        }
        return out;
}
