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

/**
 * the size of static parameters for list predicate
 * @return size
 */
int predicate::size_of_static_parameters() {
        if (is_list()) {
                int i = m_pars.size()-1;
                for (; i>=0; i--) {
                        if (m_pars[i].to_string().find("sta_")!=0) break;
                }
                return m_pars.size() - i;
        }
        return 0;
}

/**
 * the index, when E occurs in gamma for list predicate
 * @return -1, E does not occur in gamma
 *         index
 */
int predicate::idx_E_gamma() {
        if (is_list()) {
                int size = m_pars.size() - size_of_static_parameters();
                for (int i=1; i<size/2; i++) {
                        if (m_rec_rules[0].get_rec_apps()[0].arg(i).hash() == m_pars[0].hash()) return i-1;
                }
        }
        return -1;
}
