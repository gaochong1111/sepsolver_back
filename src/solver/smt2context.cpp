#include "smt2context.h"
#include "listsolver.h"
#include "treesolver.h"

bool smt2context::is_tree() {
        for (int i=0; i<m_preds.size(); i++) {
                if (!m_preds[i].is_tree()) return false;
        }
        return true;
}

bool smt2context::is_list() {
        for (int i=0; i<m_preds.size(); i++) {
                if (!m_preds[i].is_list()) return false;
        }
        return true;
}

predicate smt2context::get_pred(int index) {
        assert(index < m_preds.size());
        return m_preds[index];
}

bool  smt2context::is_no_formula() {
        return (Z3_ast(m_posf) == 0) && (Z3_ast(m_negf) == 0);
}

bool  smt2context::is_sat() {
        return Z3_ast(m_posf) == 0;
}

bool  smt2context::is_entl() {
        return (Z3_ast(m_negf) != 0) && (Z3_ast(m_posf) != 0);
}
