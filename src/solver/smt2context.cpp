#include "smt2context.h"

bool smt2context::is_tree() {
        // TODO
        for (int i=0; i<m_preds.size(); i++) {
                if (!m_preds[i].is_tree()) return false;
        }
        return true;
}

bool smt2context::is_list() {
        // TODO
        for (int i=0; i<m_preds.size(); i++) {
                if (!m_preds[i].is_list()) return false;
        }
        return true;
}
