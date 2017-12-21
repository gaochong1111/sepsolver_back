#ifndef TREESOLVER_H
#define TREESOLVER_H

#include "solver.h"
#include "treechecker.h"

/**
 * tree predicate solver
 */
class treesolver :public solver {
private:
        void get_constants(z3::expr const& exp, std::set<z3::expr, exprcomp>& vec);
        void get_constants(predicate& pred, std::set<z3::expr, exprcomp>& vec);


        void get_alpha_beta(predicate& pred, z3::expr_vector& alpha, z3::expr_vector& beta);
        void get_alpha_beta(predicate& pred, std::vector<Vertex>& alpha, std::vector<Vertex>& beta);
        void get_gamma_delta_epsilon(pred_rule& rule, z3::expr_vector& gamma, z3::expr_vector& delta, z3::expr_vector& epsilon);
        void get_gamma_delta_epsilon(pred_rule& rule, std::vector<Vertex>& gamma, std::vector<Vertex>& delta, std::vector<Vertex>& epsilon);
        z3::expr_vector get_x_h(pred_rule& rule);

        void expr2graph(z3::expr& exp, OrderGraph& og);
        void exp2vertex(z3::expr_vector& exp_vec, std::vector<Vertex>& ver_vec);
        void exp2vertex(std::set<z3::expr, exprcomp>& exp_set, std::vector<Vertex>& ver_vec);
        void vector2set(std::vector<Vertex>& ver_vec, std::set<Vertex>& ver_set);
        std::string get_exp_name(z3::expr exp);
        std::string simplify_var_name(std::string str);
        z3::expr vertex2exp(Vertex v);
        z3::expr edge2exp(Edge e);
        z3::expr graph2exp(OrderGraph& og);

        void compute_all_delta_ge1_p();

        z3::expr compute_delta_phi_pd(predicate& pred);
        z3::expr compute_delta_ge1_rule(pred_rule& rule, predicate& pred, z3::expr& delta_ge1_p_abs);

        OrderGraphSet lfp(predicate& pred);

public:
    treesolver(smt2context& ctx) : solver(ctx){}
        void check_preds();
        z3::check_result check_sat();
        z3::check_result check_entl();
        z3::expr pred2abs(z3::expr& atom, int i, z3::expr_vector& new_bools);
        std::string get_model_of_atom(z3::model& m, z3::expr& atom, int i, int n);
        z3::model get_model() {}
};



#endif /* TREESOLVER_H */
