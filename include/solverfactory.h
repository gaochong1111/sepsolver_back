#ifndef SOLVERFACTORY_H
#define SOLVERFACTORY_H
#include "solver.h"
#include "listsolver.h"
#include "treesolver.h"
#include "smt2context.h"

class solverfactory {
public:
        static solver* get_solver(smt2context& ctx) {
                // solve the tree predicate case
                if (ctx.is_tree()) {
                        std::cout << "tree solver.\n";
                        //  treesolver sol(ctx);
                        return new treesolver(ctx);
                } else if (ctx.is_list()) {
                        //TODO: solve the list predicate case
                        std::cout << "list solver.\n";
                        // listsolver sol(ctx);
                        //sol.solve();
                        return new listsolver(ctx);
                } else {
                        std::cout << "unsupported. \n";
                        return NULL;
                }
        }
};



#endif /* SOLVERFACTORY_H */
