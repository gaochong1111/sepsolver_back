#include "mona_translator.h"
#include <fstream>

std::string mop_strs[] = {"UNDEF",
                          " & ", " | ", "~", " => ", " <= ",
                          " < ", " >= ", " > ", " = ", " ~= ",
                          " + ", " - ", "min ", "max ", " union ",
                          " inter ", " \\ ", " sub ", " in ", "{$}"
};


/**
 * get string of formula
 */
void mona_translator::write_to_file(std::string name) {
        // 1. get var

        std::cout << "write to file: " << name << std::endl;
        std::ofstream out(name);

        out << "ws1s;\n";


        std::set<z3::expr, exprcomp> bool_vars;
        std::set<z3::expr, exprcomp> fo_vars;
        std::set<z3::expr, exprcomp> so_vars;

        expr_tool::get_zero_order_vars(m_formula, bool_vars);
        expr_tool::get_first_order_vars(m_formula, fo_vars);
        expr_tool::get_second_order_vars(m_formula, so_vars);

        std::string bool_decl_str = get_decl_str(0, bool_vars);

        std::string fo_decl_str = get_decl_str(1, fo_vars);

        std::string so_decl_str = get_decl_str(2, so_vars);


        if (bool_decl_str != "")
                out <<"var" << bool_decl_str << ";" << std::endl;
        if (fo_decl_str != "")
                out <<"var" <<fo_decl_str << ";" << std::endl;
        if (so_decl_str != "")
                out<<"var" << so_decl_str << ";" << std::endl;

        // 2. formula
        std::vector<std::set<std::string> > ctx_set_items;
        std::set<std::string> items;
        ctx_set_items.push_back(items);
        std::string formula_str = get_str(m_formula, 0, ctx_set_items);


        out << formula_str << ";" << std::endl;

        if (ctx_set_items.size() > 0) {
                std::set<std::string> set_items = ctx_set_items[0];
                for (auto item : set_items) {
                        out << "~empty(" << item << ");\n";
                }
        }


        out.close();
}

/**
 * get string of item
 * @param item
 * @param ctx: 0, 1, 2, ... (init 0, quantifier +1)
 * @param vector of set_items: ctx -> non-empty set items
 * @return string
 */
std::string mona_translator::get_str(z3::expr item,  int ctx, std::vector<std::set<std::string> >& ctx_set_items) {

        std::string str = "(";
        if (item.is_app()) {
                int num_args = item.num_args();
                if (num_args == 0) {
                        return expr_tool::get_mona_name(item);
                }
                // operation
                std::string op = item.decl().name().str();
                mona_op mop = op_map[op];
                if (mop == 0) {
                        std::cout << "UNSUPPORTED MONA OP: " << op << " !\n";
                        exit(-1);
                }
                std::string op_str = mop_strs[mop];
                if (mop <= MONA_OR) {
                        int size = item.num_args();
                        for (int i=0; i<size; i++) {
                                str.append(get_str(item.arg(i), ctx, ctx_set_items));
                                if (i<size-1) str.append(op_str);
                        }
                } else if(num_args == 2) {
                        //
                        std::string item1 = get_str(item.arg(0), ctx, ctx_set_items);
                        std::string item2 = get_str(item.arg(1), ctx, ctx_set_items);


                        if (item1 == "emptyset" || item2 == "emptyset") {
                                std::string item = item1=="emptyset"? item2 : item1;
                                if (mop == MONA_DISTINCT) {
                                        str.append("~");
                                }
                                str.append("empty(").append(item).append(")");
                        } else {
                                str.append(item1);
                                str.append(op_str);
                                str.append(item2);
                        }
                } else if (num_args == 1) {
                        std::string item1 = get_str(item.arg(0), ctx, ctx_set_items);
                        if (mop == MONA_MIN || mop == MONA_MAX) {
                                ctx_set_items[ctx].insert(item1);
                        }
                        if (mop == MONA_SET) {
                                str.append("{").append(item1).append("}");
                        } else {
                                str.append(op_str);
                                str.append(item1);
                        }

                }
        } else if (item.is_quantifier()){
                // quantifiers
                z3::expr_vector bounds(m_ctx);
                z3::expr body(m_ctx);
                expr_tool::get_pars_quantifier(m_ctx, item, bounds, body);
                bool is_forall = Z3_is_quantifier_forall(Z3_context(m_ctx), Z3_ast(item));
                std::string bounds_str = get_quantifier_bounds_str(is_forall, bounds);

                std::set<std::string> items;
                ctx_set_items.push_back(items);
                std::string body_str = get_str(body, ctx+1, ctx_set_items);

                std::set<std::string> no_empty_items = ctx_set_items.back();
                ctx_set_items.pop_back();
                for (auto item : no_empty_items) {
                        body_str.append(" & ~empty(").append(item).append(")");
                }
                str.append(bounds_str).append("\n").append(body_str);
        }
        str.append(")");
        return str;
}

/**
 * get string of quantifier bounds
 * @param is_all : forall flag
 * @param bounds :
 * @return string
 */
std::string mona_translator::get_quantifier_bounds_str(bool is_all, z3::expr_vector &bounds) {
        std::set<z3::expr, exprcomp> bool_vars;
        std::set<z3::expr, exprcomp> fo_vars;
        std::set<z3::expr, exprcomp> so_vars;
        for (int i=0; i<bounds.size(); i++) {
                if (bounds[i].is_bool()) {
                        bool_vars.insert(bounds[i]);
                } else if (bounds[i].is_int()) {
                        fo_vars.insert(bounds[i]);
                } else {
                        so_vars.insert(bounds[i]);
                }
        }
        std::string str="";
        std::string quant_str = is_all? "all" : "ex";
        std::string str0 = get_decl_str(0, bool_vars);
        std::string str1 = get_decl_str(1, fo_vars);
        std::string str2 = get_decl_str(2, so_vars);

        if (str0 != "") str.append(quant_str).append(str0).append(": ");
        if (str1 != "") str.append(quant_str).append(str1).append(": ");
        if (str2 != "") str.append(quant_str).append(str2).append(": ");

        return str;
}

/**
 * get string of declare vars
 * @param order : 0, 1, 2
 * @param var_set : vars
 * @return string
 */
std::string mona_translator::get_decl_str(int order, std::set<z3::expr, exprcomp> &var_set) {
        if (order > 2 || var_set.size() == 0) return "";


        std::string str = "";
        if (order == 0) {
                str.append("0 ");
        } else if (order == 1) {
                str.append("1 ");
        } else if (order == 2) {
                str.append("2 ");
        }

        int size = var_set.size();
        int i=0;
        for (auto exp : var_set) {
                str.append(expr_tool::get_mona_name(exp));
                if (i<size-1) str.append(", ");
                i++;
        }
        // str.append(";\n");
        return str;
}
