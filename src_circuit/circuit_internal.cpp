#include "../src/internal.hpp"

namespace CaDiCaL {

void Internal::circuit_init(const Circuit_Graph *graph_ptr) {
    assert (circuit_wtab.size() == (size_t)(2 * (max_var + 1)));
    assert (circuit_dwtab.size() == (size_t)(2 * (max_var + 1)));

    // 确定每个gate监视值和监视指针、并把其放入监视列表
    const auto &gates = graph_ptr->get_gates();
    for (const auto &gate : gates) {
        assert(clause.empty());
        // watch_value of and-gate: 0(output), 1(input1), 1(input2)
        // if input has inverter, watch_value is inverted
        // if output has inverter, watch_value is inverted
        clause = gate->get_PIs();
        clause.push_back(gate->get_PO() * -1);

        auto cur_gate_info_ptr = circuit_new_gate(false, clause.size());
        clause.clear();

        // 把input1和input2作为监视指针，并把其放入监视列表
        circuit_watch_gate(cur_gate_info_ptr);

        // 构建直接蕴含图
        circuit_watch_gate_direct(cur_gate_info_ptr);
    }

    const auto& outputs = graph_ptr->get_outputs();
    for (const auto output : outputs) {
        circuit_assign_original_unit(output);
    }
}

/**
 * @note:   internal.cpp: solve()
 */
int Internal::circuit_solve() {
    START (solve);

    int result = circuit_cdcl_loop_with_inprocessing();

    STOP (solve);
    return result;
}

/**
 * @brief:  the main CDCL loop
 * @note:   internal.cpp:   cdcl_loop_with_inprocessing()
 */
int Internal::circuit_cdcl_loop_with_inprocessing() {
    int res = 0;
    START (search);

    if (stable) {
        START (stable);
        report ('[');
    } else {
        START (unstable);
        report ('{');
    }

    while (!res) {
        if (unsat) {
            res = 20;
        } else if (!circuit_propagate()) {
            circuit_analyze();                      // propagate and analyze
        } else if (iterating) {
            circuit_iterate();                      // report learnt unit
        } else if (circuit_satisfied()) {
            res = 10;                               // already satisfied
        } else if (search_limits_hit()) {
            break;                                  // decision or conflict limit
        } else if (circuit_restarting()) {
            circuit_restart();                      // restart by backtracking
        } else if (circuit_rephasing()) {
            circuit_rephase();                      // reset variable phases
        } else if (circuit_reducing()) {
            circuit_reduce();                       // collect useless clauses
        } else if (circuit_probing()) {
            circuit_probe();                        // failed literal probing
        } else if (circuit_subsuming()) {
            circuit_subsume();                      // subsumption algorithm
#if 0
        } else if (circuit_eliminating()) {
            circuit_elim();                         // variable elimination
#endif
        } else {
            circuit_decide();                       // next decision
        }
    }

    if (stable) {
        STOP (stable);
        report (']');
    } else {
        STOP (unstable);
        report ('}');
    }

    STOP (search);

    return res;
}

}
