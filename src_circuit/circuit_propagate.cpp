#include "../src/internal.hpp"

namespace CaDiCaL {

static Circuit_Gate circuit_decision_reason_gate;
static Circuit_Gate *circuit_decision_reason = &circuit_decision_reason_gate;

/**
 * @beief calculate actual assignment level
 * If chronological backtracking is used the actual assignment level might be lower than the current decision level
 */
inline int Internal::circuit_assignment_level(int lit, Circuit_Gate *reason) {
    assert(opts.chrono);

    assert(reason);
    int res = 0;
    for (const auto &other : *reason) {
        if (lit == -other)
            continue;
        int tmp = circuit_assign_level_get(other);
        if (tmp > res) {
            res = tmp;
        }
    }
    return res;
}

/**
 * @beief assign val for gate_id with reasons
 * @note    propagate.cpp   search_assign()
 * @param   lit (gate_id * gate_val)
 */
inline void Internal::circuit_search_assign(int lit, Circuit_Gate* reason, int reason_direct) {
    const int idx = vidx(lit);
    assert(!val(idx));
    Var& v = var (idx);
    int lit_level = 0;
    if (!reason && !reason_direct)
        lit_level = 0;                          // unit
    else if (reason == circuit_decision_reason)
        lit_level = level, reason = nullptr;    // decision
    else if (opts.chrono)
        lit_level = reason ? circuit_assignment_level(lit, reason) : circuit_assign_level_get(reason_direct);
    else
        lit_level = level;
    if (!lit_level)
        reason = nullptr, reason_direct = 0;

    v.level = lit_level;
    v.trail = (int) trail.size();
    v.circuit_reason = reason;
    v.circuit_reason_direct = reason_direct;
    assert ((int) num_assigned < max_var);
    assert (num_assigned == trail.size ());
    num_assigned++;
    if (!lit_level)
        circuit_learn_unit_clause(lit);    // increases 'stats.fixed'
    const signed char tmp = sign(lit);
    circuit_set_val(idx, tmp);
    phases.saved[idx] = tmp;
    trail.push_back(lit);                  // gate_id * val
#ifdef LOGGING
    if (!assign_level)
        LOG ("root-level unit assign %d @ 0", lit);
    else
        LOG (reasons, "search assign %d @ %d", lit, lit_level);
#endif

    if (circuit_watching()) {
        const Circuit_Watches &ws = circuit_watches (lit);
        if (!ws.empty ()) {
            const Circuit_Watch &w = ws[0];
            __builtin_prefetch (&w, 0, 1);
        }
    }
}

/**
 * @note    propagate.cpp:      assign_unit()
 */
void Internal::circuit_assign_unit(int lit) {
    assert(!level);
    circuit_search_assign(lit, nullptr, 0);
}

/**
 * @beief assign val for gate_id in decide
 * @note    propagate.cpp   search_assume_decision()
 * @param   lit (gate_id * val)
 */
void Internal::circuit_search_assume_decision(int lit) {
    assert (propagated == trail.size ());
    new_trail_level(lit);
    LOG ("search decide %d", lit);
    circuit_search_assign(lit, circuit_decision_reason, 0);
}

/**
 * @beief assign val for gate_id (uip) in analyze.
 * @note    propagate.cpp   search_assign_driving()
 * @param   lit (gate_id * val)
 */
void Internal::circuit_search_assign_driving(int lit, Circuit_Gate *reason, int reason_direct) {
    circuit_search_assign(lit, reason, reason_direct);
}

/**
 * @return      true: propagate success; false: generate conflict
 */
bool Internal::circuit_propagate() {
    START (propagate);
    
    int64_t before = propagated;
    while (!circuit_conflict_gate && !circuit_conflict_direct[0] &&
            propagated != trail.size()) {
        const int lit = trail[propagated++];

        // 1. Propagate direct
        const auto &dws = circuit_direct_watches(lit);
        for (const auto &direct : dws) {
            circuit_propagate_direct(lit, direct);
        }

        // 2. Propagate watch-list
        Circuit_Watches& ws = circuit_watches(lit);

        const circuit_const_watch_iterator eow = ws.end();
        circuit_watch_iterator j = ws.begin();
        circuit_const_watch_iterator i = j;

        while (i != eow) {

            const Circuit_Watch w = *j++ = *i++;
            const signed char b = circuit_val(w.blit);

            if (b < 0)
                continue;       // blocking literal is unwatch-value

            if (w.binary()) {
                if (b > 0) {    // blocking literal was assigned with watch-value: generate conflict
                    circuit_conflict_gate = w.gate;     // but continue ...
                } else {        // blocking literal is unassigned: generate assign with unwatch-value
                    circuit_search_assign(-w.blit, w.gate, 0);
                }
            } else {
                assert(w.gate->size > 2);
                if (circuit_conflict_gate || circuit_conflict_direct[0])
                    break;      // Stop if there was a binary conflict already.

                if (w.gate->garbage) {
                    j--;
                    continue;
                }

                circuit_literal_iterator lits = w.gate->begin();
                const int other = lits[0] ^ lits[1] ^ lit;
                const signed char u = circuit_val(other);
                if (u < 0) {    // Other was assigned with unwatch-value, no need to analyze. Can not generate assign or conflict.
                    j[-1].blit = other;
                } else {
                    const int size = w.gate->size;
                    const circuit_literal_iterator middle = lits + w.gate->pos;
                    const circuit_const_literal_iterator end = lits + size;
                    circuit_literal_iterator k = middle;

                    // Find replacement watch 'r' at position 'k' with value 'v'

                    int r = 0;
                    signed char v = 1;

                    while (k != end && (v = circuit_val(r = *k)) > 0)
                        k++;

                    if (v > 0) { // need second search starting at the head?
                        k = lits + 2;
                        assert(w.gate->pos <= size);
                        while (k != middle && (v = circuit_val(r = *k)) > 0)
                            k++;
                    }

                    w.gate->pos = (k - lits); // always save position
                    assert(lits + 2 <= k), assert(k <= w.gate->end());

                    if (v < 0) {        // Replacement is assigned with unwatch-value, so just replace blit.
                        j[-1].blit = r;
                    } else if (!v) {    // Found new unassigend replacement literal to be watched.

                        lits[0] = other;
                        lits[1] = r;
                        *k = lit;

                        circuit_watch_literal(r, lit, w.gate);

                        j--;            // Drop this watch from the watch list of 'lit'
                    } else if (!u) {    // Only other watched-line is unassigned: assign with unwatch-value
                        assert(v > 0);
                        circuit_search_assign(-other, w.gate, 0);
                    } else {            // All lines were asigned with watch-value: generate conflict.
                        assert(u > 0);
                        assert(v > 0);
                        circuit_conflict_gate = w.gate;
                        break;
                    }
                }
            }
        }

        if (j != i) {
            while (i != eow)
                *j++ = *i++;
            ws.resize(j - ws.begin());
        }
    }

    stats.propagations.search += (propagated - before);
    if (!circuit_conflict_gate && !circuit_conflict_direct[0]) {
        no_conflict_until = propagated;
    } else {
        if (stable)
            stats.stabconflicts++;
        stats.conflicts++;

        // The trail before the current decision level was conflict free.
        //
        no_conflict_until = control[level].trail;
    }

    STOP (propagate);
    return !circuit_conflict_gate && !circuit_conflict_direct[0];
}

/**
 * @brief called by circuit_propagate_direct_left()/circuit_propagate_direct_right()
 * 1. In circuit_propagate_direct_left() lit is output with unwatch-value, direct is input (for common and gate, output is 1 => input1/input2 is 1)
 *      (1) if input is unassigned, assigned with watch-value.
 *      (2) if input is assigned with unwatched-value, generate conflict.
 * 2. In circuit_propagate_direct_right() lit is input with unwatch-value, direct is output (for common and gate, input is 0 => output is 0)
 *      (1) if output is unassigned, assigned with watch-value.
 *      (2) if ouput is assigned with unwatched-value, generate conflict.
 */
inline void Internal::circuit_propagate_direct(int lit, int direct) {
    const signed char direct_val = circuit_val(direct);
    if (direct_val > 0) {
        // direct was assigned with watch-val: do nothing.
    } else if (!direct_val) {
        // direct unassigned: generate assign with watch-value
        circuit_search_assign(direct, nullptr, lit); 
    } else {
        // direct was assigned with unwatch-val: generate conflict.
        assert(direct_val < 0);
        circuit_conflict_direct = {lit, -direct};
    }
}

}
