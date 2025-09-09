#include "../src/internal.hpp"

namespace CaDiCaL {

/**
 * @beief:  get decide phase for gate_id
 * @note:   decide.cpp: decide_phase()
 * @param:  idx
 * @param:  target
 */
int Internal::circuit_decide_phase(int idx, bool target) {
    const int initial_phase = opts.phase ? 1 : -1;
    int phase = 0;
    if (force_saved_phase)
        phase = phases.saved[idx];
    if (!phase)
        phase = phases.forced[idx];
    if (!phase && opts.forcephase)
        phase = initial_phase;
    if (!phase && target)
        phase = phases.target[idx];
    if (!phase)
        phase = phases.saved[idx];

    if (!phase)
        phase = initial_phase;

    return phase * idx;
}

/**
 * @note: decide.cpp    likely_phase()
 */
int Internal::circuit_likely_phase(int idx) { return circuit_decide_phase(idx, false); }

/**
 * @brief:  check already satisfied or not.
 * @note:   decide.cpp: satisfied()
 */
bool Internal::circuit_satisfied() {
    if (num_assigned < (size_t) max_var)
        return false;
    assert(num_assigned == (size_t) max_var);
    if (propagated < trail.size ())
        return false;
    size_t assigned = num_assigned;
    return (assigned = (size_t) max_var);
}

/**
 * @brief:  search for the next decision and assign it
 * @note:   decide.cpp: decide()
 */
int Internal::circuit_decide() {
    assert(!circuit_satisfied());
    START (decide);

    int idx = next_decision_variable();

    const bool target = (opts.target > 1 || (stable && opts.target));
    int decision = circuit_decide_phase(idx, target);

    circuit_search_assume_decision(decision);
    stats.decisions++;

    STOP (decide);
    return 0;
}

}  // namespace CaDiCaL
