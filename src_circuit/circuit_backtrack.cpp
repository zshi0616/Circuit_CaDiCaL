#include "../src/internal.hpp"

namespace CaDiCaL {

/**
 * @brief:  Unassign for gate_id
 * @note:   backtrack.cpp: unassign()
 * @param:  lit     gate_id * val
 */
inline void Internal::circuit_unassign(int lit) {
    assert(val(lit) > 0);
    circuit_set_val (lit, 0);
    int idx = vidx(lit);

    LOG ("unassign %d @ %d", lit, var (idx).level);
    num_assigned--;

    if (!scores.contains (idx))
        scores.push_back (idx);

    if (queue.bumped < btab[idx])
        update_queue_unassigned (idx);
}

/**
 * @brief:  Backtrack to new_level
 * @note:   backtrack.cpp: backtrack()
 * @param:  new_level
 */
void Internal::circuit_backtrack(int new_level) {
    assert(new_level <= level);
    if (new_level == level)
        return;

    stats.backtracks++;
    update_target_and_best();

    assert (num_assigned == trail.size());

    const size_t assigned = control[new_level + 1].trail;

    LOG ("backtracking to decision level %d with decision %d and trail %zd",
         new_level, control[new_level].decision, assigned);

    const size_t end_of_trail = trail.size();
    size_t i = assigned, j = i;

#ifdef LOGGING
    int unassigned = 0;
#endif
    int reassigned = 0;

    while (i < end_of_trail) {
        int lit = trail[i++];
        Var& v = var(lit);
        if (v.level > new_level) {
            circuit_unassign(lit);
#ifdef LOGGING
            unassigned++;
#endif
        } else {
            assert(opts.chrono);
#ifdef LOGGING
            if (!v.level)
                LOG ("reassign %d @ 0 unit clause %d", lit, lit);
            else
                LOG (v.reason, "reassign %d @ %d", lit, v.level);
#endif
            trail[j] = lit;
            v.trail = j++;
            reassigned++;
        }
    }
    trail.resize(j);
    LOG ("unassigned %d literals %.0f%%", unassigned, percent (unassigned, unassigned + reassigned));
    LOG ("reassigned %d literals %.0f%%", reassigned, percent (reassigned, unassigned + reassigned));

    if (propagated > assigned)
        propagated = assigned;
    if (no_conflict_until > assigned)
        no_conflict_until = assigned;

    control.resize(new_level + 1);
    level = new_level;
    assert (num_assigned == trail.size());
}

} // namespace CaDiCaL
