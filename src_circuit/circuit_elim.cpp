#include "../src/internal.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

/**
 * @note:   elim.cpp:   eliminating()
 */
bool Internal::circuit_eliminating() {

    if (!opts.elim)
        return false;
    if (!preprocessing && !opts.inprocessing)
        return false;
    if (preprocessing)
        assert (lim.preprocessing);

    // Respect (increasing) conflict limit.
    //
    if (lim.elim >= stats.conflicts)
        return false;

    // Wait until there are new units or new removed variables
    // (in removed or shrunken irredundant clauses and thus marked).
    //
    if (last.elim.fixed < stats.all.fixed)
        return true;
    if (last.elim.marked < stats.mark.elim)
        return true;

    return false;
}

/*------------------------------------------------------------------------*/

/**
 * @note:   elim.cpp:   elim()
 */
void Internal::circuit_elim (bool update_limits) {
    if (unsat)
        return;
    if (level)
        circuit_backtrack ();
    if (!circuit_propagate ()) {
        circuit_learn_empty_clause ();
        return;
    }

    stats.elimphases++;
    PHASE ("elim-phase", stats.elimphases,
           "starting at most %d elimination rounds", opts.elimrounds);

    if (external_prop) {
        assert(!level);
        private_steps = true;
    }

#ifndef QUIET
    int old_active_variables = active ();
    int old_eliminated = stats.all.eliminated;
#endif

    // TODO(taomengxia:2025/02/20: main elim need support later)


#ifndef QUIET
    int eliminated = stats.all.eliminated - old_eliminated;
    PHASE ("elim-phase", stats.elimphases, "eliminated %d variables %.2f%%",
            eliminated, percent (eliminated, old_active_variables));
#endif

    if (external_prop) {
        assert(!level);
        private_steps = false;
    }

    if (!update_limits)
        return;

    int64_t delta = scale (opts.elimint * (stats.elimphases + 1));
    lim.elim = stats.conflicts + delta;

    PHASE ("elim-phase", stats.elimphases,
            "new limit at %" PRId64 " conflicts after %" PRId64 " conflicts",
            lim.elim, delta);

    last.elim.fixed = stats.all.fixed;
}

} // namespace CaDiCaL