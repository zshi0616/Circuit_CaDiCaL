#include "../src/internal.hpp"

namespace CaDiCaL {

/**
 * @brief:  check need reduce or not
 * @note:   reduce.cpp: reducing()
 */
bool Internal::circuit_reducing() {
    if (!opts.reduce)
        return false;
    if (!stats.current.redundant)
        return false;
    return stats.conflicts >= lim.reduce;
}

/**
 * @brief:  Gates of larger glue or larger size are considered less useful
 * @note:   reduce.cpp: reduce_less_useful
 */
struct circuit_reduce_less_useful {
    bool operator() (const Circuit_Gate* a, const Circuit_Gate* b) const {  
        if (a->glue > b->glue)
            return true;
        if (a->glue < b->glue)
            return false;
        return a->size > b->size;
    }
};

/**
 * @brief:  Mark useless redundant gates as garbag.
 * @note:   reduce.cpp: mark_useless_redundant_clauses_as_garbage()
 */
void Internal::circuit_mark_useless_redundant_gates_as_garbage() {
    vector<Circuit_Gate*> stack;

    stack.reserve(stats.current.redundant);

    for (const auto &c : circuit_gates) {
        assert (c);
        if (!c->redundant)          // Keep irredundant.
            continue;
        if (c->garbage)             // Skip already marked.
            continue;
        if (c->reason)
            continue;               // Need to keep reasons.

#if 0 // TODO(taomengxia)
        const unsigned used = c->used;
        if (used)
            c->used--;
        if (c->hyper) {          // Hyper binary and ternary resolvents
            assert (c->size <= 3); // are only kept for one reduce round
            if (!used)
                circuit_mark_garbage (c); // (even if 'c->keep' is true) unless
            continue;           //  used recently.
        }
        if (used)
            continue;               // Do keep recently used gates.
#endif
        if (c->keep)
            continue;               // Forced to keep

        stack.push_back(c);
    }

    stable_sort(stack.begin(), stack.end(), circuit_reduce_less_useful());

    size_t target = 1e-2 * opts.reducetarget * stack.size();
    if (target > stack.size()) {
        target = stack.size();
    }

    PHASE ("reduce", stats.reductions, "reducing %zd clauses %.0f%%", target,
           percent (target, stats.current.redundant));

    auto i = stack.begin();
    const auto t = i + target;
    while (i != t) {
        Circuit_Gate* c = *i++;
//        LOG (c, "marking useless to be collected");
        circuit_mark_garbage (c);
        stats.reduced++;
    }

    lim.keptsize = lim.keptglue = 0;

    const auto end = stack.end();
    for (i = t; i != end; i++) {
        Circuit_Gate *c = *i;
        if (c->size > lim.keptsize)
            lim.keptsize = c->size;
        if (c->glue > lim.keptglue)
            lim.keptglue = c->glue;
    }

    erase_vector(stack);

    PHASE ("reduce", stats.reductions, "maximum kept size %d glue %d",
        lim.keptsize, lim.keptglue);
}

/**
 * @brief:
 * @note:   reduce.cpp: propagate_out_of_order_units()
 */
bool Internal::circuit_propagate_out_of_order_units() {
    if (!level)
        return true;
    int oou = 0;
    for (size_t i = control[1].trail; !oou && i < trail.size(); i++) {
        const int lit = trail[i];
        if (circuit_assign_level_get(lit))
            continue;
        LOG ("found out-of-order assigned unit %d", oou);
        oou = lit;
    }
    if (!oou)
        return true;
    assert(opts.chrono);
    circuit_backtrack(0);
    if (circuit_propagate())
        return true;
    circuit_learn_empty_clause();
    return false;
}

/**
 * @brief:  Reduce the learnt gate
 * @note:   reduce.cpp: reduce()
 */
void Internal::circuit_reduce() {
    START (reduce);

    stats.reductions++;
    report ('.', 1);

    if (!circuit_propagate_out_of_order_units())
        goto DONE;

    circuit_mark_satisfied_gates_as_garbage();
    circuit_protect_reasons();

    /// mark useless redundant gates as garbage
    circuit_mark_useless_redundant_gates_as_garbage();

    circuit_garbage_collection();

    /// recalculate reduce limit
    {
        int64_t delta = opts.reduceint * (stats.reductions + 1);
        if (irredundant () > 1e5) {
            delta *= log (irredundant () / 1e4) / log (10);
            if (delta < 1)
                delta = 1;
        }
        lim.reduce = stats.conflicts + delta;
        PHASE ("reduce", stats.reductions,
               "new reduce limit %" PRId64 " after %" PRId64 " conflicts",
               lim.reduce, delta);
    }

    last.reduce.conflicts = stats.conflicts;

DONE:

    STOP (reduce);
}

}
