#include "../src/internal.hpp"

namespace CaDiCaL {

/// @note:   subsume.cpp:    subsuming()
bool Internal::circuit_subsuming() {
#if 0  // TODO(taomengxia: 2025/02/28) need support vivify later
    if (!opts.subsume && !opts.vivify)
        return false;
#else
    if (!opts.subsume)
        return false;
#endif
    if (!preprocessing && !opts.inprocessing)
        return false;
    if (preprocessing)
        assert (lim.preprocessing);

    // Only perform global subsumption checking immediately after a clause
    // reduction happened where the overall allocated memory is small and we
    // got a limit on the number of kept clause in terms of size and glue.
    //
    if (opts.reduce && stats.conflicts != last.reduce.conflicts)
        return false;

    if (stats.conflicts < lim.subsume)
        return false;

    return true; 
}

/// @note:   subsume.cpp:    subsume_check()
inline int Internal::circuit_subsume_check(Circuit_Gate *subsuming, Circuit_Gate *subsumed) {
#ifdef NDEBUG
    (void) subsumed;
#endif
    assert (!subsumed->garbage);
    assert (!subsuming->garbage);
    assert (subsuming != subsumed);
    assert (subsuming->size <= subsumed->size);

    stats.subchecks++;
    if (subsuming->size == 2)
        stats.subchecks2++;
    
    int flipped = 0, prev = 0;
    bool failed = false;
    const auto eoc = subsuming->end();
    for (auto i = subsuming->begin(); !failed && i != eoc; i++) {
        int lit = *i;
        *i = prev;
        prev = lit;
        const int tmp = marked(lit);
        if (!tmp)
            failed = true;
        else if (tmp > 0)
            continue;
        else if (flipped)
            failed = true;
        else
            flipped = lit;
    }
    assert (prev);
    assert (!subsuming->literals[0]);
    subsuming->literals[0] = prev;

    if (failed)
        return 0;
    
    if (!flipped)
        return INT_MIN;    // subumed!!
    else if (!opts.subsumestr)
        return 0;
    else 
        return flipped;     // strengthen!!
}

/*------------------------------------------------------------------------*/

/// @note:   subsume.cpp:    subsume_clause()
inline void Internal::circuit_subsume_clause(Circuit_Gate *subsuming, Circuit_Gate *subsumed) {
    stats.subsumed++;
    assert (subsuming->size <= subsumed->size);
    LOG (subsumed, "subsumed");
    if (subsumed->redundant)
        stats.subred++;
    else
        stats.subirr++;
    if (subsumed->redundant || !subsuming->redundant) {
        circuit_mark_garbage(subsumed);
        return;
    }
    LOG ("turning redundant subsuming clause into irredundant clause");
    subsuming->redundant = false;
    circuit_mark_garbage(subsumed);
    stats.current.irredundant++;
    stats.added.irredundant++;
    stats.irrlits += subsuming->size;
    assert (stats.current.redundant > 0);
    stats.current.redundant--;
    assert (stats.added.redundant > 0);
    stats.added.redundant--;
}

/*------------------------------------------------------------------------*/

/// @note:   subsume.cpp:    strengthen_clause()
void Internal::circuit_strengthen_clause(Circuit_Gate *c, int lit) {
    stats.strengthened++;
    assert(c->size > 2);
    
    auto new_end = remove(c->begin(), c->end(), lit);
    assert (new_end + 1 == c->end ()), (void) new_end;
    (void)circuit_shrink_gate(c, c->size - 1);
}

/// @note:   subsume.cpp:    try_to_subsume_clause()
inline int Internal::circuit_try_to_subsume_clause(Circuit_Gate *c, vector<Circuit_Gate*> &shrunken) {
    stats.subtried++;
    assert (!level);

    circuit_mark(c); // signed!

    Circuit_Gate *d = nullptr;
    int flipped = 0;

    for (const auto &lit : *c) {
        if (!flags(lit).subsume)
            continue;

        for (int sign = 1; !d && sign >= -1; sign -= 2) {

            for (const auto &bin : circuit_bins(sign * lit)) {
                const auto &other = bin.lit;
                const int tmp = marked(other);
                if (!tmp)
                    continue;
                if (tmp < 0 && sign < 0)
                    continue;
                if (tmp < 0) {
                    if (sign < 0)
                        continue;
                    flipped = other;
                } else {
                    flipped = (sign < 0) ? -lit : INT_MIN;
                }
                d = bin.gate;

                break;
            }

            if (d)
                break;

            const Circuit_Occs &os = circuit_occs(sign * lit);
            for (const auto &e : os) {
                assert(!e->garbage);
                flipped = circuit_subsume_check(e, c);
                if (!flipped)
                    continue;
                d = e;
                break;
            }
        }
        if (d)
            break;
    }

    circuit_unmark(c);
    
    if (flipped == INT_MIN) {
        circuit_subsume_clause(d, c);
        return 1;
    }

    if (flipped) {
        circuit_strengthen_clause(c, -flipped);
        shrunken.push_back(c);
        return -1;
    }

    return 0;
}

struct GateSize {
    size_t size;
    Circuit_Gate *gate;
    GateSize(int s, Circuit_Gate *c) : size(s), gate(c) {}
    GateSize() {}
};

struct circuit_smaller_clause_size_rank{
    typedef size_t Type;
    Type operator() (const GateSize &a) { return a.size; }
};

struct circuit_subsume_less_noccs {
    Internal *internal;
    circuit_subsume_less_noccs(Internal *i) : internal(i) {};
    bool operator() (int a, int b) {
        const signed char u = internal->circuit_val(a), v = internal->circuit_val(b);
        if (!u && v)
            return true;
        if (u && !v)
            return false;
        
        const int64_t m = internal->noccs (a), n = internal->noccs (b);
        if (m < n)
            return true;
        if (m > n)
            return false;
        return abs(a) < abs(b);
    }
};

/// @note:   subsume.cpp:    subsume_round()
bool Internal::circuit_subsume_round() {
    if (!opts.subsume)
        return false;
    if (unsat)
        return false;
    if (terminated_asynchronously ())
        return false;
    if (!stats.current.redundant && !stats.current.irredundant)
        return false;

    START_SIMPLIFIER (subsume, SUBSUME);
    stats.subsumerounds++;

    int64_t check_limit;
    if (opts.subsumelimited) {
        int64_t delta = stats.propagations.search;
        delta *= 1e-3 * opts.subsumereleff;
        if (delta < opts.subsumemineff)
        delta = opts.subsumemineff;
        if (delta > opts.subsumemaxeff)
        delta = opts.subsumemaxeff;
        delta = max (delta, (int64_t) 2l * active ());

        PHASE ("subsume-round", stats.subsumerounds,
            "limit of %" PRId64 " subsumption checks", delta);

        check_limit = stats.subchecks + delta;
    } else {
        PHASE ("subsume-round", stats.subsumerounds,
            "unlimited subsumption checks");
        check_limit = LONG_MAX;
    }

    int old_marked_candidate_variables_for_elimination = stats.mark.elim;

    assert(!level);

    // Allocate schedule and occurrence lists.
    //
    vector<GateSize> schedule;
    init_noccs ();

    // Determine candidate clauses and sort them by size.
    //
    int64_t left_over_from_last_subsumption_round = 0;

    for (auto c : circuit_gates) {
        if (c->garbage)
            continue;
        if (c->size > opts.subsumeclslim)
            continue;
        if (!circuit_likely_to_be_kept_clause(c))
            continue;

        bool fixed = false;
        int subsume = 0;
        for (const auto &lit : *c)
            if (circuit_val(lit))
                fixed = true;
            else if (flags(lit).subsume)
                subsume++;

        // If the clause contains a root level assigned (fixed) literal we will
        // not work on it.  This simplifies the code substantially since we do
        // not have to care about assignments at all.  Strengthening becomes
        // much simpler too.
        //
        if (fixed) {
            continue;
        }

        // Further, if less than two variables in the clause were added since
        // the last subsumption round, the clause is ignored too.
        //
        if (subsume < 2) {
            continue;
        }

        if (c->subsume)
            left_over_from_last_subsumption_round++;
        schedule.push_back(GateSize(c->size, c));
        for (const auto &lit : *c)
            noccs(lit)++; 
    }
    shrink_vector(schedule);

    // Smaller clauses are checked and connected first.
    //
    rsort (schedule.begin (), schedule.end (), circuit_smaller_clause_size_rank ());

    if (!left_over_from_last_subsumption_round)
        for (auto cs : schedule)
            if (cs.gate->size > 2)
                cs.gate->subsume = true;

#ifndef QUIET
    int64_t scheduled = schedule.size ();
    int64_t total = stats.current.irredundant + stats.current.redundant;
    PHASE ("subsume-round", stats.subsumerounds,
           "scheduled %" PRId64 " clauses %.0f%% out of %" PRId64 " clauses",
           scheduled, percent (scheduled, total), total);
#endif

    // Now go over the scheduled clauses in the order of increasing size and
    // try to forward subsume and strengthen them. Forward subsumption tries
    // to find smaller or same size clauses which subsume or might strengthen
    // the candidate.  After the candidate has been processed connect one
    // of its literals (with smallest number of occurrences at this point) in
    // a one-watched scheme.

    int64_t subsumed = 0, strengthened = 0, checked = 0;

    vector<Circuit_Gate *> shrunken;
    circuit_init_occs();
    circuit_init_bins();

    for (const auto &s : schedule) {
        if (terminated_asynchronously ())
            break;
        if (stats.subchecks >= check_limit)
            break;
        
        Circuit_Gate *c = s.gate;
        assert(!c->garbage);

        checked++;

        if (c->size > 2 && c->subsume) {
            c->subsume = false;
            const int tmp = circuit_try_to_subsume_clause(c, shrunken);
            if (tmp > 0) {
                subsumed++;
                continue;
            }
            if (tmp < 0)
                strengthened++;
        }

        // If not subsumed connect smallest occurring literal, where occurring
        // means the number of times it was used to connect (as a one-watch) a
        // previous smaller or equal sized clause.  This minimizes the length of
        // the occurrence lists traversed during 'try_to_subsume_clause'. Also
        // note that this number is usually way smaller than the number of
        // occurrences computed before and stored in 'noccs'.
        //
        int minlit = 0;
        int64_t minoccs = 0;
        size_t minsize = 0;
        bool subsume = true;
        bool binary = (c->size == 2 && !c->redundant);

        for (const auto &lit : *c) {

            if (!flags (lit).subsume)
                subsume = false;
            const size_t size = binary ? circuit_bins(lit).size() : circuit_occs (lit).size ();
            if (minlit && minsize <= size)
                continue;
            const int64_t tmp = noccs (lit);
            if (minlit && minsize == size && tmp <= minoccs)
                continue;
            minlit = lit, minsize = size, minoccs = tmp;
        }

        // If there is a variable in a clause different from is not 'subsume'
        // (has been added since the last subsumption round), then this clause
        // can not serve to strengthen or subsume another clause, since all
        // shrunken or added clauses mark all their variables as 'subsume'.
        //
        if (!subsume)
            continue;

        if (!binary) {

            // If smallest occurring literal occurs too often do not connect.
            //
            if (minsize > (size_t) opts.subsumeocclim)
                continue;

            circuit_occs(minlit).push_back(c);
            // This sorting should give faster failures for assumption checks
            // since the less occurring variables are put first in a clause and
            // thus will make it more likely to be found as witness for a clause
            // not to be subsuming.  One could in principle (see also the
            // discussion on 'subsumption' in our 'Splatz' solver) replace marking
            // by a kind of merge sort, as also suggested by Bayardo.  It would
            // avoid 'marked' calls and thus might be slightly faster but could
            // not take benefit of this sorting optimization.
            //
            sort (c->begin (), c->end (), circuit_subsume_less_noccs (this));
        } else {
            // If smallest occurring literal occurs too often do not connect.
            //
            if (minsize > (size_t) opts.subsumebinlim)
                continue;

            const int minlit_pos = (c->literals[1] == minlit);
            const int other = c->literals[!minlit_pos];
            circuit_bins(minlit).push_back(Circuit_Bin{other, c});
        }
    }

    PHASE ("subsume-round", stats.subsumerounds,
           "subsumed %" PRId64 " and strengthened %" PRId64 " out of %" PRId64
           " clauses %.0f%%",
           subsumed, strengthened, scheduled,
           percent (subsumed + strengthened, scheduled));

    const int64_t remain = schedule.size () - checked;
    const bool completed = !remain;

    if (completed)
        PHASE ("subsume-round", stats.subsumerounds,
            "checked all %" PRId64 " scheduled clauses", checked);
    else
        PHASE ("subsume-round", stats.subsumerounds,
            "checked %" PRId64 " clauses %.0f%% of scheduled (%" PRId64
            " remain)",
            checked, percent (checked, scheduled), remain);

    // Release occurrence lists and schedule.
    //
    erase_vector (schedule);
    reset_noccs ();
    circuit_reset_occs ();
    circuit_reset_bins ();

    // Reset all old 'added' flags and mark variables in shrunken
    // clauses as 'added' for the next subsumption round.
    //
    if (completed)
        reset_subsume_bits ();

    for (const auto &c : shrunken)
        circuit_mark_added (c);
    erase_vector (shrunken);

    report ('s', !opts.reportall && !(subsumed + strengthened));

    STOP_SIMPLIFIER (subsume, SUBSUME);

    return old_marked_candidate_variables_for_elimination < stats.mark.elim;
}

/*------------------------------------------------------------------------*/

/// @note:   subsume.cpp:    subsume()
void Internal::circuit_subsume (bool update_limits) {
    stats.subsumephases++;
    if (!stats.current.redundant && !stats.current.irredundant)
        goto UPDATE_LIMITS;

    if (unsat)
        return;
    
    circuit_backtrack();
    if (!circuit_propagate()) {
        circuit_learn_empty_clause();
        return;
    }

    if (external_prop) {
        assert(!level);
        private_steps = true;
    }

    if (opts.subsume) {
        circuit_reset_watches ();
        circuit_subsume_round ();
        circuit_init_watches ();
        circuit_connect_watches ();
        if (!unsat && !circuit_propagate ()) {
            LOG ("propagation after subsume rounds results in inconsistency");
            circuit_learn_empty_clause ();
        }
    }

#if 0   // TODO(taomengxia: 20250225)
    // Schedule 'vivification' in 'subsume' as well as 'transitive reduction'.
    //
    if (opts.vivify)
        vivify ();
#endif
    if (opts.transred)
        circuit_transred ();

    if (external_prop) {
        assert(!level);
        private_steps = false;
    }

UPDATE_LIMITS:

    if (!update_limits)
        return;

    int64_t delta = scale (opts.subsumeint * (stats.subsumephases + 1));
    lim.subsume = stats.conflicts + delta;

    PHASE ("subsume-phase", stats.subsumephases,
            "new subsume limit %" PRId64 " after %" PRId64 " conflicts",
            lim.subsume, delta);
}

} // namespace CaDiCaL