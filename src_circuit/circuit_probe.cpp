#include "../src/internal.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

/**
 * @note:   probe.cpp:  probing()
 */
bool Internal::circuit_probing () {
    if (!opts.probe)
        return false;
    if (!preprocessing && !opts.inprocessing)
        return false;
    if (preprocessing)
        assert (lim.preprocessing);
    if (stats.probingphases && last.probe.reductions == stats.reductions)
        return false;
    return lim.probe <= stats.conflicts;
}

/*------------------------------------------------------------------------*/

/**
 * @note:   probe.cpp:  get_parent_reason_literal()
 */
inline int Internal::circuit_get_parent_reason_literal(int lit) {
    const int idx = vidx(lit);
    int res = parents[idx];
    return res;
}

/**
 * @note:   probe.cpp:  set_parent_reason_literal()
 */
inline void Internal::circuit_set_parent_reason_literal(int lit, int reason) {
    const int idx = vidx(lit);
    parents[idx] = reason;
}

/*------------------------------------------------------------------------*/

/**
 * @note:   probe.cpp:  clean_probehbr_lrat()
 */
void Internal::circuit_clean_probehbr_lrat() {
    // TODO(taomengxia: 2025/02/20): maybe need to implement later
    return;
}

/**
 * @note:   probe.cpp:  init_probehbr_lrat()
 */
void Internal::circuit_init_probehbr_lrat() {
    // TODO(taomengxia: 2025/02/20): maybe need to implement later
    return;
}

/*------------------------------------------------------------------------*/

/**
 * @note:   probe.cpp:  probe_dominator()
 */
int Internal::circuit_probe_dominator (int a, int b) {
    require_mode (PROBE);
    int l = a, k = b;
    Var *u = &var(l), *v = &var(k);
    assert(u->level == 1), assert(v->level == 1);
    while (l != k) {
        if (u->trail > v->trail)
            swap(l, k), swap(u, v);
        if (!circuit_get_parent_reason_literal(l))
            return l;
        int parent = circuit_get_parent_reason_literal(k);
        assert(parent);
        v = &var(k = parent);
        assert(v->level == 1);
    }

    LOG ("dominator %d of %d and %d", l, a, b);
    return l; 
}

/**
 * @note:   probe.cpp:  hyper_binary_resolve()
 */
inline int Internal::circuit_hyper_binary_resolve (Circuit_Gate *reason) {
    require_mode (PROBE);
    assert (level == 1);
    assert (reason->size > 2);

    const circuit_const_literal_iterator end = reason->end();
    const int *lits = reason->literals;
    circuit_const_literal_iterator k;

    stats.hbrs++;
    stats.hbrsizes += reason->size;
    const int lit = lits[1];
    int dom = lit, non_root_level_literals = 0;
    for (k = lits + 2;  k != end; k++) {
        const int other = *k;
        if (!circuit_assign_level_get(other))
            continue;
        dom = circuit_probe_dominator(dom, other);
        non_root_level_literals++;
    }  
    circuit_probe_reason = reason;
    if (non_root_level_literals && opts.probehbr) {
        bool contained = false;
        for (k = lits + 1; !contained && k != end; k++)
            contained = (*k == dom);
        const bool red = !contained || reason->redundant;
        if (red)
            stats.hbreds++;
        LOG ("new %s hyper binary resolvent %d %d",
            (red ? "redundant" : "irredundant"), dom, lits[0]);
        assert(clause.empty());
        clause.push_back (dom);
        clause.push_back (lits[0]);
        Circuit_Gate *c = circuit_new_hyper_binary_resolved_clause(red, 2);
        circuit_probe_reason = c;
        if (red)
            c->hyper = true;
        clause.clear();
        if (contained) {
            stats.hbrsubs++;
            circuit_mark_garbage (reason);
        }
    }
    return dom;
}

/*------------------------------------------------------------------------*/

/**
 * @note:   probe.cpp:  probe_assign()
 */
inline void Internal::circuit_probe_assign(int lit, int parent) {
    require_mode (PROBE);
    int idx = vidx(lit);
    assert(!val(idx));
    assert (!flags (idx).eliminated () || !parent);
    assert (!parent || val (parent));
    Var &v = var(idx);
    v.level = level;
    v.trail = (int) trail.size();
    assert ((int) num_assigned < max_var);
    num_assigned++;
    v.circuit_reason = level ? circuit_probe_reason : nullptr;
    v.circuit_reason_direct = level ? circuit_probe_reason_direct : 0;
    circuit_probe_reason = nullptr, circuit_probe_reason_direct = 0;

    circuit_set_parent_reason_literal(lit, parent);
    if (!level)
        circuit_learn_unit_clause(lit);
    else
        assert (level == 1);
    const signed char tmp = sign(lit);
    circuit_set_val(idx, tmp);
    assert (val (lit) > 0);
    assert (val (-lit) < 0);
    trail.push_back (lit);

    // Do not save the current phase during inprocessing but remember the
    // number of units on the trail of the last time this literal was
    // assigned.  This allows us to avoid some redundant failed literal
    // probing attempts.  Search for 'propfixed' in 'probe.cpp' for details.
    //
    if (level)
        propfixed (lit) = stats.all.fixed;

    if (parent)
        LOG ("probe assign %d parent %d", lit, parent);
    else if (level)
        LOG ("probe assign %d probe", lit);
    else
        LOG ("probe assign %d negated failed literal UIP", lit);
}

void Internal::circuit_probe_assign_decision (int lit) {
    require_mode (PROBE);
    assert (!level);
    assert (propagated == trail.size ());
    level++;
    control.push_back (Level (lit, trail.size ()));
    circuit_probe_assign (lit, 0);
}

void Internal::circuit_probe_assign_unit (int lit) {
    require_mode (PROBE);
    assert (!level);
    assert (active (lit));
    circuit_probe_assign (lit, 0);
}

/*------------------------------------------------------------------------*/


/**
 * @note:   probe.cpp:  probe_lrat_for_units()
 */
inline void Internal::circuit_probe_lrat_for_units (int lit) {
    // TODO(taomengxia: 2025/02/20): maybe need to implement.
    (void)lit;
    return;
}


// This is essentially the same as 'propagate' except that we prioritize and
// always propagate binary clauses first (see our CPAIOR'13 paper on tree
// based look ahead), then immediately stop at a conflict and of course use
// 'probe_assign' instead of 'search_assign'.  The binary propagation part
// is factored out too.  If a new unit on decision level one is found we
// perform hyper binary resolution and thus actually build an implication
// tree instead of a DAG.  Statistics counters are also different.
/**
 * @note:   probe.cpp:  probe_propagate2()
 */
inline void Internal::circuit_probe_propagate2 () {
    require_mode (PROBE);
    while (propagated2 != trail.size()) {
        const int lit = trail[propagated2++];

        LOG ("probe propagating %d by direct", lit);
        const auto &dws = circuit_direct_watches(lit);
        for (const auto &direct : dws) {
            circuit_probe_propagate_direct(lit, direct);
        }

        LOG ("probe propagating %d over binary clauses", lit);
        Circuit_Watches &ws = circuit_watches(lit);
        for (const auto &w : ws) {
            if (!w.binary())
                continue;

            const signed char b = circuit_val(w.blit);
            if (b < 0)      // block literal was assigned with unwatch-value: do nothing
                continue;
            if (b > 0) {    // block literal was assigned with watch-value: generate conflict.
                circuit_conflict_gate = w.gate;
            } else {        // block literal was unassigned: generate assign.
                assert(!b);
                assert (!circuit_probe_reason && !circuit_probe_reason_direct);
                circuit_probe_reason = w.gate;
                circuit_probe_lrat_for_units(-w.blit);
                circuit_probe_assign(-w.blit, lit);
            }
        }
    }
}

/**
 * @brief:  see circuit_propagate_watch_list() in circuit_propagate.cpp
 */
void Internal::circuit_probe_propagate_watch_list(int lit) {
    auto &ws = circuit_watches(lit);
    size_t i = 0, j = 0;
    while (i != ws.size()) {
        const Circuit_Watch w = ws[j++] = ws[i++];
        if (w.binary())
            continue;

        const signed char b = circuit_val(w.blit);
        if (b < 0)      // blocking literal is unwatch-value
            continue;

        if (w.gate->garbage)
            continue;

        circuit_literal_iterator lits = w.gate->begin();
        const int other = lits[0] ^ lits[1] ^ lit;
        const signed char u = circuit_val(other);

        if (u < 0) {    // Other was assigned with unwatch-value, no need to analyze. Can not generate assign or conflict.
            ws[j - 1].blit = other;
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
                ws[j - 1].blit = r;
            } else if (!v) {    // Found new unassigend replacement literal to be watched.

                lits[0] = other;
                lits[1] = r;
                *k = lit;

                circuit_watch_literal(r, lit, w.gate);

                j--;            // Drop this watch from the watch list of 'lit'
            } else if (!u) {    // Only other watched-line is unassigned: assign with unwatch-value
                assert (v > 0);
                if (level == 1) {
                    lits[0] = other, lits[1] = lit;
                    int dom = circuit_hyper_binary_resolve(w.gate);
                    circuit_probe_assign(-other, dom);
                } else {
                    assert(!circuit_probe_reason && !circuit_probe_reason_direct);
                    circuit_probe_reason = w.gate;
                    circuit_probe_assign_unit(-other);
                }
                circuit_probe_propagate2();
            } else {            // All lines were asigned with watch-value: generate conflict.
                assert(u > 0);
                assert(v > 0);
                circuit_conflict_gate = w.gate;
            }
        }
    }
    if (j != i) {
        while (i != ws.size())
            ws[j++] = ws[i++];
        ws.resize(j);
    }
}

/**
 * @brief:  see circuit_propagate_direct_internal() in circuit_propagate.cpp
 */
void Internal::circuit_probe_propagate_direct(int lit, int direct) {
    const signed char direct_val = circuit_val(direct);
    if (direct_val > 0) {
        // direct was assigned with watch-val: do nothing.
    } else if (!direct_val) {
        // direct unassigned: generate assign with watch-value.
        assert(!circuit_probe_reason && !circuit_probe_reason_direct);
        circuit_probe_reason_direct = lit;
        if (level == 1) {
            circuit_probe_assign(direct, lit);
        } else {
            circuit_probe_assign_unit(direct);
        }
    } else {
        assert(direct_val < 0);
        // direct was assigned with unwatch-value: generate conflict.
        circuit_conflict_direct = {lit, -direct};
    }
}

/**
 * @note:   probe.cpp:  probe_propagate()
 */
bool Internal::circuit_probe_propagate () {
    require_mode(PROBE);
    assert (!unsat);
    START (propagate);
    int64_t before = propagated2 = propagated;
    while (!circuit_conflict_gate && !circuit_conflict_direct[0]) {
        if (propagated2 != trail.size()) {
            circuit_probe_propagate2();
        } else if (propagated != trail.size()) {
            const auto lit = trail[propagated++];
            circuit_probe_propagate_watch_list(lit);
        } else {
            break;
        }
    }
    int64_t delta = propagated2 - before;
    stats.propagations.probe += delta;
    STOP (propagate);
    bool has_conflict = circuit_conflict_gate || circuit_conflict_direct[0];
    return !has_conflict;
}

/*------------------------------------------------------------------------*/

// This a specialized instance of 'analyze'.

void Internal::circuit_failed_literal (int failed) {
    LOG ("analyzing failed literal probe %d", failed);
    stats.failed++;
    stats.probefailed++;

    assert(!unsat);
    assert(level == 1);

    START (analyze);

    int uip = 0;
    auto process_conflict_literals_array = [&](const auto &array) {
        for (const auto &lit : array) {
            if (!circuit_assign_level_get(lit))
                continue;
            uip = uip ? circuit_probe_dominator(uip, lit) : lit;
        }
    };
    if (circuit_conflict_gate) {
        process_conflict_literals_array(*circuit_conflict_gate);
    } else {
        process_conflict_literals_array(circuit_conflict_direct);
    }

    LOG ("found probing UIP %d", uip);
    assert (uip);

    vector<int> work;

    int parent = uip;
    while (parent != failed) {
        const int next = circuit_get_parent_reason_literal (parent);
        parent = next;
        assert (parent);
        work.push_back (parent);
    }

    circuit_backtrack();
    circuit_conflict_clear();

    assert(!val(uip));
    circuit_probe_assign_unit(-uip);

    if (!circuit_probe_propagate())
        circuit_learn_empty_clause();

    size_t j = 0;
    while (!unsat && j < work.size ()) {
        // assert (!opts.probehbr);        assertion fails ...
        const int parent = work[j++];
        const signed char tmp = val (parent);
        if (tmp > 0) {
            assert (!opts.probehbr); // ... assertion should hold here
//            get_probehbr_lrat (parent, uip);
            LOG ("clashing failed parent %d", parent);
            circuit_learn_empty_clause ();
        } else if (tmp == 0) {
            assert (!opts.probehbr); // ... and here
            LOG ("found unassigned failed parent %d", parent);
//            get_probehbr_lrat (parent, uip); // this is computed during
            circuit_probe_assign_unit (-parent);     // propagation and can include
//            lrat_chain.clear ();             // multiple chains where only one
            if (!circuit_probe_propagate ())
                circuit_learn_empty_clause (); // is needed!
        }
        uip = parent;
    }
    work.clear ();
    erase_vector (work);

    STOP (analyze);

    assert (unsat || val (failed) < 0);
}

/*------------------------------------------------------------------------*/

/**
 * @note:   probe.cpp:  is_binary_clause()
 */
bool Internal::circuit_is_binary_gate(Circuit_Gate *g, int &a, int &b) {
    assert(!level);
    if (g->garbage)
        return false;
    int first = 0, second = 0;
    for (const auto &lit : *g) {
        const signed char tmp = circuit_val(lit);
        if (tmp < 0)    // value of lit is unwatch-value: already satisfied.
            return false;
        if (tmp > 0)    // value of lit is watched-value: lit is useless in this gate.
            continue;
        if (second)
            return false;
        if (first)
            second = lit;
        else
            first = lit;
    }

    if (!second)
        return false;
    a = first, b = second;
    return true;
}

/**
 * @note:   struct probe_negated_noccs_rank
 */
struct circuit_probe_noccs_rank {
    Internal *internal;
    circuit_probe_noccs_rank(Internal *i) : internal(i) {}
    typedef size_t Type;
    Type operator() (int a) const { return internal->noccs(a); }
};

inline void Internal::circuit_calculate_noccs_in_binary() {
    for (const auto &g : circuit_gates) {
        int a, b;
        if (!circuit_is_binary_gate(g, a, b))
            continue;
        noccs (a)++;    // binary: a ==> -b
        noccs (b)++;    // binary: b ==> -a
    }

    /// [Circuit specical]: treat direct watches
    for (auto idx : vars) {
        if (fixed(idx))
            continue;

        // idx ==> direct in circuit_direct_watches(idx)
        const auto &dws_pos = circuit_direct_watches(idx);
        const int cnt_pos = std::count_if(dws_pos.begin(), dws_pos.end(), [this](int direct) { return !fixed(direct); });
        noccs (idx) += cnt_pos;

        // -idx ==> direct in circuit_direct_watches(-idx)
        const auto &dws_neg = circuit_direct_watches(-idx);
        const int cnt_neg = std::count_if(dws_neg.begin(), dws_neg.end(), [this](int direct) { return !fixed(direct); });
        noccs (-idx) += cnt_neg;
    }
}

/**
 * @brief:  Fill the 'probes' schedule.
 * @note:   probe.cpp:  generate_probes()
 */
void Internal::circuit_generate_probes() {

    assert (probes.empty());

    // First determine all the literals which occur in binary clauses. It is
    // way faster to go over the clauses once, instead of walking the watch
    // lists for each literal.
    //
    init_noccs ();
    circuit_calculate_noccs_in_binary();

    for (auto idx : vars) {
        const bool have_pos_bin_occs = noccs (idx) > 0;
        const bool have_neg_bin_occs = noccs (-idx) > 0;

        if (have_pos_bin_occs == have_neg_bin_occs)
            continue;

        int probe = have_pos_bin_occs ? idx : -idx;     // watch value is pos, assign with watch_value

        // See the discussion where 'propfixed' is used below.
        //
        if (propfixed (probe) >= stats.all.fixed)
            continue;

        LOG ("scheduling probe %d negated occs %" PRId64 "", probe,
             noccs (-probe));
        probes.push_back (probe);
    }

    rsort(probes.begin(), probes.end(), circuit_probe_noccs_rank (this));

    reset_noccs();
    shrink_vector(probes);

    PHASE ("probe-round", stats.probingrounds,
           "scheduled %zd literals %.0f%%", probes.size (),
            percent (probes.size (), 2u * max_var));
}


/**
 * @brief:  Follow the ideas in 'generate_probes' but flush non root probes and reorder remaining probes.
 * @note:   probe.cpp:  flush_probes()
 */
void Internal::circuit_flush_probes () {

    assert (!probes.empty());

    init_noccs();
    circuit_calculate_noccs_in_binary();

    const auto eop = probes.end();
    auto j = probes.begin();
    for (auto i = j; i != eop; i++) {
        int lit = *i;

        if (!active(lit))
            continue;
        const bool have_pos_bin_occs = noccs (lit) > 0;
        const bool have_neg_bin_occs = noccs (-lit) > 0;
        if (have_pos_bin_occs == have_neg_bin_occs)
            continue;
        if (have_neg_bin_occs)
            lit = -lit;
        assert (!noccs (-lit)), assert (noccs (lit) > 0);
        if (propfixed (lit) >= stats.all.fixed)
            continue;
        LOG ("keeping probe %d negated occs %" PRId64 "", lit, noccs (-lit));
        *j++ = lit;
    }
    size_t remain = j - probes.begin();
#ifndef QUIET
    size_t flushed = probes.size () - remain;
#endif
    probes.resize(remain);

    rsort (probes.begin (), probes.end (), circuit_probe_noccs_rank (this));

    reset_noccs();
    shrink_vector (probes);

    PHASE ("probe-round", stats.probingrounds,
           "flushed %zd literals %.0f%% remaining %zd", flushed,
           percent (flushed, remain + flushed), remain);
}

/**
 * @note:   probe.cpp:  next_probe()
 */
int Internal::circuit_next_probe () {

    int generated = 0;
    for (;;) {

        if (probes.empty()) {
            if (generated++)
                return 0;
            circuit_generate_probes();
        }

        while (!probes.empty()) {

            int probe = probes.back();
            probes.pop_back();

            // Eliminated or assigned.
            //
            if (!active (probe))
                continue;

            // There is now new unit since the last time we propagated this probe,
            // thus we propagated it before without obtaining a conflict and
            // nothing changed since then.  Thus there is no need to propagate it
            // again.  This observation was independently made by Partik Simons
            // et.al. in the context of implementing 'smodels' (see for instance
            // Alg. 4 in his JAIR article from 2002) and it has also been
            // contributed to the thesis work of Yacine Boufkhad.
            //
            if (propfixed (probe) >= stats.all.fixed)
                continue;

            return probe;
        }
    }
}

/**
 * @note:   probe.cpp:  probe_round()
 */
bool Internal::circuit_probe_round () {

    if (unsat)
        return false;
    if (terminated_asynchronously ())
        return false;

    START_SIMPLIFIER (probe, PROBE);
    stats.probingrounds++;

    // Probing is limited in terms of non-probing propagations
    // 'stats.propagations'. We allow a certain percentage 'opts.probereleff'
    // (say %5) of probing propagations in each probing with a lower bound of
    // 'opts.probmineff'.
    //
    int64_t delta = stats.propagations.search;
    delta -= last.probe.propagations;
    delta *= 1e-3 * opts.probereleff;
    if (delta < opts.probemineff)
        delta = opts.probemineff;
    if (delta > opts.probemaxeff)
        delta = opts.probemaxeff;
    delta += 2l * active ();

    PHASE ("probe-round", stats.probingrounds,
           "probing limit of %" PRId64 " propagations ", delta);

    int64_t limit = stats.propagations.probe + delta;

    int old_failed = stats.failed;
#ifndef QUIET
    int64_t old_probed = stats.probed;
#endif
    int64_t old_hbrs = stats.hbrs;


    if (!probes.empty ())
        circuit_flush_probes ();

    // We reset 'propfixed' since there was at least another conflict thus
    // a new learned clause, which might produce new propagations (and hyper
    // binary resolvents).  During 'generate_probes' we keep the old value.
    //
    for (auto idx : vars)
        propfixed (idx) = propfixed (-idx) = -1;

    assert (unsat || propagated == trail.size ());
    propagated = propagated2 = trail.size ();

    int probe;
    circuit_init_probehbr_lrat();
    while (!unsat && !terminated_asynchronously () &&
            stats.propagations.probe < limit && (probe = circuit_next_probe ())) {
        stats.probed++;
        LOG ("probing %d", probe);
        circuit_probe_assign_decision (probe);
        if (circuit_probe_propagate ())
            circuit_backtrack ();
        else
            circuit_failed_literal (probe);
        circuit_clean_probehbr_lrat ();
    }

    if (unsat)
        LOG ("probing derived empty clause");
    else if (propagated < trail.size()) {
        LOG ("probing produced %zd units",
            (size_t) (trail.size () - propagated));
        if (!circuit_propagate ()) {
            LOG ("propagating units after probing results in empty clause");
            circuit_learn_empty_clause ();
        } else
            circuit_sort_watches ();
    }

    int failed = stats.failed - old_failed;
#ifndef QUIET
    int64_t probed = stats.probed - old_probed;
#endif
    int64_t hbrs = stats.hbrs - old_hbrs;

    PHASE ("probe-round", stats.probingrounds,
           "probed %" PRId64 " and found %d failed literals", probed, failed);

    if (hbrs)
        PHASE ("probe-round", stats.probingrounds,
               "found %" PRId64 " hyper binary resolvents", hbrs);

    STOP_SIMPLIFIER (probe, PROBE);

    report ('p', !opts.reportall && !(unsat + failed + hbrs));

    return !unsat && failed;
}

/*------------------------------------------------------------------------*/

/**
 * @note:   probe.cpp:  probe()
 */
void Internal::circuit_probe (bool update_limits) {
    if (unsat)
        return;
    if (level)
        circuit_backtrack();
    if (!circuit_propagate()) {
        circuit_learn_empty_clause();
        return;
    }

    stats.probingphases++;
    if (external_prop) {
        assert(!level);
        private_steps = true;
    }
    const int before = active (); 

    // We trigger equivalent literal substitution (ELS) before ...
    //
    circuit_decompose ();

    if (circuit_ternary ()) // If we derived a binary clause
        circuit_decompose (); // then start another round of ELS.

    // Remove duplicated binary clauses and perform in essence hyper unary
    // resolution, i.e., derive the unit '2' from '1 2' and '-1 2'.
    //
    circuit_mark_duplicated_binary_clauses_as_garbage ();

    for (int round = 1; round <= opts.proberounds; round++)
        if (!circuit_probe_round ())
        break;

    circuit_decompose (); // ... and (ELS) afterwards.    

    last.probe.propagations = stats.propagations.search;

    if (external_prop) {
        assert(!level);
        private_steps = false;
    }

    if (!update_limits)
        return;

    const int after = active ();
    const int removed = before - after;
    assert (removed >= 0);

    if (removed) {
        stats.probesuccess++;
        PHASE ("probe-phase", stats.probingphases,
               "successfully removed %d active variables %.0f%%", removed,
               percent (removed, before));
    } else
        PHASE ("probe-phase", stats.probingphases,
               "could not remove any active variable");

    const int64_t delta = opts.probeint * (stats.probingphases + 1);
    lim.probe = stats.conflicts + delta;

    PHASE ("probe-phase", stats.probingphases,
           "new limit at %" PRId64 " conflicts after %" PRId64 " conflicts",
           lim.probe, delta);

    last.probe.reductions = stats.reductions;
}

} // namespace CaDiCaL
