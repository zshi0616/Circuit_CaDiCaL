#include "../src/internal.hpp"

namespace CaDiCaL {

/**
 * @brief:
 * @note:   collect.cpp: clause_contains_fixed_literal()
 */
int Internal::gate_contains_fixed_literal(Circuit_Gate* gate) {
    int watched = 0, unwatched = 0;
    for (const auto &lit : *gate) {
        const int tmp = fixed(lit);
        if (tmp > 0) {
            watched++;
        } else if (tmp < 0) {
            unwatched++;
        }
    }

    if (unwatched) {
        return 1;
    } else if (watched) {
        return -1;
    } else {
        return 0;
    }
}

/**
 * @brief:  remove fixed inputs with watch-value
 * @note:   collect.cpp: remove_falsified_literals()
 */
void Internal::circuit_remove_watched_literals(Circuit_Gate* g) {
    const circuit_literal_iterator end = g->end();
    circuit_const_literal_iterator i;
    int num_non_watched = 0;
    for (i = g->begin (); num_non_watched < 2 && i != end; i++)
        if (fixed (*i) <= 0)
            num_non_watched++;
    if (num_non_watched < 2)
        return;

    circuit_literal_iterator j = g->begin();
    for (i = j; i != end; i++) {
        const int lit = *j++ = *i;
        const int tmp = fixed(lit);
        assert (tmp >= 0);
        if (tmp <= 0)
            continue;
        LOG ("flushing %d", lit);
        j--;
    }

    stats.collected += circuit_shrink_gate(g, j - g->begin());
}

/**
 * @brief:  mark satisfied gates as garbage
 * @note:   collect.cpp: mark_satisfied_clauses_as_garbage()
 */
void Internal::circuit_mark_satisfied_gates_as_garbage() {
    if (last.collect.fixed >= stats.all.fixed)
        return;
    last.collect.fixed = stats.all.fixed;

    LOG ("marking satisfied gates");

    for (const auto &g : circuit_gates) {
        if (g->garbage)
            continue;
        
        const int tmp = gate_contains_fixed_literal(g);
        if (tmp > 0) {
            // Exist line fixed with unwatch-value, in watch check of this gate:
            // the gate is useless(can not generate assign or conflict): mark garbage for this gate.
            circuit_mark_garbage(g);
        } else if (tmp < 0) {
            // Exist line fixed with unwatch-value, in watch check of this gate:
            // these lines are useless: delete these lines in this gate;
            circuit_remove_watched_literals(g);
        }
    }

    for (auto idx : vars) {
        circuit_flush_direct_watches(idx);
        circuit_flush_direct_watches(-idx);
    }
}

inline void Internal::circuit_flush_direct_watches(int lit) {
    auto &dws = circuit_direct_watches(lit);
    const auto end = dws.end();
    auto j = dws.begin();
    for (auto i = j; i != end; i++) {
        const int direct = *i;
        int direct_tmp = fixed(direct);
        if (direct_tmp > 0)
            continue;
        *j++ = direct;
    }
    dws.resize(j - dws.begin());
    shrink_vector(dws);
}

/**
 * @breief: Reason gate can not be collected
 * @note:   collect.cpp:    protect_reasons()
 */
void Internal::circuit_protect_reasons() {
    LOG ("protecting reason clauses of all assigned variables on trail");
    assert (!protected_reasons);
#ifdef LOGGING
    size_t count = 0;
#endif
    for (const auto &lit : trail) {
        if (!active(lit))
            continue;
        assert (val(lit));
        Var &v = var(lit);
        assert(v.level > 0);
        Circuit_Gate *reason = v.circuit_reason;
        if (!reason)
            continue;
        assert(!reason->reason);
        reason->reason = true;
#ifdef LOGGING
        count++;
#endif
    }
    LOG ("protected %zd reason clauses referenced on trail", count);
    protected_reasons = true;
}

/**
 * @brief:  After garbage collection reset the 'reason' flag of the reasons of assigned literals on the trail
 * @note:   collect.cpp:    unprotect_reasons();
 */
void Internal::circuit_unprotect_reasons() {
    LOG ("unprotecting reasons clauses of all assigned variables on trail");
    assert (protected_reasons);
#ifdef LOGGING
    size_t count = 0;
#endif
    for (const auto &lit : trail) {
        if (!active(lit))
            continue;
        assert (val(lit));
        Var &v = var(lit);
        assert(v.level > 0);
        Circuit_Gate *reason = v.circuit_reason;
        if (!reason)
            continue;
        assert(reason->reason);
        reason->reason = false;
#ifdef LOGGING
        count++;
#endif
    }
    LOG ("unprotected %zd reason clauses referenced on trail", count);
    protected_reasons = false;
}

/**
 * @brief:  Update watch lists before deleting garbage clauses int the context of 'reduce'
 * @note:   collect.cpp:    flush_watches()
 */
inline void Internal::circuit_flush_watches(int lit, Circuit_Watches &saved) {
    assert (saved.empty ());
    Circuit_Watches &ws = circuit_watches(lit);
    const circuit_const_watch_iterator end = ws.end();
    circuit_watch_iterator j = ws.begin();
    circuit_const_watch_iterator i;
    for (i = j; i != end; i++) {
        Circuit_Watch w = *i;
        Circuit_Gate *g = w.gate;
        if (g->collect())
            continue;
        if (g->moved)
            g = w.gate = g->copy;
        w.size = g->size;
        const int new_blit_pos = (g->literals[0] == lit);
        assert (g->literals[!new_blit_pos] == lit);
        w.blit = g->literals[new_blit_pos];
        if (w.binary())
            *j++ = w;
        else
            saved.push_back(w);
    }
    ws.resize (j - ws.begin ());
    for (const auto &w : saved)
        ws.push_back (w);
    saved.clear ();
    shrink_vector (ws);
}

/**
 * @brief:
 * @note:   collect.cpp:    flush_all_occs_and_watches()
 */
void Internal::circuit_flush_all_occs_and_watches() {
    // remove watch for garbage learnt gate
    if (circuit_watching()) {
        Circuit_Watches tmp;
        for (auto idx : vars) {
            circuit_flush_watches(idx, tmp);
            circuit_flush_watches(-idx, tmp);
        }
    }
}

/**
 * @brief
 * @note:   collect.cpp     update_reason_references()
 */
void Internal::circuit_update_reason_references() {
    LOG ("update assigned reason references");
#ifdef LOGGING
    size_t count = 0;
#endif
    for (auto &lit : trail) {
        if (!active(lit))
            continue;
        Var &v = var(lit);
        Circuit_Gate *g = v.circuit_reason;
        if (!g)
            continue;
        assert(g->reason);
        assert(g->moved);
        Circuit_Gate *d = g->copy;
        v.circuit_reason = d;
#ifdef LOGGING
        count++;
#endif
    }

    LOG ("updated %zd assigned reason references", count);
}

/**
 * @brief:
 * @note:   collect.cpp:    delete_garbage_clauses()
 */
void Internal::circuit_delete_garbage_gates() {
    circuit_flush_all_occs_and_watches();

    LOG ("deleting garbage gates");
#ifndef QUIET
    int64_t collected_bytes = 0, collected_clauses = 0;
#endif
    const auto end = circuit_gates.end();
    auto j = circuit_gates.begin(), i = j;
    while (i != end) {
        Circuit_Gate *g = *j++ = *i++;
        assert (g);
        if (!g->collect())
            continue;
#ifndef QUIET
        collected_bytes += g->bytes ();
        collected_clauses++;
#endif
        circuit_delete_gate(g);
        j--;
    }
    circuit_gates.resize(j - circuit_gates.begin());
    shrink_vector(circuit_gates);

    PHASE ("collect", stats.collections,
           "collected %" PRId64 " bytes of %" PRId64 " garbage clauses",
           collected_bytes, collected_clauses);
}

/**
 * @note:   collect.cpp:    copy_clause()
 */
void Internal::circuit_copy_gate(Circuit_Gate *g) {
    assert(!g->moved);
    char *p = (char * ) g;
    char *q = arena.copy(p, g->bytes());
    g->copy = (Circuit_Gate *) q;
    g->moved = true;
    LOG ("copied clause[%" PRId64 "] from %p to %p", g->id, (void *) g,
        (void *) g->copy);
}

/**
 * @note:   collect.cpp:  copy_non_garbage_clauses()
 */
void Internal::circuit_copy_non_garbage_gates() {
    size_t collected_clauses = 0, collected_bytes = 0;
    size_t moved_clauses = 0, moved_bytes = 0;

    // First determine 'moved_bytes' and 'collected_bytes'.
    //
    for (const auto &g : circuit_gates) {
        if (!g->collect()) {
            moved_bytes += g->bytes(), moved_clauses++;
        } else {
            collected_bytes += g->bytes(), collected_clauses++;
        }
    }
    PHASE ("collect", stats.collections,
            "moving %zd bytes %.0f%% of %zd non garbage clauses", moved_bytes,
            percent (moved_bytes, collected_bytes + moved_bytes),
            moved_clauses);
    (void) moved_clauses, (void) collected_clauses, (void) collected_bytes;
    // Prepare 'to' space of size 'moved_bytes'.
    //
    arena.prepare (moved_bytes);

    // Keep clauses in arena in the same order.
    //
    if (opts.arenacompact)
        for (const auto &g : circuit_gates)
            if (!g->collect() && arena.contains(g))
                circuit_copy_gate(g);

    if (opts.arenatype == 1 || !circuit_watching()) {
        // Localize according to current clause order.
        for (const auto &g : circuit_gates)
            if (!g->moved && !g->collect())
                circuit_copy_gate(g);

    } else if (opts.arenatype == 2) {
        // Localize according to (original) variable order.
        for (int sign = 1; sign >= -1; sign -= 2)
            for (auto idx : vars)
                for (const auto &w : circuit_watches(sign * circuit_likely_phase (idx)))
                    if (!w.gate->moved && !w.gate->collect())
                        circuit_copy_gate(w.gate);

    } else {
        // Localize according to decision queue order.
        assert(opts.arenatype == 3);
        for (int sign = 1; sign >= -1; sign -= 2)
            for (int idx = queue.last; idx; idx = link(idx).prev)
                for (const auto &w : circuit_watches(sign * circuit_likely_phase (idx)))
                    if (!w.gate->moved && !w.gate->collect())
                        circuit_copy_gate(w.gate);

    }

    for (const auto &g : circuit_gates)
        if (!g->collect() && !g->moved)
            circuit_copy_gate(g);

    circuit_flush_all_occs_and_watches();
    circuit_update_reason_references();

    // Replace and flush clause references in 'clauses'.
    //
    const auto end = circuit_gates.end();
    auto j = circuit_gates.begin(), i = j;
    for (; i != end; i++) {
        Circuit_Gate *g = *i;
        if (g->collect()) {
            circuit_delete_gate(g);
        } else {
            assert(g->moved);
            *j++ = g->copy;
            circuit_deallocate_gate(g);
        }
    }
    circuit_gates.resize(j - circuit_gates.begin());
    if (circuit_gates.size() < circuit_gates.capacity() / 2)
        shrink_vector(circuit_gates);

    if (opts.arenasort)
        rsort(circuit_gates.begin(), circuit_gates.end(), pointer_rank ());

    // Release 'from' space completely and then swap 'to' with 'from'.
    //
    arena.swap ();

    PHASE ("collect", stats.collections,
           "collected %zd bytes %.0f%% of %zd garbage clauses",
           collected_bytes,
           percent (collected_bytes, collected_bytes + moved_bytes),
           collected_clauses);
}

/**
 * @note:   collect.cpp:    arenaing()
 */
bool Internal::circuit_arenaing() { return opts.arena && (stats.collections > 1); }

/**
 * @note:   collect.cpp: garbage_collection()
 */
void Internal::circuit_garbage_collection() {
    START (collect);
    report ('G', 1);
    stats.collections++;

    if (!protected_reasons)
        circuit_protect_reasons();

    if (circuit_arenaing())
        circuit_copy_non_garbage_gates();
    else
        circuit_delete_garbage_gates();

    circuit_unprotect_reasons();
    report ('C', 1);
    STOP (collect);
}

}
