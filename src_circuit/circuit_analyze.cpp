#include "../src/internal.hpp"

namespace CaDiCaL {

/**
 * @note:   analyze.cpp: learn_empty_clause()
 */
void Internal::circuit_learn_empty_clause() {
    assert (!unsat);
    LOG ("learned empty clause");

    unsat = true;
}

/**
 * @note:   analyze.cpp: learn_unit_clause();
 */
void Internal::circuit_learn_unit_clause(int lit) {
    assert (!unsat);
    assert (lit);
    LOG ("learned unit clause %d", lit);
    mark_fixed (lit);
}

/**
 * @note:   analyze.cpp: analyze_bumped_rank
 */
struct Circuit_analyze_bumped_rank {
    Internal *internal;
    Circuit_analyze_bumped_rank (Internal *i) : internal (i) {}
    typedef uint64_t Type;
    Type operator() (const int &a) const { return internal->bumped (a); }
};

/**
 * @note:   analyze.cpp: analyze_bumped_smaller
 */
struct Circuit_analyze_bumped_smaller {
    Internal *internal;
    Circuit_analyze_bumped_smaller (Internal *i) : internal (i) {}
    bool operator() (const int &a, const int &b) const {
        const auto s = Circuit_analyze_bumped_rank (internal) (a);
        const auto t = Circuit_analyze_bumped_rank (internal) (b);
        return s < t;
    }
};

/**
 * @brief:  Bump for gate in analyzed
 * @note:   analyze.cpp: bump_variables()
 */
void Internal::circuit_bump_variables() {
    assert(opts.bump);

    START (bump);

    if (opts.bumpreason)
        circuit_bump_also_all_reason_literals();
    
    if (!use_scores()) {
        MSORT (opts.radixsortlim, analyzed.begin (), analyzed.end (),
               Circuit_analyze_bumped_rank (this), Circuit_analyze_bumped_smaller (this));
    }

    for (const auto& var : analyzed) {
        bump_variable(var);
    }

    if (use_scores())
        bump_variable_score_inc ();

    STOP(bump);
}

/**
 * @brief:  Recompute glue: use the glue time stamp table 'gtab' for fast glue computation.
 * @note:   analyze.cpp: recompute_glue()
 */
int Internal::circuit_recompute_glue(Circuit_Gate* gate) {
    int res = 0;
    const int64_t stamp = ++stats.recomputed;
    for (const auto &lit : *gate) {
        int level = circuit_assign_level_get(lit);
        assert (gtab[level] <= stamp);
        if (gtab[level] == stamp)
            continue;
        gtab[level] = stamp;
        res++;
    }
    return res;
}

/**
 * @brief:  bump gate for learnt gate
 * @note:   analyze.cpp: bump_clause()
 * @param:  g     ptr of learnt_gate
 */
inline void Internal::circuit_bump_gate(Circuit_Gate *g) {
    unsigned used = g->used;
    g->used = 1;
    if (g->keep)
        return;
    if (g->hyper)
        return;
    if (!g->redundant)
        return;
    int new_glue = circuit_recompute_glue(g);
    if (new_glue < g->glue)
        circuit_promote_gate(g, new_glue);
    else if (used && g->glue <= opts.reducetier2glue)
        g->used = 2;
}

/**
 * @brief:  analyze gate
 * @note:   analyze.cpp: analyze_literal()
 * @param:  lit     (gate_id * gate_val)
 * @param:  open
 */
inline void Internal::circuit_analyze_literal(int lit, int &open, int &resolvent_size, int &antecedent_size) {
    assert (lit);
    Var &v = var(lit);
    if (!v.level)
        return;

    Flags& f = flags(lit);
    ++antecedent_size;
    if (f.seen)
        return;
    f.seen = true;
    analyzed.push_back(lit);

    assert(circuit_val(lit) > 0);
    assert(v.level <= level);
    if (v.level < level)
        clause.push_back(lit);
    Level& l = control[v.level];
    if (!l.seen.count++) {
        LOG ("found new level %d contributing to conflict", v.level);
        levels.push_back(v.level);
    }
    if (v.trail < l.seen.trail)
        l.seen.trail = v.trail;
    ++resolvent_size;
    LOG ("analyzed literal %d assigned at level %d", lit, v.level);
    if (v.level == level)
        open++;
}

/**
 * @brief:  analyze reason
 * @note:   analyze.cpp:    analyze_reason()
 */
inline void Internal::circuit_analyze_reason(int lit, Circuit_Gate *reason, const std::array<int, 2> &reason_direct_array,
                                             int &open, int &resolvent_size, int &antecedent_size) {
    if (reason) {
        for (const auto &reason_literal : *reason) {
            if (abs(reason_literal) != abs(lit))
                circuit_analyze_literal(reason_literal, open, resolvent_size, antecedent_size);
        }
    } else {
        for (const auto &reason_literal : reason_direct_array) {
            if (reason_literal)
                circuit_analyze_literal(reason_literal, open, resolvent_size, antecedent_size);
        }
    }
}

/**
 * @brief:  bump reason literal: lit called by circuit_bump_also_reason_literals()
 * @note:   analyze.cpp: bump_also_reason_literal()
 * @param:  lit
 */
inline bool Internal::circuit_bump_also_reason_literal(int lit) {
    assert (lit);
    assert (circuit_val(lit) > 0);
    Flags &f = flags(lit);
    if (f.seen)
        return false;
    const Var &v = var(lit);
    if (!v.level)
        return false;
    f.seen = true;
    analyzed.push_back(lit);
    LOG ("bumping also reason literal %d assigned at level %d", lit, v.level);
    return true;
}

/**
 * @brief:  bump reasons of lit
 * @note:   analyze.cpp: bump_also_reason_literals()
 * @param:  lit
 * @parmt:  limit:  limit of reasons' depth
 */
inline void Internal::circuit_bump_also_reason_literals(int lit, int limit) {
    assert (lit);
    assert (limit > 0);
    const Var &v = var (lit);
    assert(val(lit));
    if (!v.level)
        return;

    auto process_reason_literal = [&](int reason_literal) {
        if (abs(reason_literal) == abs(lit))
            return;
        if (!circuit_bump_also_reason_literal(reason_literal))
            return;
        if (limit < 2)
            return;
        circuit_bump_also_reason_literals(reason_literal, limit - 1);
    };
    auto reason = v.circuit_reason;
    auto reason_direct = v.circuit_reason_direct;
    if (reason) {
        for (const auto& reason_literal : *reason) {
            process_reason_literal(reason_literal);
        }
    } else if (reason_direct) {
        process_reason_literal(reason_direct);
    }
}

/**
 * @brief:  bump reasons of lit in clause
 * @note:   analyze.cpp: bump_also_all_reason_literals()
 */
inline void Internal::circuit_bump_also_all_reason_literals() {
    assert (opts.bumpreason);
    assert (opts.bumpreasondepth > 0);
    LOG ("bumping reasons up to depth %d", opts.bumpreasondepth);
    for (const auto &lit : clause)
         circuit_bump_also_reason_literals (lit, opts.bumpreasondepth + stable);
}

/**
 * @note:   analyze.cpp: analyze_trail_negative_rank
 */
struct Circuit_analyze_trail_negative_rank {
    Internal *internal;
    Circuit_analyze_trail_negative_rank (Internal *s) : internal (s) {}
    typedef uint64_t Type;
    Type operator() (int a) {
        Var &v = internal->var (a);
        uint64_t res = v.level;
        res <<= 32;
        res |= v.trail;
        return ~res;
    }
};


/**
 * @note:   analyze.cpp: analyze_trail_larger
 */
struct Circuit_analyze_trail_larger {
    Internal *internal;
    Circuit_analyze_trail_larger (Internal *s) : internal (s) {}
    bool operator() (const int &a, const int &b) const {
        return Circuit_analyze_trail_negative_rank (internal) (a) <
            Circuit_analyze_trail_negative_rank (internal) (b);
    }
};

/**
 * @brief:  Generate new driving gate and compute jump level
 * @note:   analyze.cpp: new_driving_clause()
 * @param： glue        the lbd for new learnt gate
 * @param： jump        the second highest decide level of new learnt gate
 * @return              the id of new learnt gate
 */
Circuit_Gate* Internal::circuit_new_driving_gate(int glue, int& jump) {
    auto size = clause.size();
    Circuit_Gate* res;

    if (size == 1) {
        iterating = true;
        jump = 0;
        res = 0;
    } else {
        assert(size > 1);

        MSORT(opts.radixsortlim, clause.begin(), clause.end(),
              Circuit_analyze_trail_negative_rank(this), Circuit_analyze_trail_larger(this));


        jump = circuit_assign_level_get(clause[1]);
        res = circuit_new_learned_redundant_gate(glue);
        res->used = 1 + (glue <= opts.reducetier2glue);
    }

    LOG ("jump level %d", jump);
    return res;
}

/**
 * @brief:  Find the actual conflict level.
 * @note:   analyze.cpp: find_conflict_level()
 * @param:  forced
 */
inline int Internal::circuit_find_conflict_level(int &forced) {
    assert(opts.chrono);

    int res = 0, count = 0;

    forced = 0;
    auto process_conflict_literals_array = [&](const auto &array) {
        for (const auto &lit : array) {
            const int tmp = circuit_assign_level_get(lit);
            if (tmp > res) {
                res = tmp;
                forced = lit;
                count = 1;
            } else if (tmp == res) {
                count++;
                if (res == level && count > 1)
                    break;
            }
        }
    };
    if (circuit_conflict_gate) {
        process_conflict_literals_array(*circuit_conflict_gate);
    } else {
        process_conflict_literals_array(circuit_conflict_direct);
    }

    LOG ("%d literals on actual conflict level %d", count, res);

    if (circuit_conflict_gate) {
        const int size = circuit_conflict_gate->size;
        int *lits = circuit_conflict_gate->literals;
        // Move the two highest level literals to the front.
        //
        for (int i = 0; i < 2; i++) {
            const int lit = lits[i];
            int highest_position = i;
            int highest_literal = lit;
            int highest_level = circuit_assign_level_get(highest_literal);

            for (int j = i + 1; j < size; j++) {
                const int other = lits[j];
                const int tmp = circuit_assign_level_get(other);
                if (highest_level >= tmp)
                    continue;
                highest_literal = other;
                highest_position = j;
                highest_level = tmp;
                if (highest_level == res)
                    break;
            }

            // No unwatched higher assignment level literal.
            //
            if (highest_position == i)
                continue;
            if (highest_position > 1) {
                circuit_remove_watch(circuit_watches(lit), circuit_conflict_gate);
            }
            lits[highest_position] = lit;
            lits[i] = highest_literal;

            if (highest_position > 1)
                circuit_watch_literal(highest_literal, lits[!i], circuit_conflict_gate);
        }
    }

    // Only if the number of highest level literals in the conflict is one
    // then we can reuse the conflict clause as driving clause for 'forced'.
    //
    if (count != 1)
        forced = 0;

    return res;
}

/**
 * @brief
 * @note:   analyze.cpp: determine_actual_backtrack_level()
 * @param:  jump
 */
inline int Internal::circuit_determine_actual_backtrack_level(int jump) {
    int res;

    assert (level > jump);
    if (!opts.chrono) {
        res = jump;
        LOG ("chronological backtracking disabled using jump level %d", res);
    } else if (opts.chronoalways) {
        stats.chrono++;
        res = level - 1;
        LOG ("forced chronological backtracking to level %d", res);
    } else if (jump >= level - 1) {
        res = jump;
        LOG ("jump level identical to chronological backtrack level %d", res);
    } else if ((size_t) jump < assumptions.size ()) {
        res = jump;
        LOG ("using jump level %d since it is lower than assumption level %zd",
            res, assumptions.size ());
    }  else if (level - jump > opts.chronolevelim) {
        stats.chrono++;
        res = level - 1;
        LOG ("back-jumping over %d > %d levels prohibited"
            "thus backtracking chronologically to level %d",
            level - jump, opts.chronolevelim, res);
    } else if (opts.chronoreusetrail) {
        int best_idx = 0, best_pos = 0;

        if (use_scores ()) {
            for (size_t i = control[jump + 1].trail; i < trail.size (); i++) {
                const int idx = abs (trail[i]);
                if (best_idx && !score_smaller (this) (best_idx, idx))
                    continue;
                best_idx = idx;
                best_pos = i;
            }
            LOG ("best variable score %g", score (best_idx));
        } else {
            for (size_t i = control[jump + 1].trail; i < trail.size (); i++) {
                const int idx = abs (trail[i]);
                if (best_idx && bumped (best_idx) >= bumped (idx))
                continue;
                best_idx = idx;
                best_pos = i;
            }
            LOG ("best variable bumped %" PRId64 "", bumped (best_idx));
        }
        assert (best_idx);
        LOG ("best variable %d at trail position %d", best_idx, best_pos);

        // Now find the frame and decision level in the control stack of that
        // best variable index.  Note that, as in 'reuse_trail', the frame
        // 'control[i]' for decision level 'i' contains the trail before that
        // decision level, i.e., the decision 'control[i].decision' sits at
        // 'control[i].trail' in the trail and we thus have to check the level
        // of the control frame one higher than at the result level.
        //
        res = jump;
        while (res < level - 1 && control[res + 1].trail <= best_pos)
         res++;

        if (res == jump)
            LOG ("default non-chronological back-jumping to level %d", res);
        else {
            stats.chrono++;
            LOG ("chronological backtracking to level %d to reuse trail", res);
        }
    } else {
        res = jump;
        LOG ("non-chronological back-jumping to level %d", res);
    }
    return res;
}

/**
 * @brief:  Use last learned clause to subsume some more.
 * @note:   analyze.cpp:    eagerly_subsume_recently_learned_clauses()
 */
void Internal::circuit_eagerly_subsume_recently_learned_clauses(Circuit_Gate *g) {
    assert(opts.eagersubsume);
    circuit_mark(g);
    int64_t lim = stats.eagertried + opts.eagersubsumelim;
    const auto begin = circuit_gates.begin();
    auto it = circuit_gates.end();
#ifdef LOGGING
    int64_t before = stats.eagersub;
#endif
    while (it != begin && stats.eagertried++ <= lim) {
        Circuit_Gate *d = *--it;
        if (g == d)
            continue;
        if (d->garbage)
            continue;
        if (!d->redundant)
            continue;
        int needed = g->size;
        for (auto &lit : *d) {
            if (marked (lit) <= 0)
                continue;
            if (!--needed)
                break;
        }
        if (needed)
            continue;
        stats.eagersub++;
        stats.subsumed++;
        circuit_mark_garbage (d);
    }
    circuit_unmark(g);
#ifdef LOGGING
    uint64_t subsumed = stats.eagersub - before;
    if (subsumed)
        LOG ("eagerly subsumed %" PRIu64 " clauses", subsumed);
#endif 

}

/**
 * @brief:  Main conflict analysis routine;
 * @note:   analyze.cpp: analyze()
 */
void Internal::circuit_analyze() {
    START (analyze);

    assert(clause.empty());

    if (opts.chrono) {
        int forced;

        const int conflict_level = circuit_find_conflict_level(forced);

        if (forced) {
            assert(forced);
            assert(conflict_level > 0);
            LOG ("single highest level literal %d", forced);

            circuit_backtrack (conflict_level - 1);

            LOG ("forcing %d", forced);
            int reason_direct = 0;
            if (!circuit_conflict_gate) {
                assert(circuit_conflict_direct[0] == forced || circuit_conflict_direct[1] == forced);
                reason_direct = forced ^ circuit_conflict_direct[0] ^ circuit_conflict_direct[1];
            }
            circuit_search_assign_driving(-forced, circuit_conflict_gate, reason_direct);

            circuit_conflict_clear();
            STOP(analyze);
            return;
        }

        circuit_backtrack(conflict_level);
    }

    // Actual conflict on root level, thus formula unsatisfiable.
    //
    if (!level){
        circuit_learn_empty_clause();
        STOP (analyze);
        return;
    }

    Circuit_Gate* reason = circuit_conflict_gate;
    std::array<int, 2>& reason_direct_array = circuit_conflict_direct;

    const auto &t = &trail;
    int i = t->size();       // Start at end-of-trail;
    int open = 0;            // Seen but not processed on this level.
    int uip = 0;             // The first UIP literal.
    int resolvent_size = 0;  // without the uip
    int antecedent_size = 1; // with the uip and without unit literals
    int resolved = 0;        // number of resolution (0 = clause in CNF)

    for (;;) {
        antecedent_size = 1; // for uip
        circuit_analyze_reason(uip, reason, reason_direct_array, open, resolvent_size, antecedent_size);
        assert (resolvent_size == open + (int) clause.size ());

        ++resolved;

        uip = 0;
        while (!uip) {
            assert (i > 0);
            const int cur_lit = (*t)[--i];
            if (!flags (cur_lit).seen)
                continue;
            if (circuit_assign_level_get(cur_lit) == level)
                uip = cur_lit;
        }
        if (!--open)
            break;

        const Var &v = var(uip);
        reason = v.circuit_reason;
        reason_direct_array = {v.circuit_reason_direct, 0};
        assert (resolvent_size);
        --resolvent_size;
    }

    LOG ("first UIP %d", uip);
    clause.push_back(uip);

    // Update glue and learned (1st UIP literals) statistics.
    //
    int size = (int)clause.size();
    const int glue = (int)levels.size() - 1;
    LOG (clause, "1st UIP size %d and glue %d clause", size, glue);
    UPDATE_AVERAGE (averages.current.glue.fast, glue);
    UPDATE_AVERAGE (averages.current.glue.slow, glue);
    stats.learned.literals += size;
    stats.learned.clauses++;
    assert (glue < size);

    if (size > 1) {
        if (opts.shrink)
            circuit_shrink_and_minimize_clause ();
        else if (opts.minimize)
            circuit_minimize_clause();

        // Update decision heuristics.
        //
        if (opts.bump)
            circuit_bump_variables();
    }

    int jump;
    Circuit_Gate *driving_gate = circuit_new_driving_gate(glue, jump);
    UPDATE_AVERAGE (averages.current.jump, jump);

    int new_level = circuit_determine_actual_backtrack_level(jump);
    UPDATE_AVERAGE (averages.current.level, new_level);
    circuit_backtrack(new_level);

    circuit_search_assign_driving(-uip, driving_gate, 0);

    if (stable)
        reluctant.tick (); // Reluctant has its own 'conflict' counter.

    // Clean up.
    //
    clear_analyzed_literals();
    clear_analyzed_levels();
    clause.clear();
    circuit_conflict_clear();

    STOP (analyze);

    if (driving_gate && opts.eagersubsume)
        circuit_eagerly_subsume_recently_learned_clauses(driving_gate);
}

/**
 * @brief:  Reportintg a learnt unit.
 * @note:   analyze.cpp: iterate()
 */
void Internal::circuit_iterate() {
    iterating = false;
    report ('i');
}

}
