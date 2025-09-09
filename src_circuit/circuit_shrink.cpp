#include "../src/internal.hpp"
#include "../src/reap.hpp"

namespace CaDiCaL {

/**
 * @brief Reset shrinkable flag in shrinkable.
 */
void Internal::circuit_reset_shrinkable () {
#ifdef LOGGING
    size_t reset = 0;
#endif
    for (const auto &lit : shrinkable) {
        LOG ("resetting lit %i", lit);
        Flags &f = flags (lit);
        assert (f.shrinkable);
        f.shrinkable = false;
#ifdef LOGGING
        ++reset;
#endif
    }
    LOG ("resetting %zu shrinkable variables", reset);
}

/**
 * @brief Mark shrinkable flag in shrinkable to removable flag.
 * @note: shrink.cpp: mark_shrinkable_as_removable()
 * @param blevel:               the level of current block
 * @param minimized_start:      the start index of minimized
 */
void Internal::circuit_mark_shrinkable_as_removable (int blevel, std::vector<int>::size_type minimized_start) {
#ifdef LOGGING
    size_t marked = 0, reset = 0;
#endif
#ifndef NDEBUG
    unsigned kept = 0, minireset = 0;
    for (; minimized_start < minimized.size (); ++minimized_start) {
        const auto lit = minimized[minimized_start];
        Flags &f = flags (lit);
        const Var &v = var (lit);
        if (v.level == blevel) {
        assert (!f.poison);
        ++minireset;
        } else
        ++kept;
    }
    (void) kept;
    (void) minireset;
#else
    (void) blevel;
    (void) minimized_start;
#endif

    for (const int lit : shrinkable) {
        Flags &f = flags (lit);
        assert (f.shrinkable);
        assert (!f.poison);
        f.shrinkable = false;
#ifdef LOGGING
        ++reset;
#endif
        if (f.removable)
        continue;
        f.removable = true;
        minimized.push_back (lit);
#ifdef LOGGING
        ++marked;
#endif
    }
    LOG ("resetting %zu shrinkable variables", reset);
    LOG ("marked %zu removable variables", marked);
}

/**
 * @brief Mark shrinkaable flag and insert into shrinkable.
 * @param lit:          lit (gate_id * gate_val)
 * @param blevel:       the level of current block
 * @param max_trail:    the max trail of current block
 * @return              0:success -1: failed
 */
int inline Internal::circuit_shrink_literal(int lit, int blevel, unsigned max_trail) {
    Flags &f = flags (lit);
    const Var &v = var(lit);
    assert (v.level <= blevel);

    if (!v.level) {
        LOG ("skipping root level assigned %d", (lit));
        return 0;
    }

    if (f.shrinkable) {
        LOG ("skipping already shrinkable literal %d", (lit));
        return 0;
    }

    if (v.level < blevel) {
        if (f.removable) {
            LOG ("skipping removable thus shrinkable %d", (lit));
            return 0;
        }
        const bool always_minimize_on_lower_blevel = (opts.shrink > 2);
        if (always_minimize_on_lower_blevel && circuit_minimize_literal (lit, 1)) {
            LOG ("minimized thus shrinkable %d", (lit));
            return 0;
        }
        LOG ("literal %d on lower blevel %u < %u not removable/shrinkable",
            (lit), v.level, blevel);
        return -1;
    }

    LOG ("marking %d as shrinkable", lit);
    f.shrinkable = true;
    f.poison = false;
    shrinkable.push_back (lit);
    if (opts.shrinkreap) {
        assert (max_trail < trail.size ());
        const unsigned dist = max_trail - v.trail;
        reap.push (dist);
    }
    return 1;
}

/**
 * @brief Process shrunken block:
 *          1. Replace rebgin_block with uip (uip of blevel).
 *          2. Replace other literal with uip0 (uip of clause), will delete in Circuit_shrink_and_minimize_clause().
 *          3. Mark shrinkable flag as removable flag in Circuit_mark_shrinkable_as_removable().
 * @note: shrink.cpp:  shrunken_block_uip()
 * @param uip:                  uip of blevel
 * @param blevel:               the decide level of current block
 * @param rbegin_block:         rbegin_block of current block
 * @param rend_block:           rend_block of current block
 * @param minimized_start:      minimized start index
 * @param uip0:                 uip of clause
 * @return                      the block_shrunken: number of literal shrunk
 */
unsigned Internal::circuit_shrunken_block_uip (int uip, int blevel,
                                               std::vector<int>::reverse_iterator &rbegin_block,
                                               std::vector<int>::reverse_iterator &rend_block,
                                               std::vector<int>::size_type minimized_start,
                                               const int uip0) {
    assert(clause[0] == uip0);

    LOG ("UIP on level %u, uip: %i (replacing by %i)", blevel, uip, uip0);
    assert (rend_block > rbegin_block);
    assert (rend_block < clause.rend());
    unsigned block_shrunken = 0;
    *rbegin_block = uip;
    Var &v = var(uip);
    Level &l = control[v.level];
    l.seen.trail = v.trail;
    l.seen.count = 1;

    Flags &f = flags (uip);
    if (!f.seen) {
        analyzed.push_back(uip);
        f.seen = true;
    }

    flags (uip).keep = true;
    for (auto p = rbegin_block + 1; p != rend_block; ++p) {
        const auto lit = *p;
        if (lit == uip0)
            continue;
        *p = uip0;

        ++block_shrunken;
        assert (clause[0] == uip0);
    }
    circuit_mark_shrinkable_as_removable(blevel, minimized_start);
    assert(clause[0] == uip0);
    return block_shrunken;
}

/**
 * @brief: For no uip block: call do minimized under option minimize.
 * @note:  shrink.cpp:  shrunken_block_no_uip()
 * @param rbegin_block:         rbegin_block of current block
 * @param rend_block:           rend_block of current block
 * @param block_minimized:      minimized num in current block
 * @param uip0:                 uip of clause
 */
void inline Internal::circuit_shrunken_block_no_uip(const std::vector<int>::reverse_iterator &rbegin_block,
                                                    const std::vector<int>::reverse_iterator &rend_block,
                                                    unsigned &block_minimized, const int uip0) {
    STOP (shrink);
    START (minimize);
    assert (rend_block > rbegin_block);
    LOG ("no UIP found, now minimizing");
    for (auto p = rbegin_block; p != rend_block; ++p) {
        assert (p != clause.rend () - 1);
        const auto lit = *p;
        if (opts.minimize && circuit_minimize_literal (lit)) {
            assert (!flags (lit).keep);
            ++block_minimized;
            *p = uip0;
        } else {
            flags (lit).keep = true;
            assert (flags (lit).keep);
        }
    }
    STOP (minimize);
    START (shrink);
}

/**
 * @brief: Push literals of block by call Circuit_shrink_literal():
 *          set shrinkable flag and insert in reap under option shrinkreap.
 * @note: shrink.cpp:  push_literals_of_block()
 * @param rbegin_block:     rbegin iterator of current block
 * @param rend_block:       rend iterator of current block
 * @param blevel:           the decide level of current block
 * @param max_trail:        the max trail of current block
 */
void Internal::circuit_push_literals_of_block(const std::vector<int>::reverse_iterator &rbegin_block,
                                              const std::vector<int>::reverse_iterator &rend_block,
                                              int blevel, unsigned max_trail) {
    assert (rbegin_block < rend_block);
    for (auto p = rbegin_block; p != rend_block; ++p) {
        assert (p != clause.rend() - 1);
        assert (!flags (*p).keep);
        const auto lit = *p;
        LOG ("pushing lit %i of blevel %i", lit, var (lit).level);
#ifndef NDEBUG
        int tmp =
#endif
            circuit_shrink_literal (lit, blevel, max_trail);
        assert (tmp > 0);
    }
}

/**
 * @brief Process next literal in current block.
 * @param blevel:           the decide level of current block
 * @param open:             the num of literals not processed in current block.
 * @param max_trail:        the max_trail of current block
 * @return                  the next literal for shrink
 */
unsigned inline Internal::circuit_shrink_next(int blevel, unsigned &open, unsigned &max_trail) {
    const auto &t = &trail;
    if (opts.shrinkreap) {
        assert (!reap.empty ());
        const unsigned dist = reap.pop ();
        --open;
        assert (dist <= max_trail);
        const unsigned pos = max_trail - dist;
        assert (pos < t->size ());
        const int uip = (*t)[pos];

        LOG ("trying to shrink literal %d at trail[%u] and level %d", uip, pos,
             blevel);
        return uip;
    } else {
        int uip;
#ifndef NDEBUG
        unsigned init_max_trail = max_trail;
#endif
        do {
            assert (max_trail <= init_max_trail);
            uip = (*t)[max_trail--];
        } while (!flags (uip).shrinkable);
        --open;
        LOG ("open is now %d, uip = %d, level %d", open, uip, blevel);
        return uip;
    }
    (void) blevel;
}

/**
 * @brief Shrink the reasons of uip.
 * @param uip:                      the current literal to process reasons
 * @param blevel:                   the decide level of uip
 * @param resolve_large_clauses:
 * @param failed_ptr:               failed ptr
 * @param max_trail:                the max trail of current block
 * @return                          the num of literals not processed in current block after analyze the reason of uip
 */
unsigned inline Internal::circuit_shrink_along_reason(int uip, int blevel, bool resolve_large_clauses, 
                                                      bool &failed_ptr, unsigned max_trail) {
    LOG ("shrinking along the reason of lit %i", uip);
    unsigned open = 0;
#ifndef NDEBUG
    const Flags &f = flags (uip);
#endif
    const Var &v = var (uip);

    assert (f.shrinkable);
    assert (v.level == blevel);

    auto reason = v.circuit_reason;
    auto reason_direct = v.circuit_reason_direct;
    assert(reason || reason_direct);

    if (resolve_large_clauses) { // TODO (taomengxia)
        auto process_reason_literal = [&](int reason_literal) {
            if (abs(reason_literal) == abs(uip))
                return;

            int tmp = circuit_shrink_literal (reason_literal, blevel, max_trail);
            if (tmp < 0) {
                failed_ptr = true;
            }
            if (tmp > 0) {
                ++open;
            }
        };
        if (reason) {
            for (const auto &reason_literal : *reason) {
                process_reason_literal(reason_literal);
                if (failed_ptr)
                    break;
            }
        } else {
            assert(reason_direct);
            process_reason_literal(reason_direct);
        }
    } else {
        failed_ptr = true;
    }
    return open;
}

/**
 * @brief Shrink block.
 * @note  shrink.cpp:   shrink_block()
 * @param rbegin_lits:          the rbegin iterator to shrink block
 * @param rend_block:           the rend iterator to shrin block
 * @param blevel:               the decide level of current block
 * @param open:                 the num of literals not processed in current block
 * @param block_minimized:      the num of minimized literals in current block
 * @param uip0:                 the uip of clause
 * @param max_trail:            the max trail of current block
 * @return                      the num of shrunken literals in current block
 */
unsigned Internal::circuit_shrink_block (std::vector<int>::reverse_iterator &rbegin_lits,
                                         std::vector<int>::reverse_iterator &rend_block,
                                         int blevel, unsigned& open, unsigned &block_minimized,
                                         const int uip0, unsigned max_trail) {
   assert (shrinkable.empty());
   assert (blevel <= this->level);
   assert (open < clause.size());
   assert (rbegin_lits >= clause.rbegin());
   assert (rend_block < clause.rend());
   assert (opts.shrink);

#ifdef LOGGING

    LOG ("trying to shrink %u literals on level %u", open, blevel);

    const auto &t = &trail;

    LOG ("maximum trail position %zd on level %u", t->size (), blevel);
    if (opts.shrinkreap)
        LOG ("shrinking up to %u", max_trail);
#endif

    const bool resolve_large_clauses = (opts.shrink > 1);
    bool failed = false;
    unsigned block_shrunken = 0;
    std::vector<int>::size_type minimized_start = minimized.size ();
    auto uip = uip0;
    unsigned max_trail2 = max_trail;

    if (!failed) {
        circuit_push_literals_of_block (rbegin_lits, rend_block, blevel, max_trail);
        assert (!opts.shrinkreap || reap.size() == open);

        assert (open > 0);
        while (!failed) {
            assert (!opts.shrinkreap || reap.size () == open);
            uip = circuit_shrink_next(blevel, open, max_trail);
            if (open == 0) {
                break;
            }
            open += circuit_shrink_along_reason(uip, blevel, resolve_large_clauses, failed, max_trail2);
            assert (open >= 1);
        }

        if (!failed)
        LOG ("shrinking found UIP %i on level %i (open: %d)", uip, blevel,
            open);
        else
        LOG ("shrinking failed on level %i", blevel);
    }

    if (failed)
        circuit_reset_shrinkable(), circuit_shrunken_block_no_uip (rbegin_lits, rend_block, block_minimized, uip0);
    else
        block_shrunken = circuit_shrunken_block_uip (uip, blevel, rbegin_lits, rend_block, minimized_start, uip0);

    if (opts.shrinkreap)
        reap.clear();
    shrinkable.clear();
    return block_shrunken;
}

struct Circuit_shrink_trail_negative_rank {
    Internal *internal;
    Circuit_shrink_trail_negative_rank (Internal *s) : internal (s) {}
    typedef uint64_t Type;
    Type operator() (int a) {
        Var &v = internal->var (a);
        uint64_t res = v.level;
        res <<= 32;
        res |= v.trail;
        return ~res;
    }
};

struct Circuit_shrink_trail_larger {
    Internal *internal;
    Circuit_shrink_trail_larger (Internal *s) : internal (s) {}
    bool operator() (const int &a, const int &b) const {
        return Circuit_shrink_trail_negative_rank (internal) (a) <
                Circuit_shrink_trail_negative_rank (internal) (b);
    }
};


/**
 * @brief   Minimize and shrink block.
 * @note    shrink.cpp: minimize_and_shrink_block()
 * @param rbegin_block:         the rbegin iterator of current block
 * @param total_shrunken:       the total num of shrunen literals in current block
 * @param total_minimized:      the total num of minimized literals in current block
 * @param uip0:                 the uip of clause
 * @return                      the end iterator of current block
 */
std::vector<int>::reverse_iterator Internal::circuit_minimize_and_shrink_block(
        std::vector<int>::reverse_iterator &rbegin_block,
        unsigned &total_shrunken, unsigned &total_minimized, const int uip0)
{
    LOG ("shrinking block");
    assert(rbegin_block < clause.rend() - 1);
    int blevel;
    unsigned open = 0;
    unsigned max_trail = 0;

    // find begining of block;
    std::vector<int>::reverse_iterator rend_block;
    {
        assert(rbegin_block <= clause.rend());
        const auto lit = *rbegin_block;
        const int idx = vidx(lit);
        blevel = vtab[idx].level;
        max_trail = vtab[idx].trail;
        LOG ("Block at level %i (first lit: %i)", blevel, lit);
        
        rend_block = rbegin_block;
        bool finished;
        do {
            assert(rend_block < clause.rend() - 1);
            const auto lit = *(++rend_block);
            const int idx = vidx(lit);
            finished = (blevel != vtab[idx].level);
            if (!finished && (unsigned)vtab[idx].trail > max_trail)
                max_trail = vtab[idx].trail;
            ++open;
            LOG (
                "testing if lit %i is on the same level (of lit: %i, global: %i)",
                lit, vtab[idx].level, blevel); 

        } while (!finished);
    }
    assert (open > 0);;
    assert (open < clause.size());
    assert (rbegin_block < clause.rend());
    assert (rend_block < clause.rend());
    
    unsigned block_shrunken = 0, block_minimized = 0;
    if (open < 2) {
        flags (*rbegin_block).keep = true;
        minimized.push_back(*rbegin_block);
    } else {
        block_shrunken = circuit_shrink_block(rbegin_block, rend_block, blevel, open,
                                              block_minimized, uip0, max_trail);
    }
    LOG ("shrunken %u literals on level %u (including %u minimized)",
         block_shrunken, blevel, block_minimized);

    total_shrunken += block_shrunken;
    total_minimized += block_minimized;

    return rend_block;
}

/**
 * @brief Minimize and shrink clause.
 */
void Internal::circuit_shrink_and_minimize_clause() {
    assert (opts.minimize || opts.shrink > 0);
    LOG (clause, "shrink first UIP clause");

    START (shrink);

    MSORT (opts.radixsortlim, clause.begin (), clause.end (),
           Circuit_shrink_trail_negative_rank (this), Circuit_shrink_trail_larger (this));
    unsigned total_shrunken = 0;
    unsigned total_minimized = 0;

    LOG (clause, "shrink first UIP clause (asserting lit: %i)", clause[0]);

    auto rend_lits = clause.rend() - 1;
    auto rend_block = clause.rbegin();
    const auto uip0 = clause[0];

    while (rend_block != rend_lits) {
        rend_block = circuit_minimize_and_shrink_block(rend_block, total_shrunken, total_minimized, uip0);
    }
    
    LOG (clause,
         "post shrink pass (with uips, not removed) first UIP clause");

#if defined(LOGGING) || !defined(NDEBUG)
    const unsigned old_size = clause.size ();
#endif
    {
        std::vector<int>::size_type i = 1;
        for (std::vector<int>::size_type j = 1; j < clause.size(); j++) {
            clause[i] = clause[j];
            if (clause[j] == uip0) {
                continue;
            }
            assert (flags (clause[i]).keep);
            ++i;
            LOG ("keeping literal %i", clause[j]);
        }
        clause.resize(i);
    }
    assert (old_size ==
             (unsigned) clause.size () + total_shrunken + total_minimized);
    LOG (clause, "after shrinking first UIP clause");
    LOG ("clause shrunken by %zd literals (including %u minimized)",
          old_size - clause.size (), total_minimized);

    stats.shrunken += total_shrunken;
    stats.minishrunken += total_minimized;

    STOP (shrink);

    START (minimize);
    circuit_clear_minimized_literals();
    STOP (minimize); 
}

}
