#include "../src/internal.hpp"

namespace CaDiCaL {

/**
 * @brief:
 * @note:   minimize.cpp: minimize_literal()
 * @param:  lit
 * @param:  depth
 */
bool Internal::circuit_minimize_literal(int lit, int depth) {
    LOG ("attempt to minimize lit %d at depth %d", lit, depth);
    assert(val(lit));

    Flags &f = flags(lit);
    Var &v = var(lit);
    if (!v.level || f.removable || f.keep)
        return true;
    auto reason = v.circuit_reason;
    auto reason_direct = v.circuit_reason_direct;
    if ((!reason && !reason_direct) || f.poison || v.level == level)
        return false;
    const Level &l = control[v.level];
    if (!depth && l.seen.count < 2)
        return false;
    if (v.trail <= l.seen.trail)
        return false;
    if (depth > opts.minimizedepth)
        return false;
    bool res = true;

    assert(reason || reason_direct);
    if (reason) {
        for (const auto &reason_literal : *reason) {
            if (abs(reason_literal) == abs(lit))
                continue;
            res =  circuit_minimize_literal(reason_literal, depth + 1);
            // cadical: minimize_literal() in condition of for-loop.
            if (res == 0) {
                break;
            }
        }
    } else {
        assert(reason_direct);
        res = circuit_minimize_literal(reason_direct, depth + 1);
    }

    if (res)
        f.removable = true;
    else
        f.poison = true;
    minimized.push_back(lit);
    if (!depth) {
        LOG ("minimizing %d %s", lit, res ? "succeeded" : "failed");
    }
    return res;
}

/**
 * @brief:  minimize
 * @note:   minimize.cpp:   minimize_clause()
 */
void Internal::circuit_minimize_clause() {
    START (minimize);
    LOG (clause, "minimizing first UIP clause");

    circuit_minimize_sort_clause();

    assert(minimized.empty());
    const auto end = clause.end();
    auto j = clause.begin (), i = j;
    for (; i != end; i++) {
        if (circuit_minimize_literal(*i)) {
            stats.minimized++;
        } else {
            flags (*j++ = *i).keep = true;
        }
    }
    LOG ("minimized %zd literals", (size_t) (clause.end () - j));
    if (j != end) {
        clause.resize(j - clause.begin());
    }
    circuit_clear_minimized_literals();
    STOP (minimize);
}


struct Circuit_minimize_trail_positive_rank {
  Internal *internal;
  Circuit_minimize_trail_positive_rank (Internal *s) : internal (s) {}
  typedef unsigned Type;
  Type operator() (const int &a) const {
    assert (internal->val (a));
    return (unsigned) internal->var (a).trail;
  }
};

struct Circuit_minimize_trail_smaller {
  Internal *internal;
  Circuit_minimize_trail_smaller (Internal *s) : internal (s) {}
  bool operator() (const int &a, const int &b) const {
    return internal->var (a).trail < internal->var (b).trail;
  }
};


/**
 * @brief:  sort clause
 * @note:   minimize.cpp:   minimize_sort_clause()
 */
void Internal::circuit_minimize_sort_clause() {
    MSORT(opts.radixsortlim, clause.begin(), clause.end(),
          Circuit_minimize_trail_positive_rank(this),
          Circuit_minimize_trail_smaller(this));
}

/**
 * @brief:  clear
 * @note:   minimize.cpp:   clear_minimized_literals()
 */
void Internal::circuit_clear_minimized_literals() {
    LOG ("clearing %zd minimized literals", minimized.size ());
    for (const auto &lit : minimized) {
        Flags &f = flags (lit);
        f.poison = f.removable = f.shrinkable = f.added = false;
    }
    for (const auto &lit : clause) {
        assert (!flags (lit).shrinkable);
        flags (lit).keep = flags (lit).shrinkable = flags (lit).added = false;
    }
    minimized.clear ();
}
}
