#include "../src/internal.hpp"

namespace CaDiCaL {

/// @note:  watch.cpp:  init_watches()
void Internal::circuit_init_watches () {
    assert(circuit_wtab.empty());
    if (circuit_wtab.size() < 2 * vsize)
        circuit_wtab.resize(2 * vsize, Circuit_Watches());
    LOG ("initialized watcher tables");
}

/// @note:  watch.cpp:  clear_watches()
void Internal::circuit_clear_watches () {
    for (auto lit : lits)
        circuit_watches (lit).clear ();
}

/// @note:  watch.cpp:  reset_watches()
void Internal::circuit_reset_watches() {
    assert(!circuit_wtab.empty());
    erase_vector(circuit_wtab);
    LOG ("reset watcher tables");
}

// This can be quite costly since lots of memory is accessed in a rather
// random fashion, and thus we optionally profile it.

/// @note:  watch.cpp:  connect_watches()
void Internal::circuit_connect_watches (bool irredundant_only) {
    START (connect);
    assert (circuit_watching());

    LOG ("watching all %sclauses", irredundant_only ? "irredundant " : "");

    // First connect binary clauses.
    //
    for (const auto &c : circuit_gates) {
        if (irredundant_only && c->redundant)
            continue;
        if (c->garbage || c->size > 2)
            continue;
        circuit_watch_gate(c);
    }

    // Then connect non-binary clauses.
    //
    for (const auto &c : circuit_gates) {
        if (irredundant_only && c->redundant)
            continue;
        if (c->garbage || c->size == 2)
            continue;
        circuit_watch_gate(c);
#if 0 // TODO(taomengxia: 2025/02/26)
        if (!level) {
            const int lit0 = c->literals[0];
            const int lit1 = c->literals[1];
            const signed char tmp0 = val (lit0);
            const signed char tmp1 = val (lit1);
            if (tmp0 > 0)
                continue;
            if (tmp1 > 0)
                continue;
            if (tmp0 < 0) {
                const size_t pos0 = var (lit0).trail;
                if (pos0 < propagated) {
                propagated = pos0;
                LOG ("literal %d resets propagated to %zd", lit0, pos0);
                }
            }
            if (tmp1 < 0) {
                const size_t pos1 = var (lit1).trail;
                if (pos1 < propagated) {
                propagated = pos1;
                LOG ("literal %d resets propagated to %zd", lit1, pos1);
                }
            }
        }
#endif
    }


    STOP (connect);
}

/// @note:  watch.cpp:  sort_watches()
void Internal::circuit_sort_watches() {
    assert(circuit_watching());
    LOG ("sorting watches");
    Circuit_Watches saved;
    for (auto lit : lits) {
        Circuit_Watches &ws = circuit_watches(lit);

        const circuit_const_watch_iterator end = ws.end();
        circuit_watch_iterator j = ws.begin();
        circuit_const_watch_iterator i;

        assert(saved.empty());

        for (i = j; i != end; i++) {
            const Circuit_Watch w = *i;
            if (w.binary())
                *j++ = w;
            else
                saved.push_back(w);
        }

        std::copy (saved.cbegin(), saved.cend(), j);
        saved.clear();
    }
}

} // namespace CaDiCaL