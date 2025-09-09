#include "../src/internal.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/


// Signed marking or unmarking of a gate

/**
 * @note:   clause.cpp: mark(Clause *)
 */
void Internal::circuit_mark(Circuit_Gate *g) {
    for (const auto &lit : *g) {
        mark(lit);        
    }
}

/**
 * @note:   clause.cpp: unmark(Clause*)
 */
void Internal::circuit_unmark(Circuit_Gate *g) {
    for (const auto &lit : *g) {
        unmark(lit);
    }
}

/*------------------------------------------------------------------------*/

void Internal::circuit_mark_added(int lit, int size, bool redundant) {
    mark_subsume(lit);

    (void)size, (void)redundant;
#if 0 // TODO
    if (size == 3)
        mark_ternary (lit);
    if (!redundant)
        mark_block (lit);
#endif
}

/// @note:  clause.cpp: mark_added(Clause *c)
void Internal::circuit_mark_added (Circuit_Gate *g) {
//    LOG (c, "marking added");
    assert (circuit_likely_to_be_kept_clause (g));

    for (const auto &lit : *g)
        circuit_mark_added(lit, g->size, g->redundant);
}

/*------------------------------------------------------------------------*/

/**
 * @brief:  Create a new gate
 * @note:   clause.cpp: new_clause()
 * @param:  red     is redundant or not
 * @param:  glue          glue for gate
 */
Circuit_Gate* Internal::circuit_new_gate(bool red, int glue) {
    assert(clause.size() <= (size_t) INT_MAX);
    const int size = (int) clause.size ();
    assert (size >= 2);

    if (glue > size)
        glue = size;

    // Determine whether this clauses should be kept all the time.
    //
    bool keep;
    if (!red)
        keep = true;
    else if (glue <= opts.reducetier1glue)
        keep = true;
    else
        keep = false;

    size_t bytes = Circuit_Gate::bytes(size);
    Circuit_Gate *g = (Circuit_Gate*) new char[bytes];

    g->id = ++clause_id;
    g->garbage = false;
    g->hyper = false;
    g->keep = keep;
    g->moved = false;
    g->reason = false;
    g->redundant = red;
    g->transred = false;
    g->subsume = false;
    g->used = 0;

    g->glue = glue;
    g->size = size;
    g->pos = 2;

    for (int i = 0; i < size; i++)
        g->literals[i] = clause[i];

    assert(g->bytes() == bytes);

    stats.current.total++;
    stats.added.total++;

    if (red) {
        stats.current.redundant++;
        stats.added.redundant++;
    } else {
        stats.irrlits += size;
        stats.current.irredundant++;
        stats.added.irredundant++;
    }

    circuit_gates.push_back(g);

    if (circuit_likely_to_be_kept_clause(g))
        circuit_mark_added(g);

    return g;
}

/**
 * @brief:  promote gate g with new_glue
 * @note:   clause.cpp: promote_clause()
 * @param:  g            ptr of gate
 * @param:  new_glue     recompute glue for g
 */
void Internal::circuit_promote_gate(Circuit_Gate *g, int new_glue) {
    assert (g->redundant);
    if (g->keep)
        return;
    if (g->hyper)
        return;
    int old_glue = g->glue;
    if (new_glue >= old_glue)
        return;
    if (!g->keep && new_glue <= opts.reducetier1glue) {
        // LOG (g, "promoting with new glue %d to tier1", new_glue);
        stats.promoted1++;
        g->keep = true;
    } else if (old_glue > opts.reducetier2glue &&
               new_glue <= opts.reducetier2glue) {
        // LOG (g, "promoting with new glue %d to tier2", new_glue);
        stats.promoted2++;
        g->used = 2;
    } else if (g->keep) {
        // LOG (g, "keeping with new glue %d in tier1", new_glue);
    } else if (old_glue <= opts.reducetier2glue) {
        // LOG (g, "keeping with new glue %d in tier2", new_glue);
    } else {
        // LOG (g, "keeping with new glue %d in tier3", new_glue);
    }
    stats.improvedglue++;
    g->glue = new_glue;
}

/**
 * @brief:  shrink gate
 * @note:   clause.cpp: shrink_clause()
 */
size_t Internal::circuit_shrink_gate( Circuit_Gate *g, int new_size) {
    assert(new_size >= 2);
    int old_size = g->size;
    assert(new_size < old_size);
#ifndef NDEBUG
    for (int i = new_size; i < g->size; i++) {
        g->literals[new_size] = 0;
    }
#endif

    if (g->pos >= new_size)
        g->pos = 2;

    size_t old_bytes = g->bytes();
    g->size = new_size;
    size_t new_bytes = g->bytes();
    size_t res = old_bytes - new_bytes;

    if (g->redundant) {
        circuit_promote_gate(g, min(g->size - 1, g->glue));
    } else {
        int delta_size = old_size - new_size;
        assert(stats.irrlits >= delta_size);
        stats.irrlits -= delta_size;
    }

    if (circuit_likely_to_be_kept_clause (g))
        circuit_mark_added (g);

    return res;
}

/**
 * @brief
 * @note:   clause.cpp: deallocate_clause()
 */
void Internal::circuit_deallocate_gate(Circuit_Gate *g) {
    char *p = (char*)g;
    if (arena.contains(p))
        return;
    delete[] p;
}

/**
 * @brief:
 * @note:    clause.cpp: delete_clause()
 */
void Internal::circuit_delete_gate(Circuit_Gate *g) {
    circuit_deallocate_gate(g);
}

/**
 * @brief:  Mark the gate as garbage
 * @note:   clause.cpp: mark_garbage()
 * @param:  g    ptr of gate
 */
void Internal::circuit_mark_garbage(Circuit_Gate* g) {
    assert(!g->garbage);

    assert (stats.current.total > 0);
    stats.current.total--;

    size_t bytes = g->bytes();
    if (g->redundant) {
        assert (stats.current.redundant > 0);
        stats.current.redundant--;
    } else {
        assert (stats.current.irredundant > 0);
        stats.current.irredundant--;
        assert (stats.irrlits >= g->size);
        stats.irrlits -= g->size;
    }

    stats.garbage.bytes += bytes;
    stats.garbage.clauses++;
    stats.garbage.literals += g->size;
    g->garbage = true;
    g->used = 0;

//    LOG (g, "marked garbage pointer %p", (void *) g);
}

/**
 * @beief:  Assign for original unit
 * @note:   clause.cpp: assign_original_unit()
 * @param   lit (gate_id * gate_val)
 */
void Internal::circuit_assign_original_unit(int lit) {
    assert (!level);
    assert (!unsat);
    const int idx = vidx(lit);
    assert(!vals[idx]);
    Var &v = var (idx);
    v.level = 0;
    v.trail = (int)trail.size();
    v.reason = nullptr;
    v.circuit_reason = nullptr;

    const signed char tmp = sign(lit);
    circuit_set_val(idx, tmp);
    trail.push_back(lit);
    num_assigned++;
    LOG ("original unit assign %d", lit);
    assert(num_assigned == trail.size());
    mark_fixed(lit);

    if (circuit_propagate())
        return;
    assert(circuit_conflict_gate ||
           (circuit_conflict_direct[0] && circuit_conflict_direct[1]));
    LOG ("propagation of original unit results in conflict");
    circuit_learn_empty_clause ();
}

/**
 * @brief:  Add learned new gate during conflict analysis and watch it
 * @note:   clause.cpp: new_learned_redundant_clause()
*/
Circuit_Gate *Internal::circuit_new_learned_redundant_gate(int glue) {
    assert(clause.size () > 1);
    auto res = circuit_new_gate(true, glue);

    /// add watch
    circuit_watch_gate(res);
    return res;
}

/**
 * @brief:  Add hyper binary resolved clause during 'probing'.
 * @note:   clause.cpp:     new_hyper_binary_resolved_clause()
 */
Circuit_Gate *Internal::circuit_new_hyper_binary_resolved_clause(bool red, int glue) {
    assert(clause.size() == 2);
    auto res = circuit_new_gate(red, glue);

    assert(circuit_watching());
    // add watch
    circuit_watch_gate(res);
    return res;
}

}
