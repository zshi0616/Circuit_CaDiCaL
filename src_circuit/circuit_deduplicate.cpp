#include "../src/internal.hpp"

namespace CaDiCaL {

void Internal::circuit_mark_duplicated_binary_clauses_as_garbage() {
    // TODO(taomengxia: 2025/02/25): disable, need enable and test later
    return;

    if (!opts.deduplicate)
        return;
    if (unsat)
        return;
    if (terminated_asynchronously())
        return;
    
    START_SIMPLIFIER (deduplicate, DEDUP);
    stats.deduplications++; 

    assert (!level);
    assert (circuit_watching());

    vector<int> stack; // To save marked literals and unmark them later.

    int64_t subsumed = 0;
    int64_t units = 0;

    for (auto idx : vars) {

        if (unsat)
            break;
        if (!active(idx))
            continue;
        int unit = 0;

        for (int sign = -1; !unit && sign <= 1; sign += 2) {

            const int lit = sign * idx; // Consider all literals.

            assert(stack.empty());
            Circuit_Watches &ws = circuit_watches(lit);

            // We are removing references to garbage clause. Thus no 'auto'.
            const circuit_const_watch_iterator end = ws.end();
            circuit_watch_iterator j = ws.begin();
            circuit_const_watch_iterator i;

            for (i = j; !unit && i != end; i++) {
                Circuit_Watch w = *j++ = *i;
                if (!w.binary())
                    continue;
                int other = w.blit;
                const int tmp = marked(other);
                Circuit_Gate *c = w.gate;

                if (tmp > 0) {  // Found duplicated binary clause.
                    if (c->garbage) {
                        j--;
                        continue;
                    }

                    // The previous identical clause 'd' might be redundant and if the
                    // second clause 'c' is not (so irredundant), then we have to keep
                    // 'c' instead of 'd', thus we search for it and replace it.
                    if (!c->redundant) {
                        circuit_watch_iterator k;
                        for (k = ws.begin();; k++) {
                            assert(k != i);
                            if (!k->binary())
                                continue;
                            if (k->blit != other)
                                continue;
                            Circuit_Gate *d = k->gate;
                            if (d->garbage)
                                continue;
                            c = d;
                            break;
                        }
                        *k = w;
                    }
                    stats.subsumed++;
                    stats.deduplicated++;
                    subsumed++;
                    circuit_mark_garbage(c);
                    j--;
                } else if (tmp < 0) {
                    unit = -lit;
                    units++;
                    while (i != end) {
                        *j++ = *i++;
                    }
                } else {
                    if (c->garbage)
                        continue;
                    mark (other);
                    stack.push_back(other);
                }
            }
            if (j == ws.begin())
                erase_vector (ws);
            else if (j != end)
                ws.resize(j - ws.begin());
            
            for (const auto &other : stack)
                unmark(other);

            stack.clear();
        }

        if (unit) {
            stats.failed++;
            stats.hyperunary++;
            circuit_assign_unit(unit);

            if (!circuit_propagate()) {
                LOG ("empty clause after propagating unit");
                circuit_learn_empty_clause ();  
            }
        }
    }

    STOP_SIMPLIFIER (deduplicate, DEDUP);

    report ('2', !opts.reportall && !(subsumed + units));
}

} // namespace CaDiCaL