#include "../src/internal.hpp"

namespace CaDiCaL {

/**
 * @brief:  Check need rephase or not
 * @note:   rephase.cpp: rephasing()
 */
bool Internal::circuit_rephasing() {
    if (!opts.rephase)
        return false;
    if (opts.forcephase)
        return false;
    return stats.conflicts > lim.rephase;
}

/**
 * @brief:  Pick the original default phase.
 * @note:   rephase.cpp:    rephase_original()
 */
char Internal::circuit_rephase_original() {
    stats.rephased.original++;
    signed char val = opts.phase ? 1 : -1; // original = initial
    PHASE ("rephase", stats.rephased.total, "switching to original phase %d",
            val);
    for (auto idx : vars)
    phases.saved[idx] = val;
    return 'O';
}

/**
 * @brief:  Pick the inverted original default phase.
 * @note:   rephase.cpp:    rephase_inverted()
 */
char Internal::circuit_rephase_inverted() {
    stats.rephased.inverted++;
    signed char val = opts.phase ? -1 : 1; // original = -initial
    PHASE ("rephase", stats.rephased.total,
           "switching to inverted original phase %d", val);
    for (auto idx : vars)
        phases.saved[idx] = val;
    return 'I';
}

/**
 * @brief:  Flip the current phase.
 * @note:   rephase.cpp:    rephase_flipping()
 */
char Internal::circuit_rephase_flipping() {
    stats.rephased.flipped++;
    PHASE ("rephase", stats.rephased.total,
           "flipping all phases individually");
    for (auto idx : vars)
        phases.saved[idx] *= -1;
    return 'F';
}

/**
 * @brief:  Complete random picking of phases.
 * @note:   rephase.cpp:    rephase_random()
 */
char Internal::circuit_rephase_random() {
    stats.rephased.random++;
    PHASE ("rephase", stats.rephased.total, "resetting all phases randomly");
    Random random (opts.seed);       // global seed
    random += stats.rephased.random; // different every time
    for (auto idx : vars)
        phases.saved[idx] = random.generate_bool () ? -1 : 1;
    return '#';
}

/**
 * @note:   rephase.cpp:    rephase_best()
 */
char Internal::circuit_rephase_best() {
    stats.rephased.best++;
    PHASE ("rephase", stats.rephased.total,
           "overwriting saved phases by best phases");
    signed char val;
    for (auto idx : vars)
    if ((val = phases.best[idx]))
        phases.saved[idx] = val;
    return 'B';
}

/**
 * @note:   rephase.cpp:    rephase_walk()
 */
char Internal::circuit_rephase_walk() {
    stats.rephased.walk++;
    PHASE ("rephase", stats.rephased.total,
           "starting local search to improve current phase");
    // walk (); // TODO(taomengxia 20250124)
    return 'W';
}

/**
 * @brief:  Rephase
 * @note:   rephase.cpp: rephase()
 */
void Internal::circuit_rephase() {
    stats.rephased.total++;
    PHASE("rephase", stats.rephased.total,
           "reached rephase limit %" PRId64 " after %" PRId64 " conflicts",
           lim.rephase, stats.conflicts);

    // Report current 'target' and 'best' and then set 'rephased' below, which
    // will trigger reporting the new 'target' and 'best' after updating it in
    // the next 'update_target_and_best' called from the next 'backtrack'.
    //
    report('~', 1);

    circuit_backtrack();
    clear_phases(phases.target);
    target_assigned = 0;

    size_t count = lim.rephased[stable]++;
    bool single;
    char type;

    if (opts.stabilize && opts.stabilizeonly)
        single = true;
    else
        single = !opts.stabilize;
    
    const bool walk = false;    // TODO(taomengxia:2025/03/04): support opts.walk [const bool walk = opts.walk; ]

    if (single && !walk) {
        // (inverted,best,flipping,best,random,best,original,best)^\omega
        switch (count % 8) {
        case 0:
            type = circuit_rephase_inverted();
            break;
        case 1:
            type = circuit_rephase_best();
            break;
        case 2:
            type = circuit_rephase_flipping();
            break;
        case 3:
            type = circuit_rephase_best();
            break;
        case 4:
            type = circuit_rephase_random();
            break;
        case 5:
            type = circuit_rephase_best();
            break;
        case 6:
            type = circuit_rephase_original();
            break;
        case 7:
            type = circuit_rephase_best();
            break;
        default:
            type = 0;
            break;
        }
    } else if (single && walk) {
        // (inverted,best,walk,
        //  flipping,best,walk,
        //    random,best,walk,
        //  original,best,walk)^\omega
        switch (count % 12) {
        case 0:
            type = circuit_rephase_inverted();
            break;
        case 1:
            type = circuit_rephase_best();
            break;
        case 2:
            type = circuit_rephase_walk();
            break;
        case 3:
            type = circuit_rephase_flipping();
            break;
        case 4:
            type = circuit_rephase_best();
            break;
        case 5:
            type = circuit_rephase_walk();
            break;
        case 6:
            type = circuit_rephase_random();
            break;
        case 7:
            type = circuit_rephase_best();
            break;
        case 8:
            type = circuit_rephase_walk();
            break;
        case 9:
            type = circuit_rephase_original();
            break;
        case 10:
            type = circuit_rephase_best();
            break;
        case 11:
            type = circuit_rephase_walk();
            break;
        default:
            type = 0;
            break;
        }
    } else if (stable && !walk) {
        // original,inverted,(best,original,best,inverted)^\omega
        if (!count)
            type = circuit_rephase_original();
        else if (count == 1)
            type = circuit_rephase_inverted();
        else
            switch ((count - 2) % 4) {
            case 0:
                type = circuit_rephase_best();
                break;
            case 1:
                type = circuit_rephase_original();
                break;
            case 2:
                type = circuit_rephase_best();
                break;
            case 3:
                type = circuit_rephase_inverted();
                break;
            default:
                type = 0;
                break;
            }
    } else if (stable && walk) {
        // original,inverted,(best,walk,original,best,walk,inverted)^\omega
        if (!count)
            type = circuit_rephase_original();
        else if (count == 1)
            type = circuit_rephase_inverted();
        else
            switch ((count - 2) % 6) {
            case 0:
                type = circuit_rephase_best();
                break;
            case 1:
                type = circuit_rephase_walk();
                break;
            case 2:
                type = circuit_rephase_original();
                break;
            case 3:
                type = circuit_rephase_best();
                break;
            case 4:
                type = circuit_rephase_walk();
                break;
            case 5:
                type = circuit_rephase_inverted();
                break;
            default:
                type = 0;
                break;
            }
    } else if (!stable && (!walk || !opts.walknonstable)) {
        // flipping,(random,best,flipping,best)^\omega
        if (!count)
            type = circuit_rephase_flipping();
        else
            switch ((count - 1) % 4) {
            case 0:
                type = circuit_rephase_random();
                break;
            case 1:
                type = circuit_rephase_best();
                break;
            case 2:
                type = circuit_rephase_flipping();
                break;
            case 3:
                type = circuit_rephase_best();
                break;
            default:
                type = 0;
                break;
            }
    } else {
        assert(!stable && walk && opts.walknonstable);
        // flipping,(random,best,walk,flipping,best,walk)^\omega
        if (!count)
            type = circuit_rephase_flipping();
        else
            switch ((count - 1) % 6) {
            case 0:
                type = circuit_rephase_random();
                break;
            case 1:
                type = circuit_rephase_best();
                break;
            case 2:
                type = circuit_rephase_walk();
                break;
            case 3:
                type = circuit_rephase_flipping();
                break;
            case 4:
                type = circuit_rephase_best();
                break;
            case 5:
                type = circuit_rephase_walk();
                break;
            default:
                type = 0;
                break;
            }
    }
    assert(type);

    int64_t delta = opts.rephaseint * (stats.rephased.total + 1);
    lim.rephase = stats.conflicts + delta;

    PHASE("rephase", stats.rephased.total,
          "new rephase limit %" PRId64 " after %" PRId64 " conflicts",
          lim.rephase, delta);

    // This will trigger to report the effect of this new set of phases at the
    // 'backtrack' (actually 'update_target_and_best') after the next
    // conflict, as well as resetting 'best_assigned' then to allow to compute
    // a new "best" assignment at that point.
    //
    last.rephase.conflicts = stats.conflicts;
    rephased = type;

    if (stable)
        shuffle_scores();
    else
        shuffle_queue();
}

}
