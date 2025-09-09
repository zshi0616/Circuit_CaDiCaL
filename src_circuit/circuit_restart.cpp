#include "../src/internal.hpp"

namespace CaDiCaL {

/**
 * @brief:  check need restart or not
 * @note:   restart.cpp: restarting()
 */
bool Internal::circuit_restarting() {
    if (!opts.restart)
        return false;
    /// TODO(taomengxia): cadical use assumptions
    if (stabilizing())
        return reluctant;
    if (stats.conflicts <= lim.restart)
        return false;
    double f = averages.current.glue.fast;
    double margin = (100.0 + opts.restartmargin) / 100.0;
    double s = averages.current.glue.slow, l = margin * s;
    LOG ("EMA glue slow %.2f fast %.2f limit %.2f", s, f, l);
    return l <= f;

}

/**
 * @brief:  restart by backtrack
 * @note:   restart.cpp: restart()
 */
void Internal::circuit_restart() {
    START (restart);
    stats.restarts++;
    stats.restartlevels += level;
    if (stable)
        stats.restartstable++;
    LOG ("restart %" PRId64 "", stats.restarts);
    circuit_backtrack(reuse_trail());

    lim.restart = stats.conflicts + opts.restartint;
    LOG ("new restart limit at %" PRId64 " conflicts", lim.restart);

    report ('R', 2);
    STOP (restart);
}

}
