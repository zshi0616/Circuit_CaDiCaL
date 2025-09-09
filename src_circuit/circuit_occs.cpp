#include "../src/internal.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// Occurrence lists.

void Internal::circuit_init_occs () {
    if (circuit_otab.size () < 2 * vsize)
        circuit_otab.resize (2 * vsize, Circuit_Occs ());
    LOG ("initialized occurrence lists");
}

void Internal::circuit_reset_occs () {
    assert (circuit_occurring ());
    erase_vector (circuit_otab);
    LOG ("reset occurrence lists");
}

/*------------------------------------------------------------------------*/

} // namespace CaDiCaL