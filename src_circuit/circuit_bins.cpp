#include "../src/internal.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// Binary implication graph lists.

/// @note: bins.cpp: init_bins()
void Internal::circuit_init_bins() {
    assert(circuit_big.empty());
    if (circuit_big.size () < 2 * vsize)
        circuit_big.resize(2 * vsize, Circuit_Bins());
    LOG ("initialized binary implication graph");   
}

/// @note: bins.cpp: reset_bins()
void Internal::circuit_reset_bins() {
    assert(!circuit_big.empty());
    erase_vector(circuit_big);
    LOG ("reset binary implication graph");
}

} // namespace CaDiCaL