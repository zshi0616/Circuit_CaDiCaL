#ifndef _circuit_bins_hpp_INCLUDED
#define _circuit_bins_hpp_INCLUDED

#include "util.hpp" // Alphabetically after 'bins'.

namespace CaDiCaL {

using namespace std;

struct Circuit_Gate;

struct Circuit_Bin {
    int lit;
    Circuit_Gate *gate;
};

typedef vector<Circuit_Bin> Circuit_Bins;

} // namespace CaDiCaL  

#endif // _circuit_bins_hpp_INCLUDED