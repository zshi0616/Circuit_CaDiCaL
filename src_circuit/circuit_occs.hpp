#ifndef _circuit_occs_h_INCLUDED
#define _circuit_occs_h_INCLUDED


#include <vector>

namespace CaDiCaL {

struct Circuit_Gate;
using namespace std;

typedef vector<Circuit_Gate*> Circuit_Occs;

} // namespace CaDiCaL

#endif  // _circuit_occs_h_INCLUDED