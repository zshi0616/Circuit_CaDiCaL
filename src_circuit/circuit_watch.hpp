#ifndef _circuit_watch_hpp_INCLUDED
#define _circuit_watch_hpp_INCLUDED

#include <vector>

namespace CaDiCaL {

struct Circuit_Gate;

struct Circuit_Watch {
    Circuit_Gate* gate;
    int blit;
    int size;

    Circuit_Watch(int b, Circuit_Gate* g) : gate(g), blit(b), size(g->size) {}
    Circuit_Watch() {}

    bool binary() const { return size == 2; }
};

typedef std::vector<Circuit_Watch> Circuit_Watches;  // of one literal

typedef Circuit_Watches::iterator circuit_watch_iterator;
typedef Circuit_Watches::const_iterator circuit_const_watch_iterator;

inline void circuit_remove_watch(Circuit_Watches &ws, Circuit_Gate *gate) {
    const auto end = ws.end();
    auto i = ws.begin();
    for (auto j = i; j != end; j++) {
        const Circuit_Watch &w = *i++ = *j;
        if (w.gate == gate)
            i--;
    }
    assert(i + 1 == end);
    ws.resize(i - ws.begin());
}

} // namespace CaDiCaL

#endif
