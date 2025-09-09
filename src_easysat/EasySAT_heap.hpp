#ifndef _circuit_heap_hpp_INCLUDED
#define _circuit_heap_hpp_INCLUDED

#include <iostream>
#include <cassert>
#include <cstdint>
#include <cstddef>
#include <vector>

#define left(x) (x << 1 | 1)
#define right(x) ((x + 1) << 1)
#define father(x) ((x - 1) >> 1)

namespace CaDiCaL {

template<class Comp>
class EasySAT_Heap {
    Comp lt;
    std::vector<int> heap;
    std::vector<int> pos;
    
    void up(int v) {
        int x = heap[v], p = father(v);
        while (v && lt(x, heap[p])) {
            heap[v] = heap[p], pos[heap[p]] = v;
            v = p, p = father(p);
        }
        heap[v] = x, pos[x] = v;
    }

    void down(int v) {
        int x = heap[v];
        while (left(v) < (int)heap.size()){
            int child = right(v) < (int)heap.size() && lt(heap[right(v)], heap[left(v)]) ? right(v) : left(v);
            if (!lt(heap[child], x)) break;
            heap[v] = heap[child], pos[heap[v]] = v, v = child;
        }
        heap[v] = x, pos[x] = v;
    }

public:
    void setComp   (Comp c)              { lt = c; }
    bool empty     ()              const { return heap.size() == 0; }
    bool inHeap    (int n)         const { return n < (int)pos.size() && pos[n] >= 0; }
    void update    (int x)               { up(pos[x]); }
    void down_update    (int x)               { down(pos[x]); }

    void insert(int x) {
        if ((int)pos.size() < x + 1) 
            pos.resize(x + 1, -1);
        pos[x] = heap.size();
        heap.push_back(x);
        up(pos[x]); 
    }

    int pop() {
        int x = heap[0];
        heap[0] = heap.back();
        pos[heap[0]] = 0, pos[x] = -1;
        heap.pop_back();
        if (heap.size() > 1) down(0);
        return x; 
    }
};


struct Circuit_GreaterActivity {        // A compare function used to sort the activities. 0927
    const double* activity;
    bool operator() (int a, int b) const {
        if (activity[a] == activity[b])return a > b;
        return activity[a] > activity[b];
    }
    Circuit_GreaterActivity() : activity(NULL) {}
    Circuit_GreaterActivity(const double* s) : activity(s) {}
};

}  // namespace CaDiCaL  


#endif //_circuit_heap_hpp_INCLUDED
