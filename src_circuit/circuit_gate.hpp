#ifndef _circuit_gate_hpp_INCLUDED
#define _circuit_gate_hpp_INCLUDED

#include <cassert>

namespace CaDiCaL {

typedef int *circuit_literal_iterator;
typedef const int* circuit_const_literal_iterator;

struct Circuit_Gate {
    union {
        uint64_t id;
        Circuit_Gate *copy;                        /// Only valid if 'moved', then that's where to.
    };

    bool garbage : 1;                                   /// can be garbage
    bool hyper : 1;                                     /// redundant hyper binary or ternary resolved
    bool keep : 1;                                      /// always keep this clause (if redundant)
    bool moved : 1;                                     /// moved during garbage collector ('copy' valid)
    bool reason : 1;                                    /// reason / antecedent clause can not be collected
    bool redundant : 1;                                 /// aka 'learned' so not 'irredundant' (original)
    bool transred : 1;                                  /// already checked for transitive reduction
    bool subsume : 1;                                   /// not checked in last subsumption round
    unsigned used : 2;                                  /// resolved in conflict analysis since last 'reduce'

    int glue;                                           /// glue/lbd
    int size;
    int pos;                                            /// Position of last watch replacement [Gent'13].

    int literals[];   /// 1. original gates: {input_1 * watch_value_1, input_2 * watch_value_2,...,output * watch_value}
                      /// 2. learned gates:  {input_1 * watch_value_1, input_2 * watch_value_2,...,input_n * watch_value_n}

    circuit_literal_iterator begin() { return literals; }
    circuit_literal_iterator end()   { return literals + size; }
    
    circuit_const_literal_iterator begin() const { return literals; }
    circuit_const_literal_iterator end()   const { return literals + size; }

    static size_t bytes(int size) {
        assert (size > 1);
        const size_t header_bytes = sizeof(Circuit_Gate);
        const size_t actual_literal_bytes = size * sizeof(int);
        size_t combined_bytes = header_bytes + actual_literal_bytes;
        size_t aligned_bytes = align (combined_bytes, 8);
        return aligned_bytes; 
    }
    size_t bytes() const { return bytes(size); }

    bool collect() const { return !reason && garbage; }
};

} // namespace CaDiCaL

#endif  // _circuit_gate_hpp_INCLUDED