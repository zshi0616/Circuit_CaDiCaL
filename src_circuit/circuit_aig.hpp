#ifndef _circuit_aig_hpp_INCLUDED
#define _circuit_aig_hpp_INCLUDED

#include <cstddef>
#include <cassert>
#include <vector>
#include <string>


// id is even: no inverter, map to postive
// id is odd:  has inverter, map to negative
constexpr int AIG_ID_CONVERT(int id) {
    return (id / 2) * (id % 2 ? -1 : 1);
}

namespace CaDiCaL {

class Circuit_LogicGate {
public:
    Circuit_LogicGate(const int po, const std::vector<int> &pis) : m_PO(po), m_PIs(pis) {}
    virtual ~Circuit_LogicGate() = default;

    int get_PO()                        const { return m_PO; }
    const std::vector<int> &get_PIs()   const { return m_PIs; }

    virtual std::string type() const = 0;

protected:
    int m_PO;
    std::vector<int> m_PIs;
};

class Circuit_AndGate final: public Circuit_LogicGate {
public:
    Circuit_AndGate(int po, const std::vector<int>& pis) : Circuit_LogicGate(po, pis) {}

    std::string type() const override { return "AND"; }
};

class Circuit_Graph {
public:
    Circuit_Graph(const int inputs_num, const int outputs_num, const int and_num) {
        m_inputs.reserve(inputs_num);
        m_outputs.reserve(outputs_num);
        m_gates.reserve(and_num);
    }

    ~Circuit_Graph() {
        for (auto gate : m_gates) {
            delete gate;
        }
    }

    void add_input(const int input);
    void add_output(const int output);
    void add_and_gate(const int output, const std::vector<int> &inputs);

    int get_num_inputs()    const { return m_inputs.size(); }
    int get_num_outputs()   const { return m_outputs.size(); }
    int get_num_gates()     const { return m_gates.size(); }

    const std::vector<int> &get_inputs()                  const { return m_inputs; }
    const std::vector<int> &get_outputs()                 const { return m_outputs; }
    const std::vector<Circuit_LogicGate*> &get_gates()    const { return m_gates; }

private:
    std::vector<int> m_inputs;
    std::vector<int> m_outputs;
    std::vector<Circuit_LogicGate*> m_gates;
};

} // namespace CaDiCaL  

#endif // _circuit_aig_hpp_INCLUDED
