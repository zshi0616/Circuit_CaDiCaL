#include "circuit_aig.hpp"

namespace CaDiCaL {

void Circuit_Graph::add_input(const int input) {
    assert(input % 2 == 0);
    m_inputs.push_back(input / 2);
}

void Circuit_Graph::add_output(const int output) {
    const int output_id = AIG_ID_CONVERT(output);
    m_outputs.push_back(output_id);
}

void Circuit_Graph::add_and_gate(const int output, const std::vector<int> &inputs) {
    assert(output % 2 == 0);

    std::vector<int> inputs_id;
    for (const auto input : inputs) {
        const int input_id = AIG_ID_CONVERT(input);
        inputs_id.push_back(input_id);
    }

    const int output_id = output / 2;
    const auto gate = new Circuit_AndGate(output_id, inputs_id);
    m_gates.emplace_back(gate);
}

}
