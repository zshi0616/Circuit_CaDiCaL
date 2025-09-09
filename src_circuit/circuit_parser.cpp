#include "../src/internal.hpp"

namespace CaDiCaL {

const char* Circuit_Parser::parse_aag(const char* path, int& vars) {
    std::ifstream file(path);
    if (!file.good())
        return internal->error_message.init ("failed to read aag file '%s'", path);

    START (parse);
    int line_ctr = 0;
    int inputs_num = 0;
    int outputs_num = 0;
    int num = 0;
    int and_num = 0;

    Circuit_Graph* graph_ptr = nullptr;
    for (std::string line; std::getline(file, line, '\n');)  {
        ++line_ctr;
        if(line.find("aag") != std::string::npos) {
            std::vector<std::string> temp = m_split(line, " ");
            and_num = std::stoi(temp[5]);
            if (and_num == 0) {
                internal->unsat = true;
                STOP (parse);
                return 0;
            }
            num = std::stoi(temp[1]);
            vars = num;
            solver->reserve(vars);

            inputs_num = std::stoi(temp[2]);
            outputs_num = std::stoi(temp[4]);
            
            graph_ptr = new Circuit_Graph(inputs_num, outputs_num, and_num);
            continue;
        }

        if(line_ctr > 1 && line_ctr <= inputs_num + 1) {
            graph_ptr->add_input(std::stoi(line));
            continue;
        }
    
        if(line_ctr > inputs_num + 1 && line_ctr <= inputs_num + outputs_num + 1) {
            graph_ptr->add_output(std::stoi(line));
            continue;
        }
        if(line_ctr <= num + outputs_num + 1) {
            std::vector<std::string> gate = m_split(line, " ");
            int output = std::stoi(gate[0]);
            int input1 = std::stoi(gate[1]);
            int input2 = std::stoi(gate[2]);
            graph_ptr->add_and_gate(output, {input1, input2});

            auto mark_flag_func = [this](int id) {
                Flags &f = internal->flags (id);
                if (f.status == Flags::UNUSED)
                    internal->mark_active (id);
                else if (f.status != Flags::ACTIVE && f.status != Flags::FIXED)
                    internal->reactivate (id);
            };
            mark_flag_func(input1 / 2);
            mark_flag_func(input2 / 2);
            mark_flag_func(output / 2);

            continue;
        }
    }

    assert (graph_ptr->get_num_gates() == and_num &&
            graph_ptr->get_num_inputs() == inputs_num &&
            graph_ptr->get_num_gates() == and_num);

    internal->circuit_init(graph_ptr);
    delete graph_ptr;

    STOP (parse);
    return 0;
}

std::vector<std::string> Circuit_Parser::m_split(const std::string& input, const std::string& pred) {
    std::vector<std::string> result;
    std::string temp{""};
    unsigned count1 = input.size();
    unsigned count2 = pred.size();
    unsigned j;
    for (size_t i = 0; i < count1; i++) {
        for(j = 0; j < count2; j++) {
            if(input[i] == pred[j]) {
                break;
            }
        }
        //if input[i] != pred中的任何一个 该字符加到temp上
        if(j == count2) {
            temp += input[i];
        } else {
            if(!temp.empty()) {
                result.push_back(temp);
                temp.clear();
            }
        }
    }
    if(!temp.empty()) {
        result.push_back(temp);
        temp.clear();
    }
    return result;
}

} // namespace CaDiCaL
