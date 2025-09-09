#ifndef _circuit_parser_hpp_INCLUDED
#define _circuit_parser_hpp_INCLUDED

#include <string>
#include <vector>
#include <fstream>

namespace CaDiCaL {

struct Internal;

class Circuit_Parser {
    Solver* solver;
    Internal *internal;

public:
    Circuit_Parser(Solver* s) : solver(s), internal(s->internal) {}

    const char* parse_aag(const char* path, int& vars);

    std::vector<std::string> m_split(const std::string& input, const std::string& pred);
};

} // namespace CaDiCaL

#endif // _circuit_parser_hpp_INCLUDED
