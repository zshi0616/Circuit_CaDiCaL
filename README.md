# Circuit-CaDiCaL: Circuit SAT Solver Based on CaDiCaL

Authors: [Mengxia Tao](https://github.com/MengxiaTao), Yalun Cai, [Zhengyuan Shi](https://zshi0616.github.io/) and [Qiang Xu](https://cure-lab.github.io/). 

## Overview
This project is a Circuit SAT solver built on top of the CaDiCaL solver, extending its capabilities to handle circuit-based satisfiability problems in And-Inverter Graph (AIG) format.

## Features
- Naturally represent Circuit-SAT problem instances as circuits in AIG format. 
- Perform variable decision with VSIDS heuristic on logic gates. 
- Implement Circuit-based Boolean Constraint Propagation (BCP) on AND gate and INV gate. 
- Implement Circuit-based clause management, the learnt clauses are represented as additional multiple-input AND gates with extra Primary Outputs (POs). 

## Base CaDiCaL
- CaDiCaL URL: https://github.com/arminbiere/cadical
- Commit ID:   31f9aae44947c673dc6190c9beb399acb9ffec6a
- Commit URL:  https://github.com/arminbiere/cadical/commit/31f9aae44947c673dc6190c9beb399acb9ffec6a 
- Version:     2.1.0

## Circuit SAT Solver Core Code
- Parse AAG: Circuit_Parser::parse_aag() in src_circuit/circuit_parser.cpp
- CDCL:      Internal::circuit_cdcl_loop_with_inprocessing() in src_circuit/circuit_interal.cpp

## Building the Project
- Basic Build:     Use `./configure && make` to configure and build `cadical` in the default `build` sub-directory.
- Advanced Build:  See [`BUILD.md`](BUILD.md)

## Supported Solvers
| Solver Type             | Main Code    | Option                | Input file | Example                          |
|-------------------------|--------------|-----------------------|------------|----------------------------------|
| CircuitSAT Solver       | src_circuit/ | default/--satsolver=1 | AAG        | ./cadical test.aag               |
| EasySAT Solver          | src_easysat/ | --satsolver=2         | CNF        | ./cadical --satsolver=2 test.cnf |
| Original CaDiCaL Solver | src/         | --satsolver=3         | CNF        | ./cadical --satsolver=3 test.cnf |

## Reference
```sh
@misc{circuit_cadical,
  author       = {Tao, Mengxia and Cai, Yalun and Shi, Zhengyuan and Xu, Qiang},
  title        = {Circuit-CaDiCaL: Circuit SAT Solver Based on CaDiCaL},
  howpublished = {\url{https://github.com/cure-lab/Circuit_CaDiCaL}},
  year         = {2025},
}
```
