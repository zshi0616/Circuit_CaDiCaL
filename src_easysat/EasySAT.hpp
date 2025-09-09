#ifndef _easysat_hpp_INCLUDED
#define _easysat_hpp_INCLUDED
/************************************************************************************
EasySAT: A CDCL SAT EasySAT_Solver
================================================================================
Copyright (c) 2022 SeedEasySAT_Solver Beijing.
https://seedsolver.com
help@seedsolver.com

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
************************************************************************************/

#include "../src/internal.hpp"

namespace CaDiCaL {

class EasySAT_Clause {
public:
    int lbd;                    // Literal Block Distance (Gilles & Laurent, IJCAI 2009)
    std::vector<int> lit;       // Literals in this clause
    EasySAT_Clause(int sz): lbd(0) { lit.resize(sz); }
    int& operator [] (int index) { return lit[index]; }
};

class Watcher {
public:
    int idx_clause              // The clause index in clause database.
        , blocker;              // Used to fast guess whether a clause is already satisfied. 
    Watcher(): idx_clause(0), blocker(0) {}
    Watcher(int c, int b): idx_clause(c), blocker(b) {}
};

struct GreaterActivity {        // A compare function used to sort the activities.
    const double *activity;     
    bool operator() (int a, int b) const { return activity[a] > activity[b]; }
    GreaterActivity(): activity(NULL) {}
    GreaterActivity(const double *s): activity(s) {}
};

class EasySAT_Solver {
public:
    std::vector<int>    learnt,                     // The clause indices of the learnt clauses.
                        trail,                      // Save the assigned literal sequence.
                        pos_in_trail,               // Save the decision variables' position in trail.
                        reduce_map;                 // Auxiliary data structure for clause management.
    std::vector<EasySAT_Clause> clause_DB;                  // clause database.
    std::vector<Watcher> *watches;                  // A mapping from literal to clauses.
    int vars, clauses, origin_clauses, conflicts;   // the number of variables, clauses, conflicts.
    int restarts, rephases, reduces;                // the number of conflicts since the last ... .
    int rephase_limit, reduce_limit;                // parameters for when to conduct rephase and reduce.
    int threshold;                                  // A threshold for updating the local_best phase.
    int propagated;                                 // The number of propagted literals in trail.
    int time_stamp;                                 // Aid parameter for conflict analyzation and LBD calculation.   
   
    int lbd_queue[50],                              // circled queue saved the recent 50 LBDs.
        lbd_queue_size,                             // The number of LBDs in this queue
        lbd_queue_pos;                              // The position to save the next LBD.
    double fast_lbd_sum, slow_lbd_sum;              // Sum of the Global and recent 50 LBDs.        
    int *value,                                     // The variable assignement (1:True; -1:False; 0:Undefine) 
        *reason,                                    // The index of the clause that implies the variable assignment.
        *level,                                     // The decision level of a variable      
        *mark,                                      // Aid for conflict analyzation.
        *local_best,                                // A phase with a local deepest trail.                     
        *saved;                                     // Phase saving.
    double *activity;                               // The variables' score for VSIDS.   
    double var_inc;                                 // Parameter for VSIDS.               
    EasySAT_Heap<GreaterActivity> vsids;                    // Heap to select variable.
     
    void alloc_memory();                                    // Allocate memory for EasySAT 
    void assign(int lit, int level, int cref);              // Assigned a variable.
    int  propagate();                                       // BCP
    void backtrack(int backtrack_level);                    // Backtracking
    int  analyze(int cref, int &backtrack_level, int &lbd); // Conflict analyzation.
    int  parse(char *filename);                             // Read CNF file.
    int  solve();                                           // Solving.
    int  decide();                                          // Pick desicion variable.
    int  add_clause(std::vector<int> &c);                    // add new clause to clause database.
    void bump_var(int var, double mult);                     // update activity      
    void restart();                                         // do restart.                                      
    void reduce();                                          // do clause management.
    void rephase();                                         // do rephase.
    void printModel();                                      // print model when the result is SAT.

    int parse_res = 0;
    Internal* internal = nullptr;
};

    int EasySAT_main(int argc, char **argv);

} // namespace CaDiCaL

#endif // _easysat_hpp_INCLUDED
