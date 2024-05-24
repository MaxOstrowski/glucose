#pragma once

#include "core/MyUtils.cuh"
#include "core/Solver.h"

using namespace Glucose;

typedef unsigned char lbool_device;

struct __attribute__((aligned(16))) AssignVardata {
    lbool_device assign;
    Solver::VarData vardata;
  };

struct binWatchVector {
  unsigned int size;
  Solver::Watcher* watches;
};

union watchVector {
  unsigned int size;
  CRef* crefs;
};

struct MySolver {
  unsigned int host_num_vars;
  unsigned int decision_level;

  Lit* new_trail;
  unsigned int* trail_size;
  Lit* host_trail;
  unsigned int host_trail_size;
  unsigned int* qhead;

  AssignVardata* assigns_vardata;

  unsigned int old_trail_size;
  CRef* confl_host;
  CRef* confl_device;

  binWatchVector* hostBinWatch;
  binWatchVector* watchesBin;
  watchVector* hostWatches;
  watchVector* watches;
  uint32_t* ca;
};

MySolver create_solver(Solver& solver);
void propagate(MySolver& my_solver);
void compare(MySolver &solver, Solver& s, CRef confl);
void destroy_solver(MySolver &solver);



// class MyPropagator {
// public:
//   /// @brief  converts literal into index
//   /// @param l
//   /// @return var(l)*2+sign(l)
//   static int watch_index(Lit l) { return var(l) * 2 + int(sign(l)); }
//   MyPropagator(Solver &solver);
//   ~MyPropagator();
//   CRef propagate();
//   void write_back(Solver &solver); // write back the changes
//   void compare(Solver &solver,
//                CRef confl); // compare the changes with the solver

//   struct __attribute__((aligned(16))) AssignVardata {
//     AssignVardata() : assign(l_Undef), vardata() {}
//     AssignVardata(lbool assign, Solver::VarData vardata)
//         : assign(assign), vardata(vardata) {}
//     lbool assign;
//     Solver::VarData vardata;
//   };

// private:
//   const int num_vars;
//   int decision_level;
//   FixedSizeVector<Lit> new_trail;
//   int old_trail_size;
//   CRef confl;
//   FixedSizeVector<AssignVardata> assigns_vardata;
//   FixedSizeVector<VariableSizedVector<Solver::Watcher>> watchesBin;
//   FixedSizeVector<VariableSizedVector<CRef>> watches;
//   FixedSizeVector<uint32_t> ca;

//   // Add other members here
// };