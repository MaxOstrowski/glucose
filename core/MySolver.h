#pragma once

#include "core/MyUtils.h"
#include "core/Solver.h"

using namespace Glucose;

class MyPropagator {
public:
  /// @brief  converts literal into index
  /// @param l
  /// @return var(l)*2+sign(l)
  static int watch_index(Lit l) { return var(l) * 2 + int(sign(l)); }
  MyPropagator(Solver &solver);
  ~MyPropagator() {
    // delete vectors
    delete_vector(new_trail);
    delete_vector(assigns_vardata);
    for (int i = 0; i < watchesBin.size(); i++) {
      delete_vector(watchesBin[i]);
    }
    for (int i = 0; i < watches.size(); i++) {
      delete_vector(watches[i]);
    }
    delete_vector(watchesBin);
    delete_vector(watches);
    delete_vector(ca);
  }
  CRef propagate(int& num_props);
  void write_back(Solver &solver); // write back the changes

  struct __attribute__((aligned(16))) AssignVardata {
    AssignVardata() : assign(l_Undef), vardata() {}
    AssignVardata(lbool assign, Solver::VarData vardata) : assign(assign), vardata(vardata) {}
    lbool assign;
    Solver::VarData vardata;
  };

private:
  const int num_vars;
  int decision_level;
  FixedSizeVector<Lit> new_trail;
  int old_trail_size;
  CRef confl;
  FixedSizeVector<AssignVardata> assigns_vardata;
  FixedSizeVector<VariableSizedVector<Solver::Watcher>> watchesBin;
  FixedSizeVector<VariableSizedVector<CRef>> watches;
  FixedSizeVector<uint32_t> ca;

  // Add other members here
};