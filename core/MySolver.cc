#include "core/MySolver.h"
#include "core/MyUtils.h"
#include "core/Solver.h"
#include "core/SolverTypes.h"
#include <algorithm>
#include <iostream>

using namespace Glucose;

/// @brief This propagation is meant to do everything in parallel
/// also it does not change the clause database, it uses 1 Literal watches
/// Afterwards, the watches and the clauses need to be restored to old style
/// @param solver
MyPropagator::MyPropagator(Solver &solver)
    : num_vars(solver.nVars()), decision_level(solver.decisionLevel()), new_trail(FixedSizeVector<Lit>(num_vars, &solver.trail[solver.qhead], solver.trail.size() - solver.qhead)),
      old_trail_size(solver.trail.size() - solver.qhead), confl(CRef_Undef), assigns_vardata(FixedSizeVector<AssignVardata>(num_vars)),
      watchesBin(FixedSizeVector<VariableSizedVector<Solver::Watcher>>(num_vars * 2 + 1)), watches(FixedSizeVector<VariableSizedVector<CRef>>(num_vars * 2 + 1)),
      ca(FixedSizeVector<uint32_t>(solver.ca.size() * 2, reinterpret_cast<uint32_t *>(solver.ca.lea(0)), solver.ca.size())) {

  // copy assigns and vardata
  for (int i = 0; i < num_vars; i++) {
    assigns_vardata.push_back(MyPropagator::AssignVardata(solver.assigns[i], solver.vardata[i]));
  }

  for (Var v = 0; v < num_vars; ++v) {
    {
      Lit lit = mkLit(v, false);
      auto dummy = watch_index(lit);
      vec<Solver::Watcher> &watchlist = solver.watchesBin[lit];
      watchesBin[watch_index(lit)].append(&watchlist[0], watchlist.size());
    }

    {
      Lit lit = mkLit(v, true);
      auto dummy = watch_index(lit);
      vec<Solver::Watcher> &watchlist = solver.watchesBin[lit];
      watchesBin[watch_index(lit)].append(&watchlist[0], watchlist.size());
    }
  }

  // create nary watches like binary watches
  for (Var v = 0; v < num_vars; ++v) {
    {
      Lit lit = mkLit(v, false);
      vec<Solver::Watcher> &watchlist = solver.watches[lit];
      watches.push_back(VariableSizedVector<CRef>(watchlist.size()));
      auto &wl = watches[watch_index(lit)];
      for (int i = 0; i < watchlist.size(); i++) {
        wl.push_back(watchlist[i].cref);
      }
    }
    {
      Lit lit = mkLit(v, true);
      vec<Solver::Watcher> &watchlist = solver.watches[lit];
      watches.push_back(VariableSizedVector<CRef>(watchlist.size()));
      auto &wl = watches[watch_index(lit)];
      for (int i = 0; i < watchlist.size(); i++) {
        wl.push_back(watchlist[i].cref);
      }
    }
  }
}

lbool value(Lit p, const FixedSizeVector<MyPropagator::AssignVardata> &assigns) { return assigns[var(p)].assign ^ sign(p); }

void valid_propagation(int trail_min, int trail_max, FixedSizeVector<Lit> &new_trail, FixedSizeVector<MyPropagator::AssignVardata> &assigns_vardata,
                       FixedSizeVector<VariableSizedVector<Solver::Watcher>> &watchesBin, const int decision_level, CRef &confl) {
  int trail_p = trail_min;
  while (trail_p < trail_max) {
    Lit p = new_trail[trail_p++];
    if (value(p, assigns_vardata) == l_False) {
      confl = assigns_vardata[var(p)].vardata.reason;
      return;
    }
  }
}

void binary_propagation(int trail_min, int trail_max, FixedSizeVector<Lit> &new_trail, FixedSizeVector<MyPropagator::AssignVardata> &assigns_vardata,
                        FixedSizeVector<VariableSizedVector<Solver::Watcher>> &watchesBin, const int decision_level, CRef &confl) {
  int trail_p = trail_min;
  while (trail_p < trail_max) {
    Lit p = new_trail[trail_p++];
    VariableSizedVector<Solver::Watcher> &wbin = watchesBin[MyPropagator::watch_index(p)];
    for (int k = 0; k < wbin.size(); k++) {
      Lit imp = wbin[k].blocker;
      if (value(imp, assigns_vardata) == l_False) {
        confl = wbin[k].cref;
        return;
      }
      if (value(imp, assigns_vardata) == l_Undef) {
        new_trail.push_back(imp);
        assigns_vardata[var(imp)] = MyPropagator::AssignVardata(lbool(!sign(imp)), Solver::mkVarData(wbin[k].cref,
                                                                                                     decision_level)); // ensure that these are written
                                                                                                                       // atomically relaxed
      }
    }
  }
}

/// @brief add literal to new trail and assign/vardata
void uncheckedEnqueue(Lit p, CRef cref, FixedSizeVector<MyPropagator::AssignVardata> &assigns_vardata, FixedSizeVector<Lit> &new_trail) {
  new_trail.push_back(p);
  assigns_vardata[var(p)] = MyPropagator::AssignVardata(lbool(!sign(p)), Solver::mkVarData(cref, 0));
}

// add nary watch
void add_watch(Lit p, CRef cref, FixedSizeVector<VariableSizedVector<CRef>> &watches) { watches[MyPropagator::watch_index(p)].push_back(cref); }

void nary_propagation(int trail_min, int trail_max, FixedSizeVector<Lit> &new_trail, FixedSizeVector<MyPropagator::AssignVardata> &assigns_vardata, FixedSizeVector<VariableSizedVector<CRef>> &watches,
                      FixedSizeVector<uint32_t> &ca, const int decision_level, CRef &confl) {
  int trail_p = trail_min;
  while (trail_p < trail_max) {
    Lit p = new_trail[trail_p++];
    VariableSizedVector<CRef> &wnary = watches[MyPropagator::watch_index(p)];
    for (int k = 0; k < wnary.size(); k++) {
      std::cout << "Literal " << MyPropagator::watch_index(p) << " and wnary " << k << std::endl;
      CRef cref = wnary[k];
      Clause &clause = *reinterpret_cast<Clause *>(&ca[cref]);

      int first = -1;
      // std::cout << "first " << first << std::endl;
      while (++first < clause.size()) {
        // std::cout << "first in while " << first << std::endl;
        if (value(clause[first], assigns_vardata) == l_True) {
          return;
        }
        if (value(clause[first], assigns_vardata) == l_Undef) {
          break;
        }
      }
      int second = first;
      while (++second < clause.size()) {
        if (value(clause[second], assigns_vardata) == l_True) {
          return;
        }
        if (value(clause[second], assigns_vardata) == l_Undef) {
          break;
        }
      }
      if (second == clause.size()) {
        /// only first literal found something (or nothing)
        if (first == -1) {
          confl = cref;
          return;
        }
        uncheckedEnqueue(clause[first], cref, assigns_vardata, new_trail);
        return;
      }
      // we have first and second unassigned and need to reassign watches
      add_watch(clause[first], cref, watches); // append to be done synced and in ary order
      wnary[k] = CRef_Undef;
    }
    // reduce wnary to remove CRef_Undef parts

    auto end = std::remove_if(wnary.array, wnary.array + wnary.current_size, [](CRef cref) { return cref == CRef_Undef; });
    wnary.current_size = end - wnary.array;
  }
}

CRef MyPropagator::propagate() {
  int num_props = 0;
  int trail_min = 0;
  while (trail_min < new_trail.size()) {
    int trail_max = new_trail.size();

    binary_propagation(trail_min, trail_max, new_trail, assigns_vardata, watchesBin, decision_level, confl);
    if (confl != CRef_Undef) {
      return confl;
    }

    nary_propagation(trail_min, trail_max, new_trail, assigns_vardata, watches, ca, decision_level, confl);
    if (confl != CRef_Undef) {
      return confl;
    }

    // sync

    valid_propagation(trail_min, trail_max, new_trail, assigns_vardata, watchesBin, decision_level, confl);
    if (confl != CRef_Undef) {
      return confl;
    }

    trail_min = trail_max;
  }

  return confl;
}

//! Returns an abstraction of p's decision level that can be used to order
//! literals.
/*!
 * The function returns a value, s.th
 * order(any true literal) > order(any free literal) > order(any false literal).
 * Furthermore, for equally assigned literals p and q, order(p) > order(q), iff
 * level(p) > level(q).
 * copied from clasp
 */
static uint32_t watchOrder(const Solver &s, Lit p) {
  lbool value_p = s.value(var(p));
  // DL+1,  if isFree(p)
  // DL(p), if isFalse(p)
  // ~DL(p),if isTrue(p)
  uint32_t abstr_p = value_p == l_Undef ? s.decisionLevel() + 1 : s.level(var(p)) ^ -(value_p == (sign(p) ? l_True : l_False));
  assert(abstr_p > 0 || (s.value(p) == l_False && s.level(var(p)) == 0));
  return abstr_p;
}

// order clause using watchOrder
void reorder_clause(Solver &solver, CRef cref) {
  Clause &clause = *dynamic_cast<Clause *>(&solver.ca[cref]);
  if (clause.size() > 2 && !(clause.mark() & 1)) {
    Lit *it = const_cast<Lit *>(static_cast<const Lit *>(clause));
    std::nth_element(it, it + 2, it + clause.size(), [&](Lit a, Lit b) { return watchOrder(solver, a) > watchOrder(solver, b); });
    solver.attachClause(cref);
  }
}

/// @brief write back all temporary datastructures to the original solver
/// @param solver
void MyPropagator::write_back(Solver &solver) {
  // copy assignment
  for (int i = old_trail_size; i < new_trail.size(); i++) {
    solver.uncheckedEnqueue(new_trail[i], assigns_vardata[var(new_trail[i])].vardata.reason);
  }
  solver.qhead = solver.trail.size();

  // clear old solver watches
  for (Var v = 0; v < num_vars; ++v) {
    {
      Lit lit = mkLit(v, false);
      solver.watches[lit].clear();
    }
    {
      Lit lit = mkLit(v, true);
      solver.watches[lit].clear();
    }
  }

  // reorder clauses in solver s.t. the watch order is correct
  for (int i = 0; i < solver.clauses.size(); ++i) {
    reorder_clause(solver, solver.clauses[i]);
  }
  for (int i = 0; i < solver.learnts.size(); ++i) {
    reorder_clause(solver, solver.learnts[i]);
  }
  for (int i = 0; i < solver.permanentLearnts.size(); ++i) {
    reorder_clause(solver, solver.permanentLearnts[i]);
  }
}
