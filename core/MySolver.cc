#include "core/MySolver.h"
#include "core/MyUtils.h"
#include "core/Solver.h"
#include "core/SolverTypes.h"
#include <algorithm>
#include <iostream>
#include <set>

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


  /// create complete occuruence lists in watches
  for (int i = 0; i < solver.clauses.size(); i++) {
    Clause &clause = *reinterpret_cast<Clause *>(&solver.ca[solver.clauses[i]]);
    if (clause.size() > 2) {
      for (int j = 0; j < clause.size(); j++) {
        watches[watch_index(~clause[j])].push_back(solver.clauses[i]);
      }
    }
  }
  for (int i = 0; i < solver.learnts.size(); i++) {
    Clause &clause = *reinterpret_cast<Clause *>(&solver.ca[solver.learnts[i]]);
    if (clause.size() > 2) {
      for (int j = 0; j < clause.size(); j++) {
        watches[watch_index(~clause[j])].push_back(solver.learnts[i]);
      }
    }
  }
  for (int i = 0; i < solver.permanentLearnts.size(); i++) {
    Clause &clause = *reinterpret_cast<Clause *>(&solver.ca[solver.permanentLearnts[i]]);
    if (clause.size() > 2) {
      for (int j = 0; j < clause.size(); j++) {
        watches[watch_index(clause[j])].push_back(solver.permanentLearnts[i]);
      }
    }
  }

}

lbool value(Lit p, const FixedSizeVector<MyPropagator::AssignVardata> &assigns) { return assigns[var(p)].assign ^ sign(p); }

void valid_propagation(int trail_min, int trail_max, FixedSizeVector<Lit> &new_trail, FixedSizeVector<MyPropagator::AssignVardata> &assigns_vardata, CRef &confl) {
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
void uncheckedEnqueue(Lit p, CRef cref, FixedSizeVector<MyPropagator::AssignVardata> &assigns_vardata, FixedSizeVector<Lit> &new_trail, int decision_level) {
  //std::cout << " propagate " << var(p) << " " << sign(p) << " with reason " << cref << std::endl;
  new_trail.push_back(p);
  assigns_vardata[var(p)] = MyPropagator::AssignVardata(lbool(!sign(p)), Solver::mkVarData(cref, decision_level));
}

// add nary watch
void add_watch(Lit p, Lit blocker, CRef cref, FixedSizeVector<VariableSizedVector<Solver::Watcher>> &watches) { watches[MyPropagator::watch_index(p)].push_back(Solver::Watcher(cref, blocker)); }

void nary_propagation(int trail_min, int trail_max, FixedSizeVector<Lit> &new_trail, FixedSizeVector<MyPropagator::AssignVardata> &assigns_vardata, FixedSizeVector<VariableSizedVector<CRef>> &watches,
                      FixedSizeVector<uint32_t> &ca, const int decision_level, CRef &confl) {
  int trail_p = trail_min;
  while (trail_p < trail_max) {
    Lit p = new_trail[trail_p++];
    VariableSizedVector<CRef> &wnary = watches[MyPropagator::watch_index(p)];
    for (int k = 0; k < wnary.size(); k++) {
      CRef cref = wnary[k];
      const Clause& clause = *reinterpret_cast<Clause*>(&ca[reinterpret_cast<uint32_t>(cref)]);
      Lit l = lit_Undef;

      for (int i = 0; i < clause.size(); i++) {
        if (value(clause[i], assigns_vardata) == l_True) {
          goto Continue;  // at least 1 true literal
        }
        if (value(clause[i], assigns_vardata) == l_Undef) {
          if (l != lit_Undef) {
            goto Continue; // 2 undefined literals
          }
          l = clause[i];
        }
      }
      /// all literals are false
      if (l == lit_Undef) {
        confl = cref;
        return;
      }

      uncheckedEnqueue(l, cref, assigns_vardata, new_trail, decision_level);

      Continue:
      ;
    }
  }
}


CRef MyPropagator::propagate() {
  int trail_min = 0;
  while (trail_min < new_trail.size()) {
    int trail_max = new_trail.size();

    binary_propagation(trail_min, trail_max, new_trail, assigns_vardata, watchesBin, decision_level, confl);
    if (confl != CRef_Undef) {
      //std::cout << "conflict: " << confl << std::endl;
      return confl;
    }

    nary_propagation(trail_min, trail_max, new_trail, assigns_vardata, watches, ca, decision_level, confl);
    if (confl != CRef_Undef) {
      //std::cout << "conflict: " << confl << std::endl;
      return confl;
    }

    // sync

    valid_propagation(trail_min, trail_max, new_trail, assigns_vardata, confl);
    if (confl != CRef_Undef) {
      //std::cout << "conflict: " << confl << std::endl;
      return confl;
    }

    trail_min = trail_max;
  }
  //std::cout << "no conflict: " << confl << std::endl;
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
  uint32_t abstr_p ;
  
  if (value_p == l_Undef)
    abstr_p = s.decisionLevel() + 1;
  else {
    abstr_p = s.level(var(p));
    if (value_p == (sign(p) ? l_False : l_True))
      abstr_p = ~abstr_p;
  }
  assert(abstr_p > 0 || (s.value(p) == l_False && s.level(var(p)) == 0));
  return abstr_p;
}

// order clause using watchOrder
void reorder_clause(Solver &solver, CRef cref) {
  Clause &clause = *dynamic_cast<Clause *>(&solver.ca[cref]);
  if (clause.size() > 2 && !(clause.mark() & 1)) {
    Lit *it = const_cast<Lit *>(static_cast<const Lit *>(clause));
    //std::nth_element(it, it + 2, it + clause.size(), [&](Lit a, Lit b) { return watchOrder(solver, a) > watchOrder(solver, b); });
    std::sort(it, it + clause.size(), [&](Lit a, Lit b) { return watchOrder(solver, a) > watchOrder(solver, b); });
    solver.attachClause(cref);
  }
}


void MyPropagator::compare(Solver &solver, CRef confl) {
  /// either both are in conflict or both are not in conflict
  if (this->confl == CRef_Undef && confl == CRef_Undef) {

    // both trails are the same (set comparison)
    assert(std::set<Lit>(new_trail.array, new_trail.array + new_trail.size()) == std::set<Lit>(solver.trail.data + solver.trail.size() - new_trail.size(), solver.trail.data + solver.trail.size()));
    return;
  }

  assert (this->confl != CRef_Undef && confl != CRef_Undef);
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
