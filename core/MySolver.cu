#include "core/MySolver.h"
#include "core/MyUtils.cuh"
#include "core/Solver.h"
#include "core/SolverTypes.h"
#include <algorithm>
#include <iostream>
#include <set>
#include <vector>

using namespace Glucose;

__host__ int watch_index(Lit l) { return var(l) * 2 + int(sign(l)); }

MySolver create_solver(Solver &solver)
{
  MySolver mysolver;
  unsigned int num_vars = solver.nVars();
  mysolver.host_num_vars = num_vars;
  mysolver.decision_level = solver.decisionLevel();

  gpuErrchk(cudaMalloc((void **)&mysolver.confl_device, sizeof(CRef)));
  mysolver.confl_host = new CRef(CRef_Undef);
  
  gpuErrchk(cudaMemcpy(mysolver.confl_device, &mysolver.confl_host, sizeof(CRef), cudaMemcpyHostToDevice));

  gpuErrchk(cudaMalloc((void **)&mysolver.new_trail, sizeof(Lit) * num_vars));
  gpuErrchk(cudaMemcpy(mysolver.new_trail, &solver.trail[0], solver.trail.size(), cudaMemcpyHostToDevice));

  gpuErrchk(cudaMalloc((void **)&mysolver.trail_size, sizeof(unsigned int)));
  unsigned int trail_size = solver.trail.size();
  gpuErrchk(cudaMemcpy(mysolver.trail_size, &trail_size, sizeof(unsigned int), cudaMemcpyHostToDevice));
  mysolver.host_trail_size = trail_size;
  mysolver.host_trail = new Lit[num_vars];

  gpuErrchk(cudaMalloc((void **)&mysolver.qhead, sizeof(unsigned int)));
  gpuErrchk(cudaMemcpy(mysolver.qhead, &solver.qhead, sizeof(unsigned int), cudaMemcpyHostToDevice));

  gpuErrchk(cudaMalloc((void **)&mysolver.assigns_vardata, sizeof(AssignVardata) * num_vars));

  AssignVardata *temp = new AssignVardata[num_vars];
  // copy assigns and vardata
  for (int i = 0; i < num_vars; i++)
  {
    temp[i].assign = solver.assigns[i].value;
    temp[i].vardata = solver.vardata[i];
  }
  gpuErrchk(cudaMemcpy(mysolver.assigns_vardata, temp, sizeof(AssignVardata) * num_vars, cudaMemcpyHostToDevice));
  delete[] temp;

  // copy binary watch lists
  mysolver.hostBinWatch = new binWatchVector[num_vars * 2];

  
  for (unsigned int i = 0; i < num_vars; ++i)
  {
    {
      Lit lit = mkLit(i, false);
      unsigned int size = solver.watchesBin[lit].size();
      mysolver.hostBinWatch[watch_index(lit)].size = size;
      mysolver.hostBinWatch[watch_index(lit)].watches = nullptr;
      if (size > 0) {
        gpuErrchk(cudaMalloc((void **)&mysolver.hostBinWatch[watch_index(lit)].watches, size * sizeof(Solver::Watcher)));
        gpuErrchk(cudaMemcpy(mysolver.hostBinWatch[watch_index(lit)].watches, solver.watchesBin[lit].data, sizeof(Solver::Watcher) * size, cudaMemcpyHostToDevice));
      }
    }
    {
      Lit lit = mkLit(i, true);
      unsigned int size = solver.watchesBin[lit].size();
      mysolver.hostBinWatch[watch_index(lit)].size = size;
      mysolver.hostBinWatch[watch_index(lit)].watches = nullptr;
      if (size > 0) {
        gpuErrchk(cudaMalloc((void **)&mysolver.hostBinWatch[watch_index(lit)].watches, size * sizeof(Solver::Watcher)));
        gpuErrchk(cudaMemcpy(mysolver.hostBinWatch[watch_index(lit)].watches, solver.watchesBin[lit].data, sizeof(Solver::Watcher) * size, cudaMemcpyHostToDevice));
      }
    }
  }

  gpuErrchk(cudaMalloc((void **)&mysolver.watchesBin, sizeof(binWatchVector) * num_vars * 2));
  gpuErrchk(cudaMemcpy(mysolver.watchesBin, mysolver.hostBinWatch, sizeof(binWatchVector) * num_vars * 2, cudaMemcpyHostToDevice));

  // create complete occuruence lists in watches
  std::vector<std::vector<CRef>> clause_refs(num_vars * 2, std::vector<CRef>());
  for (int i = 0; i < solver.clauses.size(); i++)
  {
    Clause &clause = *reinterpret_cast<Clause *>(&solver.ca[solver.clauses[i]]);
    if (clause.size() > 2)
    {
      for (int j = 0; j < clause.size(); j++)
      {
        clause_refs[watch_index(~clause[j])].push_back(solver.ca.ael(&clause));
      }
    }
  }
  for (int i = 0; i < solver.learnts.size(); i++)
  {
    Clause &clause = *reinterpret_cast<Clause *>(&solver.ca[solver.learnts[i]]);
    if (clause.size() > 2)
    {
      for (int j = 0; j < clause.size(); j++)
      {
        clause_refs[watch_index(~clause[j])].push_back(solver.ca.ael(&clause));
      }
    }
  }
  for (int i = 0; i < solver.permanentLearnts.size(); i++)
  {
    Clause &clause = *reinterpret_cast<Clause *>(&solver.ca[solver.permanentLearnts[i]]);
    if (clause.size() > 2)
    {
      for (int j = 0; j < clause.size(); j++)
      {
        clause_refs[watch_index(clause[j])].push_back(solver.ca.ael(&clause));
      }
    }
  }

  mysolver.hostWatches = new watchVector[num_vars * 2];

  for (unsigned int i = 0; i < num_vars; ++i)
  {
    {
      Lit lit = mkLit(i, false);
      unsigned int size = clause_refs[watch_index(lit)].size();
      mysolver.hostWatches[watch_index(lit)].size = size;
      mysolver.hostWatches[watch_index(lit)].crefs = nullptr;
      if (size > 0) {
        gpuErrchk(cudaMalloc((void **)&mysolver.hostWatches[watch_index(lit)].crefs, size * sizeof(CRef)));
        
        gpuErrchk(cudaMemcpy(mysolver.hostWatches[watch_index(lit)].crefs, &clause_refs[watch_index(lit)], sizeof(CRef) * size, cudaMemcpyHostToDevice));
      }
    }
    {
      Lit lit = mkLit(i, true);
      unsigned int size = clause_refs[watch_index(lit)].size();
      mysolver.hostWatches[watch_index(lit)].size = size;
      mysolver.hostWatches[watch_index(lit)].crefs = nullptr;
      if (size > 0) {
        gpuErrchk(cudaMalloc((void **)&mysolver.hostWatches[watch_index(lit)].crefs, size * sizeof(CRef)));
        
        gpuErrchk(cudaMemcpy(mysolver.hostWatches[watch_index(lit)].crefs, &clause_refs[watch_index(lit)], sizeof(CRef) * size, cudaMemcpyHostToDevice));
      }
    }
  }
  gpuErrchk(cudaMalloc((void **)&mysolver.watches, sizeof(watchVector) * num_vars * 2));
  gpuErrchk(cudaMemcpy(mysolver.watches, mysolver.hostWatches, sizeof(watchVector) * num_vars * 2, cudaMemcpyHostToDevice));


  // copy clause database
  gpuErrchk(cudaMalloc((void **)&mysolver.ca, sizeof(uint32_t) * solver.ca.size()));
  gpuErrchk(cudaMemcpy(mysolver.ca, solver.ca.lea(0), sizeof(uint32_t) * solver.ca.size(), cudaMemcpyHostToDevice));

  return mysolver;
}


__device__ inline lbool_device create_bool_device_from_uc(lbool_device x) { return (lbool_device)(x); }
__device__ inline lbool_device create_bool_device_from_bool(bool x) { return (lbool_device)(!x); }
__device__ inline bool sign_device(Lit p) { return p.x & 1; }
__device__ inline int var_device(Lit p) { return p.x >> 1; }
__device__ Lit  mkLit_device(Var var, bool sign = false) { Lit p; p.x = var + var + (int)sign; return p; }
#define l_True_device (lbool_device((uint8_t)0)) // gcc does not do constant propagation if these are real constants.
#define l_False_device (lbool_device((uint8_t)1))
#define l_Undef_device (lbool_device((uint8_t)2))




__device__ Solver::VarData mkVarData_device(CRef cr, int l)
{
  Solver::VarData d = {cr, l};
  return d;
}
__device__ int watch_index_device(Lit l) { return var_device(l) * 2 + int(sign_device(l)); }

/// @brief add literal to new trail and assign/vardata
__device__ void uncheckedEnqueue(Lit p, CRef cref, AssignVardata *assigns_vardata, Lit *new_trail, unsigned int *trail_size, int decision_level)
{
  // std::cout << " propagate " << var(p) << " " << sign(p) << " with reason "
  // << cref << std::endl;
  /// atomic increase trailsize
  int trail_p = atomicAdd(trail_size, 1);
  new_trail[trail_p] = p;
  AssignVardata temp;
  temp.assign = create_bool_device_from_bool(!sign_device(p));
  temp.vardata = mkVarData_device(cref, decision_level);
  assigns_vardata[var_device(p)] = temp; // ensure that these are written atomically relaxed
}

__device__ lbool_device value(Lit p, AssignVardata *assigns)
{
  return create_bool_device_from_uc((lbool_device)(assigns[var_device(p)].assign ^ (lbool_device)(sign_device(p))));
}

void destroy_solver(MySolver &solver)
{
    gpuErrchk(cudaFree(solver.confl_device));
    gpuErrchk(cudaFree(solver.new_trail));
    gpuErrchk(cudaFree(solver.trail_size));
    gpuErrchk(cudaFree(solver.assigns_vardata));
    for (unsigned int i = 0; i < solver.host_num_vars; ++i)
    {
      gpuErrchk(cudaFree(solver.hostBinWatch[watch_index(mkLit(i, false))].watches));
      gpuErrchk(cudaFree(solver.hostBinWatch[watch_index(mkLit(i, true))].watches));
      gpuErrchk(cudaFree(solver.hostWatches[watch_index(mkLit(i, false))].crefs));
      gpuErrchk(cudaFree(solver.hostWatches[watch_index(mkLit(i, true))].crefs));
    }
    gpuErrchk(cudaFree(solver.watchesBin));
    gpuErrchk(cudaFree(solver.watches));
    delete[] solver.hostBinWatch;
    delete[] solver.hostWatches;
    gpuErrchk(cudaFree(solver.ca));
}

__global__ void binary_propagation(
    unsigned int* qhead, int trail_max, Lit *new_trail, unsigned int *trail_size, AssignVardata *assigns_vardata, binWatchVector *watchesBin, const int decision_level, CRef *confl)
{
  unsigned int trail_p = *qhead;
  while (trail_p < trail_max)
  {
    Lit p = new_trail[trail_p++];
    auto &wbin = watchesBin[watch_index_device(p)];
    for (int k = 0; k < wbin.size; k++)
    {
      Lit imp = wbin.watches[k].blocker;
      if (value(imp, assigns_vardata) == l_False_device)
      {
        *confl = wbin.watches[k].cref;
        return;
      }
      if (value(imp, assigns_vardata) == l_Undef_device)
      {
        uncheckedEnqueue(imp, wbin.watches[k].cref, assigns_vardata, new_trail, trail_size, decision_level);
      }
    }
  }
  *qhead = trail_max;
  if (*trail_size > trail_max) {
    binary_propagation<<<1, 1>>>(qhead, *trail_size, new_trail, trail_size, assigns_vardata, watchesBin, decision_level, confl);
  }
}

void copyConflictToHost(MySolver &solver)
{
  gpuErrchk(cudaMemcpy(&solver.confl_host, solver.confl_device, sizeof(CRef), cudaMemcpyDeviceToHost));
}

void copyTrailToHost(MySolver &solver)
{
  gpuErrchk(cudaMemcpy(solver.host_trail, solver.new_trail, sizeof(Lit)*solver.host_num_vars, cudaMemcpyDeviceToHost));
  gpuErrchk(cudaMemcpy(&solver.host_trail_size, solver.trail_size, sizeof(unsigned int), cudaMemcpyDeviceToHost));
}

void compare(MySolver &solver, Solver& s, CRef confl)
{
  copyConflictToHost(solver);
  copyTrailToHost(solver);
  /// either both are in conflict or both are not in conflict
  if (*solver.confl_host == CRef_Undef && confl == CRef_Undef)
  {
    // both trails are the same (set comparison)
    std::set<Lit> myset(solver.host_trail, solver.host_trail + solver.host_trail_size);
    std::set<Lit> theirset(s.trail.data, s.trail.data + s.trail.size());
    // write relation between the two sets
    // if myset is a subset of theirset
    if (std::includes(theirset.begin(), theirset.end(), myset.begin(), myset.end()))
    {
      //std::cout << "fine" << std::endl;
      return;
    }
    // if theirset is a subset of myset
    if (std::includes(myset.begin(), myset.end(), theirset.begin(), theirset.end()))
    {
      std::cout << "theirset is a subset of myset" << std::endl;
    }
    return;
  }

  if(confl != CRef_Undef) { // they have a conflict
    //std::cout << "fine" << std::endl;
    return;
  }
  assert (*solver.confl_host != CRef_Undef && confl == CRef_Undef);
  std::cout << "PROBLEM: I have a conflict, they not" << std::endl;
}

void propagate(MySolver &solver)
{

  // binary_propagation<<<trail_max-trail_min, 32>>>
  binary_propagation<<<1, 1>>>(solver.qhead, solver.host_trail_size, solver.new_trail, solver.trail_size, solver.assigns_vardata, solver.watchesBin, solver.decision_level, solver.confl_device);

  gpuErrchk(cudaDeviceSynchronize());



  //   nary_propagation(trail_min, trail_max, new_trail, assigns_vardata, watches,
  //                    ca, decision_level, confl);
  //   if (confl != CRef_Undef) {
  //     // std::cout << "conflict: " << confl << std::endl;
  //     return confl;
  //   }

  //   // sync

  //   valid_propagation(trail_min, trail_max, new_trail, assigns_vardata, confl);
  //   if (confl != CRef_Undef) {
  //     // std::cout << "conflict: " << confl << std::endl;
  //     return confl;
  //   }

  //   trail_min = trail_max;
  // }
  // std::cout << "no conflict: " << confl << std::endl;
}

// /// @brief This propagation is meant to do everything in parallel
// /// also it does not change the clause database, it uses 1 Literal watches
// /// Afterwards, the watches and the clauses need to be restored to old style
// /// @param solver
// MyPropagator::MyPropagator(Solver &solver)
//     : num_vars(solver.nVars()), decision_level(solver.decisionLevel()),
//       new_trail(FixedSizeVector<Lit>(num_vars, &solver.trail[solver.qhead],
//                                      solver.trail.size() - solver.qhead)),
//       old_trail_size(solver.trail.size() - solver.qhead), confl(CRef_Undef),
//       assigns_vardata(FixedSizeVector<AssignVardata>(num_vars)),
//       watchesBin(FixedSizeVector<VariableSizedVector<Solver::Watcher>>(
//           num_vars * 2 + 1)),
//       watches(FixedSizeVector<VariableSizedVector<CRef>>(num_vars * 2 + 1)),
//       ca(FixedSizeVector<uint32_t>(
//           solver.ca.size() * 2, reinterpret_cast<uint32_t *>(solver.ca.lea(0)),
//           solver.ca.size())) {

//   // copy assigns and vardata
//   for (int i = 0; i < num_vars; i++) {
//     assigns_vardata.push_back(
//         MyPropagator::AssignVardata(solver.assigns[i], solver.vardata[i]));
//   }

//   for (Var v = 0; v < num_vars; ++v) {
//     {
//       Lit lit = mkLit(v, false);
//       auto dummy = watch_index(lit);
//       vec<Solver::Watcher> &watchlist = solver.watchesBin[lit];
//       watchesBin[watch_index(lit)].append(&watchlist[0], watchlist.size());
//     }

//     {
//       Lit lit = mkLit(v, true);
//       auto dummy = watch_index(lit);
//       vec<Solver::Watcher> &watchlist = solver.watchesBin[lit];
//       watchesBin[watch_index(lit)].append(&watchlist[0], watchlist.size());
//     }
//   }

//   /// create complete occuruence lists in watches
//   for (int i = 0; i < solver.clauses.size(); i++) {
//     Clause &clause = *reinterpret_cast<Clause *>(&solver.ca[solver.clauses[i]]);
//     if (clause.size() > 2) {
//       for (int j = 0; j < clause.size(); j++) {
//         watches[watch_index(~clause[j])].push_back(solver.clauses[i]);
//       }
//     }
//   }
//   for (int i = 0; i < solver.learnts.size(); i++) {
//     Clause &clause = *reinterpret_cast<Clause *>(&solver.ca[solver.learnts[i]]);
//     if (clause.size() > 2) {
//       for (int j = 0; j < clause.size(); j++) {
//         watches[watch_index(~clause[j])].push_back(solver.learnts[i]);
//       }
//     }
//   }
//   for (int i = 0; i < solver.permanentLearnts.size(); i++) {
//     Clause &clause =
//         *reinterpret_cast<Clause *>(&solver.ca[solver.permanentLearnts[i]]);
//     if (clause.size() > 2) {
//       for (int j = 0; j < clause.size(); j++) {
//         watches[watch_index(clause[j])].push_back(solver.permanentLearnts[i]);
//       }
//     }
//   }
// }

// MyPropagator::~MyPropagator() {
//   // delete vectors
//   new_trail.free();
//   assigns_vardata.free();
//   for (int i = 0; i < watchesBin.size(); i++) {
//     watchesBin[i].free();
//   }
//   for (int i = 0; i < watches.size(); i++) {
//     watches[i].free();
//   }
//   watchesBin.free();
//   watches.free();
//   ca.free();
// }

// /// @brief add literal to new trail and assign/vardata
// void uncheckedEnqueue(
//     Lit p, CRef cref,
//     FixedSizeVector<MyPropagator::AssignVardata> &assigns_vardata,
//     FixedSizeVector<Lit> &new_trail, int decision_level) {
//   // std::cout << " propagate " << var(p) << " " << sign(p) << " with reason "
//   // << cref << std::endl;
//   new_trail.push_back(p);
//   assigns_vardata[var(p)] = MyPropagator::AssignVardata( // ensure that these are written
//       lbool(!sign(p)), Solver::mkVarData(cref, decision_level)); // atomically relaxed
// }

// lbool value(Lit p,
//             const FixedSizeVector<MyPropagator::AssignVardata> &assigns) {
//   return assigns[var(p)].assign ^ sign(p);
// }

// void valid_propagation(
//     int trail_min, int trail_max, FixedSizeVector<Lit> &new_trail,
//     FixedSizeVector<MyPropagator::AssignVardata> &assigns_vardata,
//     CRef &confl) {
//   int trail_p = trail_min;
//   while (trail_p < trail_max) {
//     Lit p = new_trail[trail_p++];
//     if (value(p, assigns_vardata) == l_False) {
//       confl = assigns_vardata[var(p)].vardata.reason;
//       return;
//     }
//   }
// }

// void binary_propagation(
//     int trail_min, int trail_max, FixedSizeVector<Lit> &new_trail,
//     FixedSizeVector<MyPropagator::AssignVardata> &assigns_vardata,
//     FixedSizeVector<VariableSizedVector<Solver::Watcher>> &watchesBin,
//     const int decision_level, CRef &confl) {
//   int trail_p = trail_min;
//   while (trail_p < trail_max) {
//     Lit p = new_trail[trail_p++];
//     VariableSizedVector<Solver::Watcher> &wbin =
//         watchesBin[MyPropagator::watch_index(p)];
//     for (int k = 0; k < wbin.size(); k++) {
//       Lit imp = wbin[k].blocker;
//       if (value(imp, assigns_vardata) == l_False) {
//         confl = wbin[k].cref;
//         return;
//       }
//       if (value(imp, assigns_vardata) == l_Undef) {
//         uncheckedEnqueue(imp, wbin[k].cref, assigns_vardata, new_trail,
//                          decision_level);
//       }
//     }
//   }
// }

// // // add nary watch
// // void add_watch(Lit p, Lit blocker, CRef cref,
// //                FixedSizeVector<VariableSizedVector<Solver::Watcher>> &watches) {
// //   watches[MyPropagator::watch_index(p)].push_back(
// //       Solver::Watcher(cref, blocker));
// // }

// void nary_propagation(
//     int trail_min, int trail_max, FixedSizeVector<Lit> &new_trail,
//     FixedSizeVector<MyPropagator::AssignVardata> &assigns_vardata,
//     FixedSizeVector<VariableSizedVector<CRef>> &watches,
//     FixedSizeVector<uint32_t> &ca, const int decision_level, CRef &confl) {
//   int trail_p = trail_min;
//   while (trail_p < trail_max) {
//     Lit p = new_trail[trail_p++];
//     VariableSizedVector<CRef> &wnary = watches[MyPropagator::watch_index(p)];
//     for (int k = 0; k < wnary.size(); k++) {
//       CRef cref = wnary[k];
//       const Clause &clause =
//           *reinterpret_cast<Clause *>(&ca[reinterpret_cast<uint32_t>(cref)]);
//       Lit l = lit_Undef;

//       for (int i = 0; i < clause.size(); i++) {
//         if (value(clause[i], assigns_vardata) == l_True) {
//           goto Continue; // at least 1 true literal
//         }
//         if (value(clause[i], assigns_vardata) == l_Undef) {
//           if (l != lit_Undef) {
//             goto Continue; // 2 undefined literals
//           }
//           l = clause[i];
//         }
//       }
//       /// all literals are false
//       if (l == lit_Undef) {
//         confl = cref;
//         return;
//       }

//       uncheckedEnqueue(l, cref, assigns_vardata, new_trail, decision_level);

//     Continue:;
//     }
//   }
// }

// //! Returns an abstraction of p's decision level that can be used to order
// //! literals.
// /*!
//  * The function returns a value, s.th
//  * order(any true literal) > order(any free literal) > order(any false literal).
//  * Furthermore, for equally assigned literals p and q, order(p) > order(q), iff
//  * level(p) > level(q).
//  * copied from clasp
//  */
// static uint32_t watchOrder(const Solver &s, Lit p) {
//   lbool value_p = s.value(var(p));
//   // DL+1,  if isFree(p)
//   // DL(p), if isFalse(p)
//   // ~DL(p),if isTrue(p)
//   uint32_t abstr_p;

//   if (value_p == l_Undef)
//     abstr_p = s.decisionLevel() + 1;
//   else {
//     abstr_p = s.level(var(p));
//     if (value_p == (sign(p) ? l_False : l_True))
//       abstr_p = ~abstr_p;
//   }
//   assert(abstr_p > 0 || (s.value(p) == l_False && s.level(var(p)) == 0));
//   return abstr_p;
// }

// // order clause using watchOrder
// void reorder_clause(Solver &solver, CRef cref) {
//   Clause &clause = *dynamic_cast<Clause *>(&solver.ca[cref]);
//   if (clause.size() > 2 && !(clause.mark() & 1)) {
//     Lit *it = const_cast<Lit *>(static_cast<const Lit *>(clause));
//     // std::nth_element(it, it + 2, it + clause.size(), [&](Lit a, Lit b) {
//     // return watchOrder(solver, a) > watchOrder(solver, b); });
//     std::sort(it, it + clause.size(), [&](Lit a, Lit b) {
//       return watchOrder(solver, a) > watchOrder(solver, b);
//     });
//     solver.attachClause(cref);
//   }
// }

// void MyPropagator::compare(Solver &solver, CRef confl) {
//   /// either both are in conflict or both are not in conflict
//   if (this->confl == CRef_Undef && confl == CRef_Undef) {

//     // both trails are the same (set comparison)
//     assert(std::set<Lit>(new_trail.array, new_trail.array + new_trail.size()) ==
//            std::set<Lit>(solver.trail.data + solver.trail.size() -
//                              new_trail.size(),
//                          solver.trail.data + solver.trail.size()));
//     return;
//   }

//   assert(this->confl != CRef_Undef && confl != CRef_Undef);
// }

// /// @brief write back all temporary datastructures to the original solver
// /// @param solver
// void MyPropagator::write_back(Solver &solver) {
//   // copy assignment
//   for (int i = old_trail_size; i < new_trail.size(); i++) {
//     solver.uncheckedEnqueue(new_trail[i],
//                             assigns_vardata[var(new_trail[i])].vardata.reason);
//   }
//   solver.qhead = solver.trail.size();

//   // clear old solver watches
//   for (Var v = 0; v < num_vars; ++v) {
//     {
//       Lit lit = mkLit(v, false);
//       solver.watches[lit].clear();
//     }
//     {
//       Lit lit = mkLit(v, true);
//       solver.watches[lit].clear();
//     }
//   }

//   // reorder clauses in solver s.t. the watch order is correct
//   for (int i = 0; i < solver.clauses.size(); ++i) {
//     reorder_clause(solver, solver.clauses[i]);
//   }
//   for (int i = 0; i < solver.learnts.size(); ++i) {
//     reorder_clause(solver, solver.learnts[i]);
//   }
//   for (int i = 0; i < solver.permanentLearnts.size(); ++i) {
//     reorder_clause(solver, solver.permanentLearnts[i]);
//   }
// }
