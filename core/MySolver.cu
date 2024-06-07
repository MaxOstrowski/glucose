#include "core/MySolver.h"
#include "core/MyUtils.cuh"
#include "core/Solver.h"
#include "core/SolverTypes.h"
#include <algorithm>
#include <iostream>
#include <set>
#include <vector>
#include <cooperative_groups.h>

using namespace Glucose;

__host__ int watch_index(Lit l) { return var(l) * 2 + int(sign(l)); }


void copyConflictToHost(MySolver &solver);

MySolver create_solver(Solver &solver)
{
  MySolver mysolver;
  unsigned int num_vars = solver.nVars();
  mysolver.host_num_vars = num_vars;
  mysolver.decision_level = solver.decisionLevel();

  // create storage for conflict clause
  gpuErrchk(cudaMalloc((void **)&mysolver.confl_device, sizeof(CRef)));
  gpuErrchk(cudaMalloc((void **)&mysolver.device_conflict, sizeof(Lit) * num_vars));
  gpuErrchk(cudaMalloc((void **)&mysolver.device_conflict_size, sizeof(unsigned int)));
  gpuErrchk(cudaMalloc((void **)&mysolver.device_backtrack_level, sizeof(unsigned int)));
  mysolver.host_conflict = new Lit[num_vars];
  mysolver.host_conflict_size = 0;
  mysolver.host_backtrack_level = 0;
  gpuErrchk(cudaMemcpy(mysolver.device_conflict_size, &mysolver.host_conflict_size, sizeof(unsigned int), cudaMemcpyHostToDevice));
  gpuErrchk(cudaMemcpy(mysolver.device_backtrack_level, &mysolver.host_backtrack_level, sizeof(unsigned int), cudaMemcpyHostToDevice));
  mysolver.confl_host = new CRef(CRef_Undef);
  gpuErrchk(cudaMemcpy(mysolver.confl_device, mysolver.confl_host, sizeof(CRef), cudaMemcpyHostToDevice));

  copyConflictToHost(mysolver);

  gpuErrchk(cudaMalloc((void **)&mysolver.device_trail, sizeof(Lit) * num_vars));
  gpuErrchk(cudaMemcpy(mysolver.device_trail, &solver.trail[0], solver.trail.size()*sizeof(Lit), cudaMemcpyHostToDevice));

  gpuErrchk(cudaMalloc((void **)&mysolver.device_trail_size, sizeof(unsigned int)));
  unsigned int trail_size = solver.trail.size();
  gpuErrchk(cudaMemcpy(mysolver.device_trail_size, &trail_size, sizeof(unsigned int), cudaMemcpyHostToDevice));
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
        
        gpuErrchk(cudaMemcpy(mysolver.hostWatches[watch_index(lit)].crefs, clause_refs[watch_index(lit)].data(), sizeof(CRef) * size, cudaMemcpyHostToHost));
      }
    }
    {
      Lit lit = mkLit(i, true);
      unsigned int size = clause_refs[watch_index(lit)].size();
      mysolver.hostWatches[watch_index(lit)].size = size;
      mysolver.hostWatches[watch_index(lit)].crefs = nullptr;
      if (size > 0) {
        gpuErrchk(cudaMalloc((void **)&mysolver.hostWatches[watch_index(lit)].crefs, size * sizeof(CRef)));
        
        gpuErrchk(cudaMemcpy(mysolver.hostWatches[watch_index(lit)].crefs, clause_refs[watch_index(lit)].data(), sizeof(CRef) * size, cudaMemcpyHostToHost));
      }
    }
  }
  gpuErrchk(cudaMalloc((void **)&mysolver.watches, sizeof(watchVector) * num_vars * 2));
  gpuErrchk(cudaMemcpy(mysolver.watches, mysolver.hostWatches, sizeof(watchVector) * num_vars * 2, cudaMemcpyHostToDevice));


  // copy clause database
  gpuErrchk(cudaMalloc((void **)&mysolver.ca, sizeof(uint32_t) * solver.ca.size()));
  gpuErrchk(cudaMemcpy(mysolver.ca, solver.ca.lea(0), sizeof(uint32_t) * solver.ca.size(), cudaMemcpyHostToDevice));

  gpuErrchk(cudaDeviceSynchronize());

  return mysolver;
}


__device__ inline lbool_device create_bool_device_from_uc(lbool_device x) { return (lbool_device)(x); }
__device__ inline lbool_device create_bool_device_from_bool(bool x) { return (lbool_device)(!x); }
__device__ inline bool compare_lbool_device(lbool_device a, lbool_device b) { return ((b&2) & (a&2)) | (!(b&2)&(a == b)); }
__device__ inline bool sign_device(Lit p) { return p.x & 1; }
__device__ inline int var_device(Lit p) { return p.x >> 1; }
__device__ Lit  mkLit_device(Var var, bool sign = false) { Lit p; p.x = var + var + (int)sign; return p; }
#define l_True_device (lbool_device((uint8_t)0)) // gcc does not do constant propagation if these are real constants.
#define l_False_device (lbool_device((uint8_t)1))
#define l_Undef_device (lbool_device((uint8_t)2))
__device__ int toInt_device(Lit p) { return p.x; }
__device__ Lit toLit_device(int i) { Lit p; p.x = i; return p; }




__device__ Solver::VarData mkVarData_device(CRef cr, int l)
{
  Solver::VarData d = {cr, l};
  return d;
}
__device__ int watch_index_device(Lit l) { return var_device(l) * 2 + int(sign_device(l)); }

/// @brief add literal to new trail and assign/vardata
__device__ void uncheckedEnqueue(Lit p, CRef cref, AssignVardata *assigns_vardata, Lit *new_trail, unsigned int *trail_size, int decision_level)
{
  //printf(" propagate %d %d with reason %d on level %d\n", var_device(p), sign_device(p), cref, decision_level);
  // std::cout << " propagate " << var(p) << " " << sign(p) << " with reason "
  // << cref << std::endl;
  /// atomic increase trailsize
  int trail_p = atomicAdd(trail_size, 1);
  //int trail_p = *trail_size;
  //*trail_size = trail_p + 1;
  //printf("trail_p %d access\n", trail_p);
  new_trail[trail_p] = p;
  AssignVardata temp;
  temp.assign = create_bool_device_from_bool(!sign_device(p));
  temp.vardata = mkVarData_device(cref, decision_level);
  assigns_vardata[var_device(p)] = temp; // ensure that these are written atomically relaxed
}

__device__ lbool_device value_device(Lit p, AssignVardata *assigns)
{
  // printf("value for %d %d\n", var_device(p), sign_device(p));
  // printf("value assign %d\n", assigns[var_device(p)].assign);
  // printf("value sign %d\n", sign_device(p));
  // printf("value %d\n", assigns[var_device(p)].assign ^ (lbool_device)(sign_device(p)));
  // printf("value %d\n", create_bool_device_from_uc((lbool_device)assigns[var_device(p)].assign ^ (lbool_device)(sign_device(p))));
  return create_bool_device_from_uc((lbool_device)(assigns[var_device(p)].assign ^ (lbool_device)(sign_device(p))));
}

__device__ CRef reason_device(Var x, AssignVardata* assigns_vardata) { return assigns_vardata[x].vardata.reason; }
__device__ int level_device(Var x, AssignVardata* assigns_vardata) { return assigns_vardata[x].vardata.level; }

void destroy_solver(MySolver &solver)
{
    gpuErrchk(cudaFree(solver.confl_device));
    gpuErrchk(cudaFree(solver.device_trail));
    gpuErrchk(cudaFree(solver.device_trail_size));
    delete [] solver.host_trail;
    gpuErrchk(cudaFree(solver.qhead));
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

    gpuErrchk(cudaFree(solver.device_conflict));
    gpuErrchk(cudaFree(solver.device_conflict_size));
    gpuErrchk(cudaFree(solver.device_backtrack_level));
    delete solver.confl_host;
    delete[] solver.host_conflict;
}

__device__ bool isExactlyOneBitSet(uint32_t n) {
    return n && !(n & (n - 1));
}

__device__ int getSetBitPosition(uint32_t n) {
    return __ffs(n);
}

__device__ void analyze(bool* seen, unsigned int nVars, CRef confl, Lit* trail, unsigned int trail_size, uint32_t *ca, const int decision_level, AssignVardata* assigns_vardata ,Lit* out_learnt, unsigned int* out_learnt_size, unsigned int* out_btlevel);

__device__ void binary_propagation(unsigned int tid, unsigned int bid, unsigned int bdim, unsigned int gdim,
    unsigned int trail_p, int trail_max, Lit *new_trail, unsigned int *trail_size, AssignVardata *assigns_vardata, binWatchVector *watchesBin, const int decision_level, CRef *confl)
{
  // collect thread and block id and sizes
  // unsigned int tid = threadIdx.x;
  // unsigned int bid = blockIdx.x;
  // unsigned int bdim = blockDim.x;
  // unsigned int gdim = gridDim.x;

  //printf("enter binary_propagation %d %d %d\n", trail_p, *trail_size, trail_max);
  if (bid == 0 and tid == 0)
  {
    //printf("binary propagation with %d blocks and %d threads doing %d literals\n", gdim, bdim, trail_max-trail_p);
  }
  for (unsigned int lit_access=trail_p+bid; lit_access < trail_max; lit_access+=gdim)
  //while (trail_p < trail_max)
  {
    //printf("binary propagation %d\n", trail_p);
    Lit p = new_trail[lit_access];
    //printf("binary propagation %d %d\n", var_device(p), sign_device(p));
    //printf("watch binary clauses with index %d\n", watch_index_device(p));
    auto &wbin = watchesBin[watch_index_device(p)];
    if (tid == 0)
    {
      //printf("binary propagating literal with %d binary clauses\n", wbin.size);
    }
    for (int k = tid; k < wbin.size; k+=bdim)
    {
      //printf("binary propagation wbin %d of %d\n", k, wbin.size);
      Lit imp = wbin.watches[k].blocker;
      //printf("binary propagation imp %d %d\n", var_device(imp), sign_device(imp));
      //printf("binary propagation value %d\n", value_device(imp, assigns_vardata));
      /// be careful, there was a hidden == operator that didnt compare for equality
      if (compare_lbool_device(value_device(imp, assigns_vardata), l_False_device))
      {
        //printf("binary propagation conflict %d detected\n", wbin.watches[k].cref);
        *confl = wbin.watches[k].cref;
        //return;
      }
      if (compare_lbool_device(value_device(imp, assigns_vardata), l_Undef_device))
      {
        //printf("binary propagation enqueue %d %d\n", var_device(imp), sign_device(imp));
        uncheckedEnqueue(imp, wbin.watches[k].cref, assigns_vardata, new_trail, trail_size, decision_level);
      }
      else
      {
        //printf("binary propagation else\n");
      }
    }
  }
}


__device__ int warpReduceSum(int val) {
    unsigned mask = 0xffffffff; // All threads participate
    for (int offset = warpSize / 2; offset > 0; offset /= 2) {
        val += __shfl_down_sync(mask, val, offset);
    }
    return val;
}

template <unsigned int NUM_WARPS>
__device__ void nary_propagation(unsigned int tid, unsigned int bid, unsigned int bdim, unsigned int gdim,
    unsigned int trail_p, unsigned int trail_max, Lit *new_trail, unsigned int* trail_size, AssignVardata *assigns_vardata, watchVector *watches, uint32_t *ca, const int decision_level, CRef *confl) {
  Lit lit_Undef;
  lit_Undef.x = -2;

  //__shared__ unsigned int undef_counter[NUM_WARPS];
  //__shared__ Lit l[NUM_WARPS];

  const unsigned int thread_index = tid/32;
  //undef_counter[thread_index] = 0;
  //l[thread_index] = lit_Undef;
  // printf("Block %d and thread %d entering\n", bid, tid);
  __syncthreads();

  // unsigned int tid = threadIdx.x;
  // unsigned int bid = blockIdx.x;
  // unsigned int bdim = blockDim.x;
  // unsigned int gdim = gridDim.x;
  // printf("enter nary_propagation %d %d\n", trail_p, trail_max);
  if (bid == 0 and tid == 0)
  {
    //printf("nary propagation with %d blocks and %d threads doing %d literals\n", gdim, bdim, trail_max-trail_p);
  }
  for (unsigned int lit_access=trail_p+bid; lit_access < trail_max; lit_access+=gdim) {
  //while (trail_p < trail_max) {
    //printf("nary propagation %d\n", trail_p);
    Lit p = new_trail[lit_access];
    //printf("nary propagation lit p %d %d\n", var_device(p), sign_device(p));
    watchVector &wnary = watches[watch_index_device(p)];
    //printf("accessed wnary with index %u \n", watch_index_device(p));
    if (tid == 0)
    {
      //printf("nary propagating literal with %d nary clauses\n", wnary.size);
    }
    for (int k = thread_index; k < wnary.size; k+=NUM_WARPS) {
      
      CRef cref = wnary.crefs[k];
      //printf("nary propagation cref %d\n", cref);
      const Clause &clause =
          *reinterpret_cast<Clause *>(&ca[reinterpret_cast<uint32_t>(cref)]);
      if (tid % 32 == 0) {
          //printf("nary propagation wnary access %d of %u has clause size: %d\n", k, wnary.size, clause.size());
      }
      //printf("nary propagation clause size %d\n", clause.size());
      /// CAN BE OPTIMIZED USING __shfl_down_sync
      unsigned int undef_counter_local = 0;
      Lit l = lit_Undef;
      for (int i = tid-(thread_index*32); i < clause.size(); i+=32) {
        //printf("Handling position %d of clause %d by thread %d\n", i, k, tid);
        if (compare_lbool_device(value_device(clause[i], assigns_vardata), l_True_device)) {
          undef_counter_local += 2;
          //atomicAdd_block(&undef_counter[thread_index], 2);
          // printf("True: %d increased undef_counter[%d] to %d\n", i, thread_index, undef_counter[thread_index]);
          //goto Continue; // at least 1 true literal
        }
        else if (compare_lbool_device(value_device(clause[i], assigns_vardata), l_Undef_device)) {
          ++undef_counter_local;
          //atomicAdd_block(&undef_counter[thread_index], 1);
          // printf("Undef: %d increased undef_counter[%d] to %d\n", i, thread_index, undef_counter[thread_index]);
          //l[thread_index] = clause[i];
          l = clause[i];
          //printf("Block %d and thread %d found undefined literal %d %d\n", bid, tid, var_device(l), sign_device(l));
        }
        
      }
      //printf("Thread %d and block %d found %d undefined literals\n", bid, tid, undef_counter_local);
      undef_counter_local = warpReduceSum(undef_counter_local); // i can make this shorter by using clause.size to only add up the necessary values
      undef_counter_local = __shfl_sync(0xffffffff, undef_counter_local, 0);
      //printf("Afterwards thread %d and block %d found %d undefined literals\n", bid, tid, undef_counter_local);
      __syncwarp(); // redundant?
      // printf("Tid: %d, Tid mod 32: %d.  After sync undef_counter[%d] = %d\n", tid, tid%32, thread_index, undef_counter[thread_index]);
      //if (tid%32 == 0) { // use the first thread of the warp to check the results
        // printf("Thread %d and block %d found %d undefined literals\n", bid, tid, undef_counter[thread_index]);
      if (undef_counter_local == 1 && l != lit_Undef) {
        //printf("Block %d and thread %d enqueue %d %d\n", bid, tid, var_device(l), sign_device(l));
        uncheckedEnqueue(l, cref, assigns_vardata, new_trail, trail_size, decision_level);
      }
      if (tid%32 == 0 && undef_counter_local == 0) {
        //printf("nary propagation conflict %d\n", cref);
        *confl = cref;
        //return;
      }
      //}
      
     
      __syncwarp();
     
      // // if there is a conflict in any other warp we have to stop
      /// there is no easy way to stop the whole kernel except for pulling a global variable
      // for (unsigned int i = 0; i < num_warps; i++) {
      //   if (undef_counter[i] == 0) {
      //     printf("Block %d and thread %d leaving\n", bid, tid);
      //     return;
      //   }
      // }
      // __syncthreads();
    }
  }
  //printf("Block %d and thread %d leaving\n", bid, tid);
}

//compare with original code propagation using git stash


__device__ void valid_propagation(unsigned int tid, unsigned int bid, unsigned int bdim, unsigned int gdim,
    unsigned int trail_p, int trail_max, Lit *new_trail, AssignVardata *assigns_vardata, CRef *confl) {
  // unsigned int tid = threadIdx.x;
  // unsigned int bdim = blockDim.x;
  for (unsigned int lit_access=trail_p+tid+bid*bdim; lit_access < trail_max; lit_access+=bdim) {
  //while (trail_p < trail_max) {
    Lit p = new_trail[lit_access];
    if (compare_lbool_device(value_device(p, assigns_vardata), l_False_device)) {
      *confl = assigns_vardata[var_device(p)].vardata.reason;
      return;
    }
  }
}

void copyConflictToHost(MySolver &solver)
{
  gpuErrchk(cudaMemcpy(solver.confl_host, solver.confl_device, sizeof(CRef), cudaMemcpyDeviceToHost));
  gpuErrchk(cudaMemcpy(solver.host_conflict, solver.device_conflict, sizeof(Lit)*solver.host_num_vars, cudaMemcpyDeviceToHost));
  gpuErrchk(cudaMemcpy(&solver.host_conflict_size, solver.device_conflict_size, sizeof(unsigned int), cudaMemcpyDeviceToHost));
  gpuErrchk(cudaMemcpy(&solver.host_backtrack_level, solver.device_backtrack_level, sizeof(unsigned int), cudaMemcpyDeviceToHost));
}

void copyTrailToHost(MySolver &solver)
{
  gpuErrchk(cudaMemcpy(solver.host_trail, solver.device_trail, sizeof(Lit)*solver.host_num_vars, cudaMemcpyDeviceToHost)); // can be optimized
  gpuErrchk(cudaMemcpy(&solver.host_trail_size, solver.device_trail_size, sizeof(unsigned int), cudaMemcpyDeviceToHost));
}

void compare(MySolver &mysolver, Solver& s, CRef confl)
{
  copyConflictToHost(mysolver);
  copyTrailToHost(mysolver);
  /// either both are in conflict or both are not in conflict
  if (*mysolver.confl_host == CRef_Undef && confl == CRef_Undef)
  {
    // both trails are the same (set comparison)
    // print host trail and trail
    // for (int i = 0; i < solver.host_trail_size; i++)
    // {
    //   std::cout << "host trail " << i << " " << toInt(solver.host_trail[i]) << std::endl;
    // }
    // for (int i = 0; i < s.trail.size(); i++)
    // {
    //   std::cout << "trail " << i << " " << toInt(s.trail[i]) << std::endl;
    // }
    std::set<Lit> myset(mysolver.host_trail, mysolver.host_trail + mysolver.host_trail_size);
    std::set<Lit> theirset(s.trail.data, s.trail.data + s.trail.size());
    
    // write relation between the two sets
    // std::cout << "my trail size " << mysolver.host_trail_size << " and their trail size " << s.trail.size() << std::endl;
    // std::cout << "sizes: " << myset.size() << "/" << theirset.size() << std::endl;
    // if (std::includes(theirset.begin(), theirset.end(), myset.begin(), myset.end()))
    // {
    //   std::cout << "my set is a subset of theirs" << std::endl;
    //   //return;
    // }
    // // if theirset is a subset of myset
    // if (std::includes(myset.begin(), myset.end(), theirset.begin(), theirset.end()))
    // {
    //   std::cout << "theirset is a subset of myset" << std::endl;
    //   //return;
    // }
    // if (myset != theirset)
    //   std::cout << "trails complte different" << std::endl;
    

    assert (myset == theirset);
    return;
  }

  if (*mysolver.confl_host == confl) {
    // compare analyzed conflicts
    //std::cout << "conflict is the same" << std::endl;
  } else {
    //std::cout << "different conflict detected " << *solver.confl_host << " " << confl << std::endl;
  }

  // if(confl != CRef_Undef) { // they have a conflict
  //   // std::cout << "they have conflict, fine" << std::endl;
  //   return;
  // }
  assert (*mysolver.confl_host != CRef_Undef && confl != CRef_Undef);
  //std::cout << "PROBLEM: I have a conflict, they not" << std::endl;
}

__global__ void propagate_control(MySolver solver);

// __global__ void propagate_end(MySolver solver, unsigned int trail_max) {
//   //printf("propagate end with previous qhead %d and new %d and confl %d \n", *solver.qhead, trail_max, *solver.confl_device);
//   *solver.qhead = trail_max;
//   //printf("propagate end with device_trail_size %d\n", *solver.device_trail_size);
//   /// print trail with respective decision levels
//   for (int i = 0; i < *solver.device_trail_size; i++) {
//     //printf("trail %d %d with level %d\n", var_device(solver.device_trail[i]), sign_device(solver.device_trail[i]), level_device(var_device(solver.device_trail[i]), solver.assigns_vardata));
//   }
//   if (*solver.confl_device != CRef_Undef)
//   {
//     if (solver.decision_level == 0)
//     {
//       // conflict on dl 0
//       return;
//     }
//     analyze<<<1, 1, solver.host_num_vars * sizeof(bool), cudaStreamTailLaunch>>>(solver.host_num_vars, *solver.confl_device, solver.device_trail, *solver.device_trail_size, solver.ca, solver.decision_level, solver.assigns_vardata, solver.device_conflict, solver.device_conflict_size, solver.device_backtrack_level);
//     return;
//   }
//   else if (*solver.device_trail_size > trail_max)
//   {
//     //printf("continue propagation\n");
//     propagate_control<<<1, 1, 0, cudaStreamTailLaunch>>>(solver);
//   }
// }

// __global__ void propagate_control(MySolver solver) {
//   // assert only 1 thread and 1 block running
//   /// TODO

//   unsigned int trail_max = *solver.device_trail_size;
//   unsigned int qhead = *solver.qhead;
//   //printf("propagate control on decision level %d with qhead %d and trail_max %d\n", solver.decision_level, qhead, trail_max);
//   /// print trail with respective decision levels
//   //for (int i = 0; i < *solver.device_trail_size; i++) {
//     //printf("trail %d %d with level %d\n", var_device(solver.device_trail[i]), sign_device(solver.device_trail[i]), level_device(var_device(solver.device_trail[i]), solver.assigns_vardata));
//   //}
  
//   binary_propagation<<<8, 32, 0, cudaStreamFireAndForget>>>(qhead, trail_max, solver.device_trail, solver.device_trail_size, solver.assigns_vardata, solver.watchesBin, solver.decision_level, solver.confl_device);
//   nary_propagation<<<8, 32, 0, cudaStreamFireAndForget>>>(qhead, trail_max, solver.device_trail, solver.device_trail_size, solver.assigns_vardata, solver.watches, solver.ca, solver.decision_level, solver.confl_device);
//   valid_propagation<<<1, 32, 0, cudaStreamTailLaunch>>>(qhead, trail_max, solver.device_trail, solver.assigns_vardata, solver.confl_device);
//   propagate_end<<<1, 1, 0, cudaStreamTailLaunch>>>(solver, trail_max);
// }

template <unsigned int NUM_WARPS>
__global__ void propagate_control2(MySolver solver) {
  unsigned int tid = threadIdx.x;
  unsigned int bid = blockIdx.x;
  unsigned int bdim = blockDim.x;
  unsigned int gdim = gridDim.x;
  //extern __shared__ bool seen[]; 
  cooperative_groups::grid_group g = cooperative_groups::this_grid(); 
  //printf("Enter control2 %d %d\n", tid, bid);
  // printf("I can synchronize: %d\n", g.is_valid());
  // cudaError_t t = cudaPeekAtLastError();
  // printf("GPUassert: %s\n", cudaGetErrorString(t));
  //if (bid == 0 && tid == 0) printf("ALL ENTER\n");
  g.sync();
  // t = cudaPeekAtLastError();
  // printf("GPUassert: %s\n", cudaGetErrorString(t));

  unsigned int trail_max = *solver.device_trail_size;
  unsigned int qhead = *solver.qhead;
  //printf("propagate control on decision level %d with qhead %d and trail_max %d\n", solver.decision_level, qhead, trail_max);
  /// print trail with respective decision levels
  //for (int i = 0; i < *solver.device_trail_size; i++) {
    //printf("trail %d %d with level %d\n", var_device(solver.device_trail[i]), sign_device(solver.device_trail[i]), level_device(var_device(solver.device_trail[i]), solver.assigns_vardata));
  //}
  while(true) {

    //printf("start while loop %d %d\n", bid, tid);
    const int divide=2;
    if (bid < gdim/divide)
      binary_propagation(tid, bid, bdim, gdim/divide, qhead, trail_max, solver.device_trail, solver.device_trail_size, solver.assigns_vardata, solver.watchesBin, solver.decision_level, solver.confl_device);
    else
      nary_propagation<NUM_WARPS>(tid, bid-gdim/divide, bdim, gdim/divide, qhead, trail_max, solver.device_trail, solver.device_trail_size, solver.assigns_vardata, solver.watches, solver.ca, solver.decision_level, solver.confl_device);

    //printf("Block/Thread %d %d ready to sync\n", bid, tid);
    
    
    g.sync();
    //if (bid == 0 && tid == 0) printf("ALL SYNCED\n");
    //*solver.qhead = trail_max;
    //printf("propagate end with device_trail_size %d\n", *solver.device_trail_size);
    /// print trail with respective decision levels
    // for (int i = 0; i < *solver.device_trail_size; i++) {
    //   //printf("trail %d %d with level %d\n", var_device(solver.device_trail[i]), sign_device(solver.device_trail[i]), level_device(var_device(solver.device_trail[i]), solver.assigns_vardata));
    // }
    
    
    if (*solver.device_trail_size <= trail_max)
    {
      //printf("reached fixpoint\n");
      //g.sync();

      valid_propagation(tid, bid, bdim, gdim, qhead, *solver.device_trail_size, solver.device_trail, solver.assigns_vardata, solver.confl_device);
      //printf("FINISHED PROPAGATION FOR BLOCK %d and THREAD %d\n", bid, tid);
      return;
    }
    else {
      qhead = trail_max;
      trail_max = *solver.device_trail_size;
      //printf("continue propagation with trail size %d/%d\n", qhead, trail_max);
    }

    g.sync();

    if (*solver.confl_device != CRef_Undef)
    {
      //printf("conflict: %d\n", *solver.confl_device);
      // if (bid == 0 && tid == 0)
      // {
      //   if (solver.decision_level > 0)
      //     analyze(seen, solver.host_num_vars, *solver.confl_device, solver.device_trail, *solver.device_trail_size, solver.ca, solver.decision_level, solver.assigns_vardata, solver.device_conflict, solver.device_conflict_size, solver.device_backtrack_level);
      // }
      //printf("FINISHED CONFLICT FOR BLOCK %d and THREAD %d\n", bid, tid);
      return;
    }

    g.sync(); // I cant let some blocks continue to create a conflict so old blocks get caught here. Why not? Because they get stuck on some other sync then
  }
}


void propagate(MySolver &solver)
{
  static int num = 0;
  // std::cout << "propagate " << num << std::endl;
  ++num;
  cudaEvent_t start, stop;
  cudaEventCreate(&start);
  cudaEventCreate(&stop);

  void *kernelArgs[] = {&solver};

  #define NUM_THREADS 128
  #define NW (NUM_THREADS/32)

  cudaEventRecord(start);
  cudaLaunchCooperativeKernel((void*)&propagate_control2<NW>, 12, NUM_THREADS, kernelArgs,  0/*solver.host_num_vars * sizeof(bool)*/, 0);
  cudaEventRecord(stop);
  //empty_test<<<1, 1>>>();

  gpuErrchk( cudaPeekAtLastError() );
  gpuErrchk( cudaEventSynchronize(stop) );
  //gpuErrchk(cudaDeviceSynchronize());
  float milliseconds = 0;
  cudaEventElapsedTime(&milliseconds, start, stop);
  std::cout << "propagate time: " << int(milliseconds*1000) << std::endl;



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


// 1 move over conflicting clause
// everything from old decision level is added to the conflict clause
// everything on current decision level is replaced by its reason
// same rules apply for reason, everything old is added, everything new is replaced
// we all all this in backwards order of trail
// stop condition unclear
__device__ void analyze(bool* seen, unsigned int nVars, CRef confl, Lit* trail, unsigned int trail_size, uint32_t *ca, const int decision_level, AssignVardata* assigns_vardata ,Lit* out_learnt, unsigned int* out_learnt_size, unsigned int* out_btlevel) {
    int pathC = 0;
    Lit lit_Undef;
    lit_Undef.x = -2;
    Lit p = lit_Undef;
    *out_learnt_size = 0;
    //printf("Analyze with trail size %d\n", trail_size);
    for (int i = 0; i < trail_size; i++) {
        //printf("trail %d %d\n", var_device(trail[i]), sign_device(trail[i]));
    }

    /// create shared memory for seen variables in size of variables
    /// initialize correctly with nvars*sizeof(bool)
    for (unsigned int i = 0; i < nVars; ++i) {
      //printf("Accessing shared memory\n");
      seen[i] = false;
    }
    //printf("set all seen to false\n");
    // in the current decision level which is much smaller, but then indexing gets much harder

    // Generate conflict clause:
    //
    *out_learnt_size +=1;  // (leave room for the asserting literal)
    unsigned int index = trail_size - 1;
    do {
        //printf("index %d and pathC %d\n", index, pathC);
        //printf("ConflictCRef: %d\n", confl);
        assert(confl != CRef_Undef); // (otherwise should be UIP)
        const Clause &c = *reinterpret_cast<Clause *>(&ca[reinterpret_cast<uint32_t>(confl)]);
        //printf("c analysiere %d\n", confl);
        for (int i = 0; i < c.size(); i++) {
           //printf("c %d %d with level %d\n", var_device(c[i]), sign_device(c[i]), level_device(var_device(c[i]), assigns_vardata));
        }

        for(int j = 0; j < c.size(); j++) {
            Lit q = c[j];
            if (p == q)
                continue;

            //printf("check for seen %d\n", var_device(q));
            if(!seen[var_device(q)]) {
                //printf("not yet seen\n");
                if(level_device(var_device(q), assigns_vardata) == 0) {
                } else { // Here, the old case
                    seen[var_device(q)] = true;
                    //printf("compare level %d >= %d\n", level_device(var_device(q), assigns_vardata), decision_level);
                    if(level_device(var_device(q), assigns_vardata) >= decision_level) {
                        //printf("increment pathC\n");
                        pathC++;
                    } else {
                        //printf("accessing out_learnt %d and writing %d %d\n", *out_learnt_size, var_device(q), sign_device(q));
                        out_learnt[(*out_learnt_size)++] = q;
                    }
                }
            }
        }
        //printf("end of loop, trailing down with index %d\n", index);

        // Select next clause to look at:
        while (!seen[var_device(trail[index--])]);
        //printf("trailed down to %d\n", index);
        p = trail[index + 1];
        //printf("next p %d %d\n", var_device(p), sign_device(p));
        //stats[sumRes]++;
        confl = reason_device(var_device(p), assigns_vardata);
        //printf("next confl %d\n", confl);
        seen[var_device(p)] = false;
        //printf("set seen %d to false\n", var_device(p));
        pathC--;
        //printf("decrement pathC to %d\n", pathC);

    } while(pathC > 0);
    
    out_learnt[0] = ~p;
    
    // Find correct backtrack level:
    //
    if(*out_learnt_size == 1)
        *out_btlevel = 0;
    else {
        int max_i = 1;
        // Find the first literal assigned at the next-highest level:
        for(int i = 2; i < *out_learnt_size; i++)
            if(level_device(var_device(out_learnt[i]), assigns_vardata) > level_device(var_device(out_learnt[max_i]), assigns_vardata))
                max_i = i;
        // Swap-in this literal at index 1:
        Lit p = out_learnt[max_i];
        out_learnt[max_i] = out_learnt[1];
        out_learnt[1] = p;
        *out_btlevel = level_device(var_device(p), assigns_vardata);
    }
}


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
