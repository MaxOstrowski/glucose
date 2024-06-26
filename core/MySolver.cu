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

/// This create a ordered heap datastructure for cuda device code
/// It has a fixed size limit and does no checks on size
/// It has also support for increase/decrease key operations
/// It is a min heap

#include "core/SolverTypes.h"

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
  gpuErrchk(cudaMemcpy(const_cast<AssignVardata*>(mysolver.assigns_vardata), temp, sizeof(AssignVardata) * num_vars, cudaMemcpyHostToDevice));
  delete[] temp;

  // copy binary watch lists
  mysolver.hostBinWatch = new binWatchVector[num_vars * 2];

  
  for (unsigned int i = 0; i < num_vars; ++i)
  {
    {
      Lit lit = mkLit(i, false);
      unsigned int size = solver.watchesBin[lit].size();
      mysolver.hostBinWatch[watch_index(lit)].size = size;
      mysolver.hostBinWatch[watch_index(lit)].capacity = size;
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
      mysolver.hostBinWatch[watch_index(lit)].capacity = size;
      mysolver.hostBinWatch[watch_index(lit)].watches = nullptr;
      if (size > 0) {
        gpuErrchk(cudaMalloc((void **)&mysolver.hostBinWatch[watch_index(lit)].watches, size * sizeof(Solver::Watcher)));
        gpuErrchk(cudaMemcpy(mysolver.hostBinWatch[watch_index(lit)].watches, solver.watchesBin[lit].data, sizeof(Solver::Watcher) * size, cudaMemcpyHostToDevice));
      }
    }
  }

  gpuErrchk(cudaMalloc((void **)&mysolver.device_watchesBin, sizeof(binWatchVector) * num_vars * 2));
  gpuErrchk(cudaMemcpy(mysolver.device_watchesBin, mysolver.hostBinWatch, sizeof(binWatchVector) * num_vars * 2, cudaMemcpyHostToDevice));

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
      mysolver.hostWatches[watch_index(lit)].capacity = size;
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
      mysolver.hostWatches[watch_index(lit)].capacity = size;
      mysolver.hostWatches[watch_index(lit)].crefs = nullptr;
      if (size > 0) {
        gpuErrchk(cudaMalloc((void **)&mysolver.hostWatches[watch_index(lit)].crefs, size * sizeof(CRef)));
        
        gpuErrchk(cudaMemcpy(mysolver.hostWatches[watch_index(lit)].crefs, clause_refs[watch_index(lit)].data(), sizeof(CRef) * size, cudaMemcpyHostToHost));
      }
    }
  }
  gpuErrchk(cudaMalloc((void **)&mysolver.device_watches, sizeof(watchVector) * num_vars * 2));
  gpuErrchk(cudaMemcpy(mysolver.device_watches, mysolver.hostWatches, sizeof(watchVector) * num_vars * 2, cudaMemcpyHostToDevice));


  // copy clause database
  unsigned int ca_size = solver.ca.size();
  gpuErrchk(cudaMalloc((void **)&mysolver.device_ca, sizeof(uint32_t) * solver.ca.size()));
  gpuErrchk(cudaMemcpy(mysolver.device_ca, solver.ca.lea(0), sizeof(uint32_t) * solver.ca.size(), cudaMemcpyHostToDevice));
  gpuErrchk(cudaMalloc((void **)&mysolver.device_ca_size, sizeof(uint32_t)));
  gpuErrchk(cudaMemcpy(mysolver.device_ca_size, &ca_size, sizeof(uint32_t), cudaMemcpyHostToDevice)); // could already reserve some extra memory!
  gpuErrchk(cudaMalloc((void **)&mysolver.device_ca_capacity, sizeof(uint32_t)));
  gpuErrchk(cudaMemcpy(mysolver.device_ca_capacity, &ca_size, sizeof(uint32_t), cudaMemcpyHostToDevice));

  // create device_seen and initialize with false
  gpuErrchk(cudaMalloc((void **)&mysolver.device_seen, sizeof(bool) * num_vars));
  gpuErrchk(cudaMemset(mysolver.device_seen, 0, sizeof(bool) * num_vars));

  // initialie selection heap
  mysolver.host_decision_heap = new CudaOrderedHeap();
  mysolver.host_decision_heap->init(num_vars);
  gpuErrchk(cudaMalloc((void **)&mysolver.device_decision_heap, sizeof(CudaOrderedHeap)));
  gpuErrchk(cudaMemcpy(mysolver.device_decision_heap, mysolver.host_decision_heap, sizeof(CudaOrderedHeap), cudaMemcpyHostToDevice));
  
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
  
  /// atomic increase trailsize
  int trail_p = atomicAdd_block(trail_size, 1);
  // printf(" Thread %d propagate %d %d with reason %d on level %d in trail position %d\n", threadIdx.x, var_device(p), sign_device(p), cref, decision_level, trail_p);
  new_trail[trail_p] = p;
  AssignVardata temp;
  temp.assign = create_bool_device_from_bool(!sign_device(p));
  temp.vardata = mkVarData_device(cref, decision_level);
  assigns_vardata[var_device(p)] = temp; // ensure that these are written atomically relaxed
}

__device__ Lit pick_branch_lit(CudaOrderedHeap* heap, AssignVardata* assigns_vardata, unsigned int num_vars) {
  for (Var i = 0; i < num_vars; ++i) {
    if (assigns_vardata[i].assign == l_Undef_device) {
      return mkLit_device(i, false);
    }
  }
  return lit_Undef;
  //return mkLit_device(heap->pop(), false);
}


// EVEN IF I GO TO 1 Block and 1024 threads (32 warps) I have problems with the free scheduling of work.
// If 1 warp writes to assign, it can call threadfence to ensure that it is written into global memory.
// This does not ensure that another thread will not try to read this new memory beforehand and get the old result.
// __syncthreads() does exactly this. So what do my 32 warps do

// 1. Either each warp takes a literal and runs all clauses on it. This is not efficient, as we have to wait for the slowest warp.
// 2. Each warp runs 1 clause. This is hard to coordinate as we do not now how many clauses per literal we have.
// We would need to have an actual barrier where each thread atomically selects a literal and a clause index and starts processing it.
// As we are synced anyway I could use a warp to schedule all warps first.
// There is a shared variable for each warp, determining the literal and the clause to process.
// Thread 0/0 writes this variable, then every synchronizes, then everybody gets to work. Then sync again
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
    gpuErrchk(cudaFree(solver.device_watchesBin));
    gpuErrchk(cudaFree(solver.device_watches));
    delete[] solver.hostBinWatch;
    delete[] solver.hostWatches;
    gpuErrchk(cudaFree(solver.device_ca));
    gpuErrchk(cudaFree(solver.device_ca_size));
    gpuErrchk(cudaFree(solver.device_ca_capacity));

    gpuErrchk(cudaFree(solver.device_conflict));
    gpuErrchk(cudaFree(solver.device_conflict_size));
    gpuErrchk(cudaFree(solver.device_backtrack_level));
    delete solver.confl_host;
    delete[] solver.host_conflict;
    solver.host_decision_heap->destroy();
    gpuErrchk(cudaFree(solver.device_decision_heap));
    gpuErrchk(cudaFree(solver.device_seen));
}

__device__ bool isExactlyOneBitSet(uint32_t n) {
    return n && !(n & (n - 1));
}

__device__ int getSetBitPosition(uint32_t n) {
    return __ffs(n);
}

// 1 move over conflicting clause
// everything from old decision level is added to the conflict clause
// everything on current decision level is replaced by its reason
// same rules apply for reason, everything old is added, everything new is replaced
// we all all this in backwards order of trail
// stop condition unclear
__device__ void analyze(bool* seen, CudaOrderedHeap* decision_heap, int nVars, CRef confl, Lit* trail, unsigned int trail_size, uint32_t *ca, const int decision_level, AssignVardata* assigns_vardata ,Lit* out_learnt, unsigned int* out_learnt_size, unsigned int* out_btlevel) {
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
                //decision_heap->increaseKey(var_device(q));
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

__device__ void binary_propagation(unsigned int trail_p, Lit *new_trail, unsigned int *trail_size, AssignVardata *assigns_vardata, binWatchVector *watchesBin, const int decision_level, CRef *confl)
{
  Lit p = new_trail[trail_p];
  auto &wbin = watchesBin[watch_index_device(p)];
  //if (threadIdx.x % warpSize == 0) printf("Bin Prop for lit index %d has %d watches\n", trail_p, wbin.size);
  for (int k = threadIdx.x%warpSize; k < wbin.size; k+=warpSize)
  {
    Lit imp = wbin.watches[k].blocker;
    /// be careful, there was a hidden == operator that didnt compare for equality
    if (compare_lbool_device(value_device(imp, assigns_vardata), l_False_device))
    {
      // printf("binary prop conflict\n");
      *confl = wbin.watches[k].cref;
    }
    if (compare_lbool_device(value_device(imp, assigns_vardata), l_Undef_device))
    {
      // printf("Thread %d found a binary implication for watch %d\n", threadIdx.x, k);
      uncheckedEnqueue(imp, wbin.watches[k].cref, assigns_vardata, new_trail, trail_size, decision_level);
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

__device__ void nary_propagation(unsigned int trail_p, unsigned int clause_index, Lit *new_trail, unsigned int* trail_size, AssignVardata *assigns_vardata, watchVector *watches, uint32_t *ca, const int decision_level, CRef *confl) {
  Lit lit_Undef;
  lit_Undef.x = -2;

  Lit p = new_trail[trail_p];
  watchVector &wnary = watches[watch_index_device(p)];
  CRef cref = wnary.crefs[clause_index];
  const Clause &clause = *reinterpret_cast<Clause *>(&ca[reinterpret_cast<uint32_t>(cref)]);
   
  unsigned int undef_counter_local = 0;
  Lit l = lit_Undef;
  for (int i = threadIdx.x%warpSize; i < clause.size(); i+=warpSize) {
    if (compare_lbool_device(value_device(clause[i], assigns_vardata), l_True_device)) {
      // printf("Thread %d found a true literal in clause %d\n", threadIdx.x, clause_index);
      undef_counter_local += 2;
    }
    else if (compare_lbool_device(value_device(clause[i], assigns_vardata), l_Undef_device)) {
      // printf("Thread %d found an undef literal in clause %d\n", threadIdx.x, clause_index);
      ++undef_counter_local;
      l = clause[i];
    }
  }
    
  undef_counter_local = warpReduceSum(undef_counter_local); // i can make this shorter by using clause.size to only add up the necessary values
  undef_counter_local = __shfl_sync(0xffffffff, undef_counter_local, 0);

  // if (threadIdx.x % warpSize == 0) printf("Thread %d has %d undef literals in clause %d\n", threadIdx.x, undef_counter_local, clause_index);

  if (undef_counter_local == 1 && l != lit_Undef) {
    uncheckedEnqueue(l, cref, assigns_vardata, new_trail, trail_size, decision_level);
  }
  if (threadIdx.x%warpSize == 0 && undef_counter_local == 0) {
    // printf("nary prop conflict\n");
    *confl = cref;
  }
}

//compare with original code propagation using git stash


__device__ void valid_propagation(unsigned int trail_p, int trail_max, Lit *new_trail, AssignVardata *assigns_vardata, CRef *confl) {
  // unsigned int tid = threadIdx.x;
  // unsigned int bdim = blockDim.x;
  for (unsigned int lit_access=trail_p+threadIdx.x; lit_access < trail_max; lit_access+=blockDim.x) {
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

    // std::cout << "my trail: ";
    // for (auto it = myset.begin(); it != myset.end(); ++it)
    // {
    //   std::cout << "( " << var(*it) << " " << sign(*it) << " ) ";
    // }
    // std::cout << std::endl;
    // std::cout << "their trail: ";
    // for (auto it = theirset.begin(); it != theirset.end(); ++it)
    // {
    //   std::cout << "( " << var(*it) << " " << sign(*it) << " ) ";
    // }
    // std::cout << std::endl;
    

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

/// method adds a clause to the clause database
/// might need to reallocate space in ca
__device__ void add_clause(Lit* conflict, unsigned int* conflict_size, uint32_t** ca, unsigned int* ca_size, unsigned int* ca_capacity, watchVector* watches, binWatchVector* watchesBin) {
  if (*ca_size + *conflict_size > *ca_capacity) {
    //printf("need to reallocate clause database\n");
    unsigned int new_capacity = (int)(*ca_capacity * 1.5f); // minimum growth should be clause size!
    uint32_t* new_ca = new uint32_t[new_capacity];
    for (unsigned int i = 0; i < *ca_size; ++i) {
      new_ca[i] = (*ca)[i];
    }
    delete[] *ca; //make test to see if I can use delete[] in device code BAD: https://docs.nvidia.com/cuda/cuda-c-programming-guide/index.html#dynamic-global-memory-allocation-and-operations
    /// dynamic new/delete seems to be using "heap" memory, which is not the same as global memory but a predefined subset, set to 8MB on default
    (*ca) = new_ca;
    *ca_capacity = new_capacity;
  }
  //printf("add clause with size %d\n", *conflict_size);
  Clause& c = *(Clause*)(*ca)[*ca_size];
  c.header.mark      = 0;
  c.header.learnt    = 1;
  c.header.extra_size = 0;
  c.header.reloced   = 0;
  c.header.size      = *conflict_size;
  c.header.lbd = 0;
  c.header.canbedel = 1;
  c.header.exported = 0; 
  c.header.oneWatched = 0;
  c.header.simplified = 0;
  c.header.seen = 0;
  
  for (int i = 0; i < c.header.size; i++) 
    c.data[i].lit = conflict[i];

  // add watches and maybe increase watch size 
  if (*conflict_size == 2) {
    Lit p = conflict[0];
    Lit q = conflict[1];
    watchesBin[watch_index_device(p)].push(*ca_size, q);
    watchesBin[watch_index_device(q)].push(*ca_size, p);
  }
  else {
    for (int i = 0; i < c.header.size; i++) {
      watches[watch_index_device(c.data[i].lit)].push(*ca_size);
    }
  }

  *ca_size += sizeof(Clause)/sizeof(uint32_t) + *conflict_size;
	
}


__device__ void backtrack(unsigned int backtrack_level, AssignVardata* assigns_vardata, unsigned int& decision_level, Lit* device_trail, unsigned int* device_trail_size) {
  unsigned int trail_p = *device_trail_size;
  while (trail_p > 0 && level_device(var_device(device_trail[trail_p-1]), assigns_vardata) > backtrack_level) {
    assigns_vardata[var_device(device_trail[trail_p-1])].assign = l_Undef_device;
    --trail_p;
  }
  *device_trail_size = trail_p;
  decision_level = backtrack_level;
}


template <unsigned char NUM_WARPS>
__global__ void propagate_control2(MySolver solver) {

  // if (threadIdx.x == 0) {
  //   printf("All heap pointer information: \n");
  //   printf("Heap size %d\n", solver.device_decision_heap->size);
  //   printf("Heap heap %p\n", solver.device_decision_heap->heap);


    
  // }

  unsigned char warp_id = threadIdx.x / warpSize;
  const unsigned char NUM_BIN_PROP_WARPS = 2;

  unsigned int original_qhead = *solver.qhead;
  if (original_qhead == *solver.device_trail_size) {
    return;
  }
  //if (threadIdx.x == 0) { printf("Start propagation with qhead %d and trail size %d\n", original_qhead, *solver.device_trail_size); }
  
  /*
  Clauses can be learnt by reserving all memory we have in advance. Problem. Watches need to grow dynamically. Apparently i can use new/delete[] now in kernels for global memory.
  */
  __shared__ unsigned int decision_level;
  decision_level = solver.decision_level;
  __shared__ int qhead_index[NUM_WARPS];
  __shared__ int clause_index[NUM_WARPS]; // can safe one for thread 0, as bin prop does not need it
  __shared__ bool fixpoint;
  fixpoint = false;
  __shared__ bool exhausted;
  exhausted = false;

  unsigned int qhead_start_nary = original_qhead; // currently only used in warp 0
  unsigned int qhead_start_binary = original_qhead; // currently only used in warp 0
  for (unsigned char i = 0; i < NUM_BIN_PROP_WARPS; ++i) {
    qhead_index[i] = original_qhead-1+i;
  }
  for (unsigned char i = 0; i < NUM_WARPS; ++i) {
    clause_index[i] = -1;
  }
  unsigned int clause_start = 0;
  __syncthreads();

  while(true) {
    while(true) { // busy waiting loop

      __syncthreads();
      if (exhausted) {
        return;
      }
      if (warp_id == 0) {
        /// thread 0 spreads the work to all warps 1..NUM_WARPS
        /// warp 0 is supposed to do binary propagation
        if (threadIdx.x == 0) {
          if (*solver.confl_device != CRef_Undef) {
            fixpoint = true;
          }
          else {
            // assign work for binary propagation
            for (unsigned int i = 0; i < NUM_BIN_PROP_WARPS; ++i) {
              if (qhead_start_binary < *solver.device_trail_size) {
                qhead_index[i] = qhead_start_binary;
                ++qhead_start_binary;
              }
              else {
                qhead_index[i] = -1;
              }
            }
            // assign work for nary propagation
            unsigned char num_created = NUM_BIN_PROP_WARPS;
            while (qhead_start_nary < *solver.device_trail_size) {
              Lit p = solver.device_trail[qhead_start_nary];
              watchVector &wnary = solver.device_watches[watch_index_device(p)];
              unsigned int max_loop = min((unsigned int)(NUM_WARPS-num_created), (unsigned int)(wnary.size - clause_start));
              // printf(" for qstart %d max loop %d and wnary.size %d and num_created before %d and clause start %d\n", qhead_start_nary, max_loop, wnary.size, num_created, clause_start);
              for (unsigned int k = 0; k < max_loop; ++k) {
                qhead_index[num_created+k] = qhead_start_nary;
                clause_index[num_created+k] = clause_start;
                ++clause_start;
              }
              num_created+=max_loop;
              // printf("Clause start %d vs wnary.size %d\n", clause_start, wnary.size);
              if (clause_start == wnary.size) {
                clause_start = 0;
                ++qhead_start_nary;
              }
              if (num_created == NUM_WARPS) {
                break;
              }
            }
            // printf("created %d warps\n", num_created);
            // fill the rest with -1 if we run out of work
            for (unsigned int k = num_created; k < NUM_WARPS; ++k) {
              qhead_index[k] = -1;
            }
            if (qhead_index[0] == -1 && qhead_index[NUM_BIN_PROP_WARPS] == -1) {
              fixpoint = true;
            }

            for (unsigned int i = 0; i < NUM_WARPS; ++i) {
              printf("warp %d qhead %d clause %d\n", i, qhead_index[i], clause_index[i]);
            }
          }
        }  
      }
      __syncthreads();
      if (fixpoint) {
        break;
      }
      // do the actual propagation
      if (warp_id < NUM_BIN_PROP_WARPS) {
        if (qhead_index[warp_id] != -1) {
          //printf("BinProp threadIdx.x %d", threadIdx.x);
          printf("Call binary propagation with qhead_index %d\n", qhead_index[warp_id]);
          binary_propagation(qhead_index[warp_id], solver.device_trail, solver.device_trail_size, solver.assigns_vardata, solver.device_watchesBin, decision_level, solver.confl_device);
        }
      }
      else {
        if (qhead_index[warp_id] != -1) {
          printf("Call nary propagation with qhead_index %d and clause index %d\n", qhead_index[warp_id], clause_index[warp_id]);
          nary_propagation(qhead_index[warp_id], clause_index[warp_id], solver.device_trail, solver.device_trail_size, solver.assigns_vardata, solver.device_watches, solver.device_ca, decision_level, solver.confl_device);
        }
      }
    }
    valid_propagation(original_qhead, *solver.device_trail_size, solver.device_trail, solver.assigns_vardata, solver.confl_device);
    /// I think I might need to check double entries in the device trail, two clauses can propagate the same literal with different reasons
    /// could I possibly get cyclic reasons if I remove the wrong double entry?

    __syncthreads();
    qhead_start_binary = *solver.device_trail_size;
    qhead_start_nary = *solver.device_trail_size;
    if (threadIdx.x == 0 ) {
      if (*solver.confl_device != CRef_Undef)
      {
        if (solver.decision_level == 0)
        {
          printf("UNSAT\n");
          exhausted = true;
          // conflict on dl 0
          //return;
        }
        analyze(solver.device_seen, solver.device_decision_heap, solver.host_num_vars, *solver.confl_device, solver.device_trail, *solver.device_trail_size, solver.device_ca, solver.decision_level, solver.assigns_vardata, solver.device_conflict, solver.device_conflict_size, solver.device_backtrack_level);
        add_clause(solver.device_conflict, solver.device_conflict_size, &solver.device_ca, solver.device_ca_size, solver.device_ca_capacity, solver.device_watches, solver.device_watchesBin);
        *solver.device_conflict_size = 0;
        printf("Found conflict, need to BACKTRACK!!!!\n");
        backtrack(*solver.device_backtrack_level, solver.assigns_vardata, decision_level, solver.device_trail, solver.device_trail_size);
        uncheckedEnqueue(solver.device_conflict[0], CRef_Undef, solver.assigns_vardata, solver.device_trail, solver.device_trail_size, decision_level);       
      }
      else {
        //printf("No conflict, need to make a decision\n");
        Lit s = pick_branch_lit(solver.device_decision_heap, solver.assigns_vardata, solver.host_num_vars);
        printf("picked branch lit %d %d\n", var_device(s), sign_device(s));
        if (s != lit_Undef) {
          solver.decision_level++;
          uncheckedEnqueue(s, CRef_Undef, solver.assigns_vardata, solver.device_trail, solver.device_trail_size, decision_level);
        }
        else {
          // found a model
          exhausted = true;
          printf("Found a model\n");
        }
      }
    }
    fixpoint = false;

  } // outer while true
}


void propagate(MySolver &solver)
{
  static int num = 0;
  // std::cout << "propagate " << num << std::endl;
  ++num;
  cudaEvent_t start, stop;
  cudaEventCreate(&start);
  cudaEventCreate(&stop);

  //void *kernelArgs[] = {&solver};

  #define NUM_THREADS (32*12)
  #define NW (NUM_THREADS/32)

  //test_heap<100><<<1, 1>>>();

  cudaEventRecord(start);
  //cudaLaunchCooperativeKernel((void*)&propagate_control2<NW>, 2, NUM_THREADS, kernelArgs,  0/*solver.host_num_vars * sizeof(bool)*/, 0);
  propagate_control2<NW><<<1, NUM_THREADS>>>(solver);
  cudaEventRecord(stop);

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
