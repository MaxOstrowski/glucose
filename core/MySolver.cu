#include "core/MySolver.h"
#include "core/MyUtils.cuh"
#include "core/Solver.h"
#include "core/SolverTypes.h"
#include <algorithm>
#include <iostream>
#include <set>
#include <vector>

using namespace Glucose;

/// This create a ordered heap datastructure for cuda device code
/// It has a fixed size limit and does no checks on size
/// It has also support for increase/decrease key operations
/// It is a min heap

#include "core/SolverTypes.h"

using namespace Glucose;


__host__ int watch_index(Lit l) { return var(l) * 2 + int(sign(l)); }
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
// __device__ Solver::VarData mkVarData_device(CRef cr, int l)
// {
//   Solver::VarData d = {cr, l};
//   return d;
// }
__device__ int watch_index_device(Lit l) { return var_device(l) * 2 + int(sign_device(l)); }


// /// opposite of initialize kernel
// __global__ void dealloc_heap(MySolver solver) {
//   das ganze free funktioniert nicht weil auch die cref und watches pointer eventuell verschoben wurden und ich ihren aktuellen Wert garnicht weiss
//   deshalb mache ich free auf den alten werten resp. null_ptr
//   wenn die solver instanz global ist kann ich immer wieder drauf zugreifen und sie wird cudaGraphExecUpdateErrorNodeTypeChangedSolver instanz von mysolver global machen
//   sollten dann auch die Variablen __device__ sein?
//   for (unsigned int i = 0; i < solver.host_num_vars; ++i)
//   {
//     {
//       Lit lit = mkLit_device(i, false);
//       free(solver.device_watchesBin[watch_index_device(lit)].watches);      
//     }
//     {
//       Lit lit = mkLit_device(i, true);
//       free(solver.device_watchesBin[watch_index_device(lit)].watches);     
//     }
//   }

//   for (unsigned int i = 0; i < solver.host_num_vars; ++i)
//   {
//     {
//       Lit lit = mkLit_device(i, false);
//       free(solver.device_watches[watch_index_device(lit)].crefs);
//     }
//     {
//       Lit lit = mkLit_device(i, true);
//       free(solver.device_watches[watch_index_device(lit)].crefs);
//     }
//   }

//   free(solver.device_ca);
// }

__global__ void dynamicAllocKernel(void** devicePtr, size_t numElements) {
    if (threadIdx.x == 0) { // Let only one thread allocate
        *devicePtr = (void*)malloc(numElements * sizeof(char));
        if (*devicePtr == nullptr) {
          printf("Allocation failed\n");
        }
    }
    __syncthreads(); // Ensure allocation is done before proceeding
}

__device__ unsigned int device_decision_level;
__device__ CRef device_confl_ref;
__device__ Lit* device_conflict;
__device__ unsigned int device_conflict_size;
__device__ unsigned int device_backtrack_level;
__device__ Lit* device_trail;
__device__ unsigned int device_trail_size;
__device__ lbool_device* device_assign;
__device__ CRef* device_reasons;
__device__ int* device_levels;
__device__ binWatchVector* device_watches_bin;
__device__ watchVector* device_watches;
__device__ uint32_t* device_ca;
__device__ uint32_t device_ca_size;
__device__ uint32_t device_ca_capacity;
__device__ bool* device_seen;


binWatchVector *host_bin_watch = nullptr;
watchVector *host_watches = nullptr;
uint32_t* host_ca = nullptr;

// device pointers to host memory
__device__ binWatchVector *host_bin_watch_dp;
__device__ watchVector *host_watches_dp;
__device__ uint32_t* host_ca_dp;


__global__ void initializeKernel(unsigned int num_vars);

void create_solver(Solver &solver)
{
  size_t heap_size = static_cast<size_t>(3) * 1024 * 1024 * 1024; // 3G
  gpuErrchk(cudaDeviceSetLimit(cudaLimitMallocHeapSize, heap_size));
  size_t actual_size = 0;
  gpuErrchk(cudaDeviceGetLimit(&actual_size, cudaLimitMallocHeapSize));
  assert(actual_size >= heap_size);

  unsigned int num_vars = solver.nVars();
  unsigned int zero = 0;
  CRef cref_Undef = CRef_Undef;
  unsigned int temp_uint = 0;

  void* device_ptr = nullptr;

  temp_uint = solver.decisionLevel();
  gpuErrchk(cudaMemcpyToSymbol(device_decision_level, &temp_uint, sizeof(unsigned int)));
  gpuErrchk(cudaMemcpyToSymbol(device_backtrack_level, &zero, sizeof(unsigned int)));


  // create storage for conflict clause
  gpuErrchk(cudaMemcpyToSymbol(device_confl_ref, &cref_Undef, sizeof(CRef)));
  
  gpuErrchk(cudaMalloc((void **)&device_ptr, sizeof(Lit) * num_vars));
  gpuErrchk(cudaMemcpyToSymbol(device_conflict, &device_ptr, sizeof(Lit*)));
  
  gpuErrchk(cudaMemcpyToSymbol(device_conflict_size, &zero, sizeof(unsigned int)));

  // create storage for trail
  gpuErrchk(cudaMalloc((void **)&device_ptr, sizeof(Lit) * num_vars));
  gpuErrchk(cudaMemcpyToSymbol(device_trail, &device_ptr, sizeof(Lit*)));
  gpuErrchk(cudaMemcpy(device_ptr, &solver.trail[0], solver.trail.size()*sizeof(Lit), cudaMemcpyHostToDevice));
  temp_uint = solver.trail.size();
  gpuErrchk(cudaMemcpyToSymbol(device_trail_size, &temp_uint, sizeof(unsigned int)));

  // create storage for assigns and vardata
  // lbool *temp = new lbool[num_vars];
  // for (int i = 0; i < num_vars; i++)
  // {
  //   temp[i].assign = solver.assigns[i].value;
  //   temp[i].vardata = solver.vardata[i];
  // }
  gpuErrchk(cudaMalloc((void **)&device_ptr, sizeof(lbool_device) * num_vars));
  gpuErrchk(cudaMemcpy(device_ptr, &solver.assigns[0], sizeof(lbool_device) * num_vars, cudaMemcpyHostToDevice));
  gpuErrchk(cudaMemcpyToSymbol(device_assign, &device_ptr, sizeof(lbool_device*)));

  int* temp = new int [num_vars];
  for (int i = 0; i < num_vars; i++)
  {
    temp[i] = solver.vardata[i].level;
  }
  gpuErrchk(cudaMalloc((void **)&device_ptr, sizeof(int) * num_vars));
  gpuErrchk(cudaMemcpy(device_ptr, temp, sizeof(int) * num_vars, cudaMemcpyHostToDevice));
  gpuErrchk(cudaMemcpyToSymbol(device_levels, &device_ptr, sizeof(int*)));
  delete[] temp;

  CRef* temp_cref = new CRef[num_vars*2];
  for (int i = 0; i < num_vars*2; i++)
  {
    temp_cref[i] = solver.vardata[i].reason;
  }
  gpuErrchk(cudaMalloc((void **)&device_ptr, sizeof(CRef) * num_vars * 2));
  gpuErrchk(cudaMemcpy(device_ptr, temp_cref, sizeof(CRef) * num_vars * 2, cudaMemcpyHostToDevice));
  gpuErrchk(cudaMemcpyToSymbol(device_reasons, &device_ptr, sizeof(CRef*)));
  delete[] temp_cref;

  // copy binary watch lists
  //mysolver.hostBinWatch = new binWatchVector[num_vars * 2];
  gpuErrchk(cudaHostAlloc((void**)&host_bin_watch, num_vars * 2 * sizeof(binWatchVector), cudaHostAllocWriteCombined));
  
  for (unsigned int i = 0; i < num_vars; ++i)
  {
    {
      Lit lit = mkLit(i, false);
      unsigned int size = solver.watchesBin[lit].size();
      host_bin_watch[watch_index(lit)].size = size;
      host_bin_watch[watch_index(lit)].capacity = size;
      host_bin_watch[watch_index(lit)].watches = nullptr;
      if (size > 0) {
        gpuErrchk(cudaHostAlloc(&host_bin_watch[watch_index(lit)].watches, size * sizeof(Solver::Watcher), cudaHostAllocWriteCombined));
        gpuErrchk(cudaMemcpy(host_bin_watch[watch_index(lit)].watches, solver.watchesBin[lit].data, sizeof(Solver::Watcher) * size, cudaMemcpyHostToHost));
      }
    }
    {
      Lit lit = mkLit(i, true);
      unsigned int size = solver.watchesBin[lit].size();
      host_bin_watch[watch_index(lit)].size = size;
      host_bin_watch[watch_index(lit)].capacity = size;
      host_bin_watch[watch_index(lit)].watches = nullptr;
      if (size > 0) {
        gpuErrchk(cudaHostAlloc(&host_bin_watch[watch_index(lit)].watches, size * sizeof(Solver::Watcher), cudaHostAllocWriteCombined));
        gpuErrchk(cudaMemcpy(host_bin_watch[watch_index(lit)].watches, solver.watchesBin[lit].data, sizeof(Solver::Watcher) * size, cudaMemcpyHostToHost));
      }
    }
  }

  gpuErrchk(cudaMalloc((void **)&device_ptr, sizeof(binWatchVector) * num_vars * 2));
  gpuErrchk(cudaMemcpyToSymbol(device_watches_bin, &device_ptr, sizeof(binWatchVector*)));
  
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

  gpuErrchk(cudaHostAlloc((void**)&host_watches, num_vars * 2 * sizeof(watchVector), cudaHostAllocWriteCombined));

  for (unsigned int i = 0; i < num_vars; ++i)
  {
    {
      Lit lit = mkLit(i, false);
      unsigned int size = clause_refs[watch_index(lit)].size();
      host_watches[watch_index(lit)].size = size;
      host_watches[watch_index(lit)].capacity = size;
      host_watches[watch_index(lit)].crefs = nullptr;
      if (size > 0) {
        gpuErrchk(cudaHostAlloc(&host_watches[watch_index(lit)].crefs, size * sizeof(CRef), cudaHostAllocWriteCombined));
        gpuErrchk(cudaMemcpy(host_watches[watch_index(lit)].crefs, clause_refs[watch_index(lit)].data(), sizeof(CRef) * size, cudaMemcpyHostToHost));
      }
    }
    {
      Lit lit = mkLit(i, true);
      unsigned int size = clause_refs[watch_index(lit)].size();
      host_watches[watch_index(lit)].size = size;
      host_watches[watch_index(lit)].capacity = size;
      host_watches[watch_index(lit)].crefs = nullptr;
      if (size > 0) {
        gpuErrchk(cudaHostAlloc(&host_watches[watch_index(lit)].crefs, size * sizeof(CRef), cudaHostAllocWriteCombined));
        gpuErrchk(cudaMemcpy(host_watches[watch_index(lit)].crefs, clause_refs[watch_index(lit)].data(), sizeof(CRef) * size, cudaMemcpyHostToHost));
      }
    }
  }

  gpuErrchk(cudaMalloc((void **)&device_ptr, sizeof(watchVector) * num_vars * 2));
  gpuErrchk(cudaMemcpyToSymbol(device_watches, &device_ptr, sizeof(watchVector*)));


  // copy clause database
  unsigned int ca_size = solver.ca.size();
  host_ca = (uint32_t*)solver.ca.lea(0);
  gpuErrchk(cudaHostRegister(host_ca, sizeof(uint32_t) * ca_size, cudaHostRegisterDefault));

  // create device_ca_size and device_ca_capacity
  gpuErrchk(cudaMemcpyToSymbol(device_ca_size, &ca_size, sizeof(uint32_t)));
  gpuErrchk(cudaMemcpyToSymbol(device_ca_capacity, &ca_size, sizeof(uint32_t)));

  // create device_seen and initialize with false


  gpuErrchk(cudaMalloc((void **)&device_ptr, sizeof(bool) * num_vars * 2));
  gpuErrchk(cudaMemset(device_ptr, 0, sizeof(bool) * num_vars * 2));
  gpuErrchk(cudaMemcpyToSymbol(device_seen, &device_ptr, sizeof(bool*)));


  gpuErrchk(cudaHostGetDevicePointer(&device_ptr, host_bin_watch, 0));
  gpuErrchk(cudaMemcpyToSymbol(host_bin_watch_dp, &device_ptr, sizeof(binWatchVector*)));
  gpuErrchk(cudaHostGetDevicePointer(&device_ptr, host_watches, 0));
  gpuErrchk(cudaMemcpyToSymbol(host_watches_dp, &device_ptr, sizeof(watchVector*)));
  gpuErrchk(cudaHostGetDevicePointer(&device_ptr, host_ca, 0));
  gpuErrchk(cudaMemcpyToSymbol(host_ca_dp, &device_ptr, sizeof(uint32_t*)));
  

  initializeKernel<<<1, 1>>>(num_vars);
  gpuErrchk(cudaDeviceSynchronize());
}


__global__ void initializeKernel(unsigned int num_vars) {
  // copy hostBinWatch to device
  for (unsigned int i = 0; i < num_vars; ++i)
  {
    {
      Lit lit = mkLit_device(i, false);
      device_watches_bin[watch_index_device(lit)].size = host_bin_watch_dp[watch_index_device(lit)].size;
      device_watches_bin[watch_index_device(lit)].capacity = host_bin_watch_dp[watch_index_device(lit)].capacity;
      device_watches_bin[watch_index_device(lit)].watches = nullptr;
      if (host_bin_watch_dp[watch_index_device(lit)].size > 0) {
        device_watches_bin[watch_index_device(lit)].watches = (Solver::Watcher*)malloc(sizeof(Solver::Watcher) * host_bin_watch_dp[watch_index_device(lit)].size);
        memcpy(device_watches_bin[watch_index_device(lit)].watches, host_bin_watch_dp[watch_index_device(lit)].watches, sizeof(Solver::Watcher) * host_bin_watch_dp[watch_index_device(lit)].size);
      }
    }
    {
      Lit lit = mkLit_device(i, true);
      device_watches_bin[watch_index_device(lit)].size = host_bin_watch_dp[watch_index_device(lit)].size;
      device_watches_bin[watch_index_device(lit)].capacity = host_bin_watch_dp[watch_index_device(lit)].capacity;
      device_watches_bin[watch_index_device(lit)].watches = nullptr;
      if (host_bin_watch_dp[watch_index_device(lit)].size > 0) {
        device_watches_bin[watch_index_device(lit)].watches = (Solver::Watcher*)malloc(sizeof(Solver::Watcher) * host_bin_watch_dp[watch_index_device(lit)].size);
        memcpy(device_watches_bin[watch_index_device(lit)].watches, host_bin_watch_dp[watch_index_device(lit)].watches, sizeof(Solver::Watcher) * host_bin_watch_dp[watch_index_device(lit)].size);
      }
    }
  }

  // copy hostWatches to device
  for (unsigned int i = 0; i < num_vars; ++i)
  {
    {
      Lit lit = mkLit_device(i, false);
      device_watches[watch_index_device(lit)].size = host_watches_dp[watch_index_device(lit)].size;
      device_watches[watch_index_device(lit)].capacity = host_watches_dp[watch_index_device(lit)].capacity;
      device_watches[watch_index_device(lit)].crefs = nullptr;
      if (host_watches_dp[watch_index_device(lit)].size > 0) {
        device_watches[watch_index_device(lit)].crefs = (CRef*)malloc(sizeof(CRef) * host_watches_dp[watch_index_device(lit)].size);
        memcpy(device_watches[watch_index_device(lit)].crefs, host_watches_dp[watch_index_device(lit)].crefs, sizeof(CRef) * host_watches_dp[watch_index_device(lit)].size);
      }
    }
    {
      Lit lit = mkLit_device(i, true);
      device_watches[watch_index_device(lit)].size = host_watches_dp[watch_index_device(lit)].size;
      device_watches[watch_index_device(lit)].capacity = host_watches_dp[watch_index_device(lit)].capacity;
      device_watches[watch_index_device(lit)].crefs = nullptr;
      if (host_watches_dp[watch_index_device(lit)].size > 0) {
        device_watches[watch_index_device(lit)].crefs = (CRef*)malloc(sizeof(CRef) * host_watches_dp[watch_index_device(lit)].size);
        memcpy(device_watches[watch_index_device(lit)].crefs, host_watches_dp[watch_index_device(lit)].crefs, sizeof(CRef) * host_watches_dp[watch_index_device(lit)].size);
      }
    }
  }

  // copy clause database
  device_ca = (uint32_t*)malloc(sizeof(uint32_t) * device_ca_size);
  for (size_t i = 0; i < device_ca_size; i++) {
    device_ca[i] = host_ca_dp[i];
    //printf("host: %d\n", host_ca_dp[i]);
    //printf("device: %d\n", device_ca[i]);
  }
  //memcpy(device_ca, host_ca_dp, sizeof(uint32_t) * device_ca_size);
}


/// @brief add literal to new trail and assign/vardata
__device__ void uncheckedEnqueue(Lit p, CRef cref)
{
  /// atomic increase trailsize
  int trail_p = atomicAdd_block(&device_trail_size, 1);
  printf(" Thread %d propagate %d %d with reason %d on level %d in trail position %d\n", threadIdx.x, var_device(p), sign_device(p), cref, device_decision_level, trail_p);
  device_trail[trail_p] = p;
  device_assign[var_device(p)] = create_bool_device_from_bool(!sign_device(p));
  device_levels[var_device(p)] = device_decision_level;
  device_reasons[watch_index_device(p)] = cref;
}

__device__ Lit pick_branch_lit(CudaOrderedHeap* heap, unsigned int num_vars) {
  for (Var i = 0; i < num_vars; ++i) {
    if (device_assign[i] == l_Undef_device) {
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
__device__ lbool_device value_device(Lit p)
{
  // printf("value for %d %d\n", var_device(p), sign_device(p));
  // printf("value assign %d\n", assigns[var_device(p)].assign);
  // printf("value sign %d\n", sign_device(p));
  // printf("value %d\n", assigns[var_device(p)].assign ^ (lbool_device)(sign_device(p)));
  // printf("value %d\n", create_bool_device_from_uc((lbool_device)assigns[var_device(p)].assign ^ (lbool_device)(sign_device(p))));
  return create_bool_device_from_uc((lbool_device)(device_assign[var_device(p)] ^ (lbool_device)(sign_device(p))));
}

__device__ CRef reason_device(Lit x) { return device_reasons[watch_index_device(x)]; }
__device__ int level_device(Var x) { return device_levels[x]; }

void destroy_solver()
{
    gpuErrchk(cudaDeviceReset());
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
__device__ void analyze(unsigned int num_vars) {
    int pathC = 0;
    Lit lit_Undef;
    lit_Undef.x = -2;
    Lit p = lit_Undef;
    device_conflict_size = 0;
    printf("Analyze with trail size %d\n", device_trail_size);
    for (int i = 0; i < device_trail_size; i++) {
        printf("trail %d %d\n", var_device(device_trail[i]), sign_device(device_trail[i]));
    }
    printf("ConflictCRef: %d\n", device_confl_ref);
    
    

    /// create shared memory for seen variables in size of variables
    /// initialize correctly with nvars*sizeof(bool)*2
    for (unsigned int i = 0; i < num_vars*2; ++i) {
      //printf("Accessing shared memory\n");
      device_seen[i] = false;
    }
    //printf("set all seen to false\n");
    // in the current decision level which is much smaller, but then indexing gets much harder

    // Generate conflict clause:
    //
    device_conflict_size +=1;  // (leave room for the asserting literal)
    unsigned int index = device_trail_size - 1;
    do {
        //printf("index %d and pathC %d\n", index, pathC);
        //printf("ConflictCRef: %d\n", confl);
        assert(device_confl_ref != CRef_Undef); // (otherwise should be UIP)
        const Clause &c = *reinterpret_cast<Clause *>(&device_ca[reinterpret_cast<uint32_t>(device_confl_ref)]);
        printf("c analysiere %d\n", device_confl_ref);
        for (int i = 0; i < c.size(); i++) {
           printf("c %d %d\n", var_device(c[i]), sign_device(c[i]));
        }

        for(int j = 0; j < c.size(); j++) {
            Lit q = c[j];
            if (p == q)
                continue;

            
            Lit neg_q = mkLit_device(var_device(q), !sign_device(q));
            printf("check for seen %d %d\n", var_device(neg_q), sign_device(neg_q));
            if(!device_seen[watch_index_device(neg_q)]) {
                //decision_heap->increaseKey(var_device(q));
                printf("not yet seen neq_q %d %d\n", var_device(neg_q), sign_device(neg_q));
                if(level_device(var_device(q)) == 0) {
                } else { // Here, the old case
                    device_seen[watch_index_device(neg_q)] = true;
                    printf("compare level %d >= %d\n", level_device(var_device(q)), device_decision_level);
                    if(level_device(var_device(q)) >= device_decision_level) {
                        printf("increment pathC\n");
                        pathC++;
                    } else {
                        printf("accessing device_conclift[%d] and writing %d %d\n", device_conflict_size, var_device(q), sign_device(q));
                        device_conflict[device_conflict_size++] = q;
                    }
                }
            }
        }
        printf("end of loop, trailing down with index %d\n", index);

        // Select next clause to look at:
        //while (!device_seen[var_device(device_trail[index--])]);
        // select next clause to look at:
        while (true) {
          Lit lit = device_trail[index--];
          // Lit neg_lit = mkLit_device(var_device(l), !sign_device(l));
          printf("check seen %d %d\n", var_device(lit), sign_device(lit));
          if (device_seen[watch_index_device(lit)]) {
            break;
          }
        }
        printf("trailed down to %d\n", index);
        p = device_trail[index + 1];
        printf("next p %d %d\n", var_device(p), sign_device(p));
        //stats[sumRes]++;
        device_confl_ref = reason_device(p);
        printf("next confl %d\n", device_confl_ref);
        device_seen[watch_index_device(mkLit_device(var_device(p), !sign_device(p)))] = false;
        printf("set seen %d %d to false\n", var_device(p), !sign_device(p));
        pathC--;
        printf("decrement pathC to %d\n", pathC);

    } while(pathC > 0);
    
    device_conflict[0] = ~p;
    
    // Find correct backtrack level:
    //
    if(device_conflict_size == 1)
        device_backtrack_level = 0;
    else {
        int max_i = 1;
        // Find the first literal assigned at the next-highest level:
        for(int i = 2; i < device_conflict_size; i++)
            if(level_device(var_device(device_conflict[i])) > level_device(var_device(device_conflict[max_i])))
                max_i = i;
        // Swap-in this literal at index 1:
        Lit p = device_conflict[max_i];
        device_conflict[max_i] = device_conflict[1];
        device_conflict[1] = p;
        device_backtrack_level = level_device(var_device(p));
    }
    device_confl_ref = CRef_Undef;
}

__device__ void binary_propagation(unsigned int trail_p)
{
  Lit p = device_trail[trail_p];
  auto &wbin = device_watches_bin[watch_index_device(p)];
  //if (threadIdx.x % warpSize == 0) printf("Bin Prop for lit index %d has %d watches\n", trail_p, wbin.size);
  for (int k = threadIdx.x%warpSize; k < wbin.size; k+=warpSize)
  {
    Lit imp = wbin.watches[k].blocker;
    /// be careful, there was a hidden == operator that didnt compare for equality
    if (compare_lbool_device(value_device(imp), l_False_device))
    {
      // printf("binary prop conflict\n");
      device_confl_ref = wbin.watches[k].cref;
      printf("binary prop conflict %d\n", device_confl_ref);
    }
    if (compare_lbool_device(value_device(imp), l_Undef_device))
    {
      // printf("Thread %d found a binary implication for watch %d\n", threadIdx.x, k);
      uncheckedEnqueue(imp, wbin.watches[k].cref);
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

__device__ void nary_propagation(unsigned int trail_p, unsigned int clause_index) {
  Lit lit_Undef;
  lit_Undef.x = -2;

  Lit p = device_trail[trail_p];
  watchVector &wnary = device_watches[watch_index_device(p)];
  printf("Accessing wnary %d with var/sign %d %d\n", watch_index_device(p), var_device(p), sign_device(p));
  printf("Accessing %d of wnary Size %d\n", clause_index, wnary.size);
  assert(clause_index < wnary.size);
  CRef cref = wnary.crefs[clause_index];
  const Clause &clause = *reinterpret_cast<Clause *>(&device_ca[reinterpret_cast<uint32_t>(cref)]);
   
  unsigned int undef_counter_local = 0;
  Lit l = lit_Undef;
  for (int i = threadIdx.x%warpSize; i < clause.size(); i+=warpSize) {
    if (compare_lbool_device(value_device(clause[i]), l_True_device)) {
      // printf("Thread %d found a true literal in clause %d\n", threadIdx.x, clause_index);
      undef_counter_local += 2;
    }
    else if (compare_lbool_device(value_device(clause[i]), l_Undef_device)) {
      // printf("Thread %d found an undef literal in clause %d\n", threadIdx.x, clause_index);
      ++undef_counter_local;
      l = clause[i];
    }
  }
    
  undef_counter_local = warpReduceSum(undef_counter_local); // i can make this shorter by using clause.size to only add up the necessary values
  undef_counter_local = __shfl_sync(0xffffffff, undef_counter_local, 0);

  // if (threadIdx.x % warpSize == 0) printf("Thread %d has %d undef literals in clause %d\n", threadIdx.x, undef_counter_local, clause_index);

  if (undef_counter_local == 1 && l != lit_Undef) {
    uncheckedEnqueue(l, cref);
  }
  if (threadIdx.x%warpSize == 0 && undef_counter_local == 0) {
    device_confl_ref = cref;
    printf("nary prop conflict %d\n", device_confl_ref);
  }
}

//compare with original code propagation using git stash

__device__ void valid_propagation(unsigned int trail_p) {
  // unsigned int tid = threadIdx.x;
  // unsigned int bdim = blockDim.x;
  for (unsigned int lit_access=trail_p+threadIdx.x; lit_access < device_trail_size; lit_access+=blockDim.x) {
    Lit p = device_trail[lit_access];
    if (compare_lbool_device(value_device(p), l_False_device)) {
      device_confl_ref = reason_device(p);
      assert(device_confl_ref != CRef_Undef);
      printf("valid propagation just set a conflict because of literal %d %d, which is %d\n", var_device(p), sign_device(p), device_confl_ref);
      return;
    }
  }
}


// void compare(Solver& s, CRef confl)
// {
//   copyConflictToHost(mysolver);
//   copyTrailToHost(mysolver);
//   /// either both are in conflict or both are not in conflict
//   if (*mysolver.confl_host == CRef_Undef && confl == CRef_Undef)
//   {
//     // both trails are the same (set comparison)
//     // print host trail and trail
//     // for (int i = 0; i < solver.host_trail_size; i++)
//     // {
//     //   std::cout << "host trail " << i << " " << toInt(solver.host_trail[i]) << std::endl;
//     // }
//     // for (int i = 0; i < s.trail.size(); i++)
//     // {
//     //   std::cout << "trail " << i << " " << toInt(s.trail[i]) << std::endl;
//     // }
//     std::set<Lit> myset(mysolver.host_trail, mysolver.host_trail + mysolver.host_trail_size);
//     std::set<Lit> theirset(s.trail.data, s.trail.data + s.trail.size());
    
//     // write relation between the two sets
//     // std::cout << "my trail size " << mysolver.host_trail_size << " and their trail size " << s.trail.size() << std::endl;
//     // std::cout << "sizes: " << myset.size() << "/" << theirset.size() << std::endl;
//     // if (std::includes(theirset.begin(), theirset.end(), myset.begin(), myset.end()))
//     // {
//     //   std::cout << "my set is a subset of theirs" << std::endl;
//     //   //return;
//     // }
//     // // if theirset is a subset of myset
//     // if (std::includes(myset.begin(), myset.end(), theirset.begin(), theirset.end()))
//     // {
//     //   std::cout << "theirset is a subset of myset" << std::endl;
//     //   //return;
//     // }
//     // if (myset != theirset)
//     //   std::cout << "trails complte different" << std::endl;

//     // std::cout << "my trail: ";
//     // for (auto it = myset.begin(); it != myset.end(); ++it)
//     // {
//     //   std::cout << "( " << var(*it) << " " << sign(*it) << " ) ";
//     // }
//     // std::cout << std::endl;
//     // std::cout << "their trail: ";
//     // for (auto it = theirset.begin(); it != theirset.end(); ++it)
//     // {
//     //   std::cout << "( " << var(*it) << " " << sign(*it) << " ) ";
//     // }
//     // std::cout << std::endl;
    

//     assert (myset == theirset);
//     return;
//   }

//   if (*mysolver.confl_host == confl) {
//     // compare analyzed conflicts
//     //std::cout << "conflict is the same" << std::endl;
//   } else {
//     //std::cout << "different conflict detected " << *solver.confl_host << " " << confl << std::endl;
//   }

//   // if(confl != CRef_Undef) { // they have a conflict
//   //   // std::cout << "they have conflict, fine" << std::endl;
//   //   return;
//   // }
//   assert (*mysolver.confl_host != CRef_Undef && confl != CRef_Undef);
//   //std::cout << "PROBLEM: I have a conflict, they not" << std::endl;
// }

/// method adds a clause to the clause database
/// might need to reallocate space in ca
__device__ CRef add_clause() {
  if (device_ca_size + device_conflict_size > device_ca_capacity) {
    //printf("need to reallocate clause database\n");
    unsigned int new_capacity = (int)(device_ca_capacity * 1.5f); // minimum growth should be clause size!
    uint32_t* new_ca = reinterpret_cast<uint32_t*>(malloc(sizeof(uint32_t) * new_capacity));
    //printf("new ca pointer %p\n", new_ca);
    for (unsigned int i = 0; i < device_ca_size; ++i) {
      //printf("old value %d\n", device_ca[i]);
      new_ca[i] = device_ca[i];
      //printf("new value %d\n", new_ca[i]);
    }
    free(device_ca); 
    device_ca = new_ca;
    device_ca_capacity = new_capacity;
  }
  //printf("new ca 0: %d\n", device_ca[0]);
  //printf("add clause with size %d\n", *conflict_size);
  Clause& c = *((Clause*)&((device_ca)[device_ca_size]));
  c.header.mark      = 0;
  c.header.learnt    = 1;
  c.header.extra_size = 0;
  c.header.reloced   = 0;
  c.header.size      = device_conflict_size;
  c.header.lbd = 0;
  c.header.canbedel = 1;
  c.header.exported = 0; 
  c.header.oneWatched = 0;
  c.header.simplified = 0;
  c.header.seen = 0;
  
  for (int i = 0; i < c.header.size; i++) 
    c.data[i].lit = device_conflict[i];

  // add watches and maybe increase watch size 
  if (device_conflict_size == 2) {
    Lit p = device_conflict[0];
    Lit q = device_conflict[1];
    device_watches_bin[watch_index_device(mkLit_device(var_device(p), !sign_device(p)))].push(device_ca_size, q);
    device_watches_bin[watch_index_device(mkLit_device(var_device(q), !sign_device(q)))].push(device_ca_size, p);
  }
  else {
    for (int i = 0; i < c.header.size; i++) {
      device_watches[watch_index_device(mkLit_device(var_device(c.data[i].lit), !sign_device(c.data[i].lit)))].push(device_ca_size);
    }
  }
  // print newly added clause
  for (int i = 0; i < c.header.size; i++) {
    printf("new clause %d %d\n", var_device(c.data[i].lit), sign_device(c.data[i].lit));
  }

  device_confl_ref = CRef_Undef;

  CRef temp = device_ca_size;

  device_ca_size += sizeof(Clause)/sizeof(uint32_t) + device_conflict_size;
  return temp;
}


__device__ void backtrack() {
  while (device_trail_size > 0 && level_device(var_device(device_trail[device_trail_size-1])) > device_backtrack_level) {
    device_assign[var_device(device_trail[device_trail_size-1])] = l_Undef_device;
    --device_trail_size;
  }
  device_decision_level = device_backtrack_level;
  printf("Backtrack to level %d\n", device_decision_level);
  printf("New trail:\n");
  for (int i = 0; i < device_trail_size; i++) {
    printf("trail %d %d\n", var_device(device_trail[i]), sign_device(device_trail[i]));
  }
}


template <unsigned char NUM_WARPS>
__global__ void gpu_search(unsigned int num_vars) {

  unsigned char warp_id = threadIdx.x / warpSize;
  const unsigned char NUM_BIN_PROP_WARPS = 2;
  unsigned int original_qhead = 0;
  //if (threadIdx.x == 0) { printf("Start propagation with qhead %d and trail size %d\n", original_qhead, *solver.device_trail_size); }

  __shared__ unsigned int decision_level;
  decision_level = device_decision_level;
  __shared__ int qhead_index[NUM_WARPS];
  __shared__ int clause_index[NUM_WARPS]; // can safe one for thread 0, as bin prop does not need it
  __shared__ bool fixpoint;
  fixpoint = false;
  __shared__ bool exhausted;
  exhausted = false;

  if (threadIdx.x == 0 && original_qhead == device_trail_size) {
    Lit s = pick_branch_lit(nullptr, num_vars);
    printf("picked branch lit %d %d\n", var_device(s), sign_device(s));
    if (s != lit_Undef) {
      device_decision_level++;
      uncheckedEnqueue(s, CRef_Undef);
    }
  }
  __syncthreads();

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
        printf("Conflict ref before propagation %d\n", device_confl_ref);
        /// thread 0 spreads the work to all warps 1..NUM_WARPS
        /// warp 0 is supposed to do binary propagation
        if (threadIdx.x == 0) {
          if (device_confl_ref != CRef_Undef) {
            fixpoint = true;
          }
          else {
            // assign work for binary propagation
            for (unsigned int i = 0; i < NUM_BIN_PROP_WARPS; ++i) {
              if (qhead_start_binary < device_trail_size) {
                qhead_index[i] = qhead_start_binary;
                ++qhead_start_binary;
              }
              else {
                qhead_index[i] = -1;
              }
            }
            // assign work for nary propagation
            unsigned char num_created = NUM_BIN_PROP_WARPS;
            while (qhead_start_nary < device_trail_size) {
              Lit p = device_trail[qhead_start_nary];
              watchVector &wnary = device_watches[watch_index_device(p)];
              printf("Accessing wnary %d with var/sign %d %d\n", watch_index_device(p), var_device(p), sign_device(p));
              unsigned int max_loop = min((unsigned int)(NUM_WARPS-num_created), (unsigned int)(wnary.size - clause_start));
              printf(" for qstart %d max loop %d and wnary.size %d and num_created before %d and clause start %d\n", qhead_start_nary, max_loop, wnary.size, num_created, clause_start);
              for (unsigned int k = 0; k < max_loop; ++k) {
                printf("Accessing %d of wnary Size %d\n", clause_start, wnary.size);
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
          //printf("Call binary propagation with qhead_index %d\n", qhead_index[warp_id]);
          binary_propagation(qhead_index[warp_id]);
        }
      }
      else {
        if (qhead_index[warp_id] != -1) {
          //printf("Call nary propagation with qhead_index %d and clause index %d\n", qhead_index[warp_id], clause_index[warp_id]);
          nary_propagation(qhead_index[warp_id], clause_index[warp_id]);
        }
      }
    }
    valid_propagation(original_qhead);
    /// I think I might need to check double entries in the device trail, two clauses can propagate the same literal with different reasons
    /// could I possibly get cyclic reasons if I remove the wrong double entry?

    __syncthreads();
    if (threadIdx.x == 0 ) {
      printf("Trail after propagation\n");
      for (int i = 0; i < device_trail_size; i++) {
        printf("trail %d %d\n", var_device(device_trail[i]), sign_device(device_trail[i]));
      }
      if (device_confl_ref != CRef_Undef)
      {
        printf("found conflict in thread %d, need to analyze it\n", threadIdx.x);
        if (device_decision_level == 0)
        {
          printf("UNSAT\n");
          exhausted = true;
          // conflict on dl 0
          //return;
        }
        analyze(num_vars);
        CRef new_clause = add_clause();
        device_conflict_size = 0;
        device_confl_ref = CRef_Undef;
        printf("Found conflict, need to BACKTRACK!!!!\n");
        backtrack();
        uncheckedEnqueue(device_conflict[0], new_clause);   
        printf("conflict reference after backtracking %d\n", device_confl_ref);    
      }
      else {
        printf("No conflict, need to make a decision\n");
        Lit s = pick_branch_lit(nullptr, num_vars);
        printf("picked branch lit %d %d\n", var_device(s), sign_device(s));
        if (s != lit_Undef) {
          device_decision_level++;
          uncheckedEnqueue(s, CRef_Undef);
        }
        else {
          // found a model
          exhausted = true;
          printf("Found a model\n");
        }
      }
    }
    fixpoint = false;
    __syncthreads();
    qhead_start_binary = device_trail_size-1;
    qhead_start_nary = device_trail_size-1;
    clause_start = 0;
    __syncthreads();

  } // outer while true
}


void search(unsigned int num_vars)
{
  static int num = 0;
  // std::cout << "propagate " << num << std::endl;
  ++num;
  cudaEvent_t start, stop;
  cudaEventCreate(&start);
  cudaEventCreate(&stop);

  //void *kernelArgs[] = {&solver};

  #define NUM_THREADS (32*8)
  #define NW (NUM_THREADS/32)

  //test_heap<100><<<1, 1>>>();

  cudaEventRecord(start);
  //cudaLaunchCooperativeKernel((void*)&propagate_control2<NW>, 2, NUM_THREADS, kernelArgs,  0/*solver.host_num_vars * sizeof(bool)*/, 0);
  gpu_search<NW><<<1, NUM_THREADS>>>(num_vars);
  cudaEventRecord(stop);

  gpuErrchk( cudaPeekAtLastError() );
  gpuErrchk( cudaEventSynchronize(stop) );
  //gpuErrchk(cudaDeviceSynchronize());
  float milliseconds = 0;
  cudaEventElapsedTime(&milliseconds, start, stop);
  std::cout << "search time: " << int(milliseconds*1000) << std::endl;

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
