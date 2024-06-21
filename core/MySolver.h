#pragma once

#include "core/MyUtils.cuh"
#include "core/Solver.h"
#include "core/SolverTypes.h"


using namespace Glucose;


class CudaOrderedHeap {
public:
    Var* heap; // index to value
    int* indices; // value to index into heap
    int size;
public:
    // host function to initialize the heap
    void init(unsigned int num_vars) {
        // WHY DO YOU SEGFAULT
        gpuErrchk(cudaMalloc((void **)&heap, sizeof(Var) * num_vars));
        //gpuErrchk(cudaMemset(heap, var_Undef, sizeof(Var) * num_vars));
        gpuErrchk(cudaMalloc((void **)&indices, sizeof(int) * num_vars));
        gpuErrchk(cudaMemset(indices, -1, sizeof(int) * num_vars));
        size = 0;
    }

    void destroy() {
        gpuErrchk(cudaFree(heap));
        gpuErrchk(cudaFree(indices));
    }

    __device__ void insert(Var value) {
        int i = size++;
        heap[i] = value;
        indices[value] = i;
        while (i > 0) {
            int parent = (i - 1) / 2;
            if (heap[parent] <= heap[i]) {
                break;
            }
            swap(i, parent);
            i = parent;
        }
    }

    __device__ Var pop() {
        printf("pop heap address %p and size %d\n", heap, size);
        if (size == 0)
            return var_Undef;
        Var result = heap[0];
        indices[result] = -1;
        heap[0] = heap[--size];
        indices[heap[0]] = 0;
        int i = 0;
        while (true) {
            int left = 2 * i + 1;
            int right = 2 * i + 2;
            if (left >= size) {
                break;
            }
            int j = left;
            if (right < size && heap[right] < heap[left]) {
                j = right;
            }
            if (heap[i] <= heap[j]) {
                break;
            }
            swap(i, j);
            i = j;
        }
        return result;
    }

    __device__ Var top() {
        return heap[0];
    }

    __device__ void decreaseKey(Var value) {
        int i = indices[value];
        while (i > 0) {
            int parent = (i - 1) / 2;
            if (heap[parent] <= heap[i]) {
                break;
            }
            swap(i, parent);
            i = parent;
        }
    }

    __device__ void increaseKey(Var value) {
        int i = indices[value];
        if (i == -1) {
            insert(value);
            // i have no clue if I should increase or not
        }
        while (true) {
            int left = 2 * i + 1;
            int right = 2 * i + 2;
            if (left >= size) {
                break;
            }
            int j = left;
            if (right < size && heap[right] < heap[left]) {
                j = right;
            }
            if (heap[i] <= heap[j]) {
                break;
            }
            swap(i, j);
            i = j;
        }
    }

    __device__ bool empty() {
        return size == 0;
    }

    __device__ int getSize() {
        return size;
    }

    // for debugging
    __device__ unsigned int get(Var i) {
        return heap[i];
    }

private:
    __device__ void swap(int i, int j) {
        Var temp = heap[i];
        heap[i] = heap[j];
        heap[j] = temp;
        indices[heap[i]] = i;
        indices[heap[j]] = j;
    }
};

typedef unsigned char lbool_device;

struct __attribute__((aligned(16))) AssignVardata {
    lbool_device assign;
    Solver::VarData vardata;
  };

struct binWatchVector {
  unsigned int size;
  unsigned int capacity;
  Solver::Watcher* watches;
  __device__ void push(CRef cref, Lit blocker) {
    if (size == capacity) {
      capacity *= 2;
      Solver::Watcher* new_watches = new Solver::Watcher[capacity];
      for (int i = 0; i < size; i++) {
        new_watches[i] = watches[i];
      }
      delete[] watches;
      watches = new_watches;
    }
    watches[size++] = Solver::Watcher(cref, blocker);
  }    

};

struct watchVector {
  unsigned int size;
  unsigned int capacity;
  CRef* crefs;
  __device__ void push(CRef cref) {
    if (size == capacity) {
      capacity *= 2;
      CRef* new_crefs = new CRef[capacity];
      for (int i = 0; i < size; i++) {
        new_crefs[i] = crefs[i];
      }
      delete[] crefs;
      crefs = new_crefs;
    }
    crefs[size++] = cref;
  }    
};

struct MySolver {
  unsigned int host_num_vars;
  unsigned int decision_level;

  Lit* device_trail;
  unsigned int* device_trail_size;
  Lit* host_trail;
  unsigned int host_trail_size;
  unsigned int* qhead;

  AssignVardata* assigns_vardata;

  unsigned int old_trail_size;
  CRef* confl_host;
  CRef* confl_device;

  binWatchVector* hostBinWatch;
  binWatchVector* device_watchesBin;
  watchVector* hostWatches;
  watchVector* device_watches;
  unsigned int max_watch_length;
  uint32_t* device_ca; // storage for all clauses
  unsigned int* device_ca_size; // pointer to next free index into device_ca
  unsigned int* device_ca_capacity; // size of reverved memory for device_ca
  /// storage for analyzing conflicts
  Lit* device_conflict;
  unsigned int* device_conflict_size;
  Lit* host_conflict;
  unsigned int host_conflict_size;
  unsigned int* device_backtrack_level;
  unsigned int host_backtrack_level;
  bool* device_seen;
  CudaOrderedHeap* device_decision_heap;
  CudaOrderedHeap* host_decision_heap;

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