#pragma once
#include <cassert>
#include <iostream>
#include <cuda_runtime.h>



#define gpuErrchk(ans)                                                         \
  { gpuAssert((ans), __FILE__, __LINE__); }
  
__inline__ void gpuAssert(cudaError_t code, const char *file, int line) {
  if (code != cudaSuccess) {
    printf("GPUassert: %s %s %d\n", cudaGetErrorString(code), file, line);
    std::cout << std::endl;
  }
}




// template<typename T>
// struct FixedSizeVector {
//     T* array = nullptr;
//     int current_size;
//     const int maximum_size;

//     FixedSizeVector(int maximum_size) : current_size(0), maximum_size(maximum_size)  {gpuErrchk(cudaMallocManaged(&array, maximum_size));}
//     // Constructor copying array of fixed size
//     FixedSizeVector(int maximum_size, const T* array, int size) : current_size(size), maximum_size(maximum_size) {
//         gpuErrchk(cudaMalloc&array, maximum_size));
//         for (int i = 0; i < size; i++) {
//             this->array[i] = array[i];
//         }
//     }

//     void push_back(const T& element) {
//         assert(current_size < maximum_size);
//         /// This has to be done atomically
//         array[current_size] = element;
//         current_size++;
        
//     }

//     T& operator[](int index) {
//         assert (index < maximum_size);
//         return array[index];
//     }
//     const T& operator[](int index) const {
//         assert (index < current_size);
//         return array[index];
//     }

//     int size() const {
//         return current_size;
//     }

//     int capacity() const {
//         return maximum_size;
//     }

//     void free() {
//         gpuErrchk(cudaFree(array));
//     }
// };


// template<typename T>
// struct VariableSizedVector {
//     T* array = nullptr;
//     int current_size;
//     int maximum_size;

//     VariableSizedVector() : current_size(0), maximum_size(256)  {gpuErrchk(cudaMallocManaged(&array, 256));}
//     VariableSizedVector(int maximum_size) : current_size(0), maximum_size(maximum_size) { gpuErrchk(cudaMallocManaged(&array, maximum_size)); assert (maximum_size > 0); }
//     // Constructor copying array of fixed size
//     VariableSizedVector(int maximum_size, const T* array, int size) : current_size(size), maximum_size(maximum_size) {
//         gpuErrchk(cudaMallocManaged(&array, maximum_size));
//         assert (maximum_size > 0);
//         for (int i = 0; i < size; i++) {
//             this->array[i] = array[i];
//         }
//     }

//     ~VariableSizedVector() {
//         delete[] array;
//     }

//     void push_back(const T& element) {
//         if (current_size == maximum_size) {
//             resize(maximum_size * 2);
//         }
//         array[current_size] = element;
//         current_size++;
//     }

//     T& operator[](int index) {
//         assert (index < current_size);
//         return array[index];
//     }

//     const T& operator[](int index) const {
//         assert (index < current_size);
//         return array[index];
//     }

//     int size() const {
//         return current_size;
//     }

//     int capacity() const {
//         return maximum_size;
//     }

//     void resize(int new_size) {
//         if (new_size > maximum_size) {
//             T* new_array = nullptr;
//             gpuErrchk(cudaMallocManaged(&new_array, new_size));
//             for (int i = 0; i < current_size; i++) {
//                 new_array[i] = array[i];
//             }
//             gpuErrchk(cudaFree(array));
//             //delete[] array;
//             array = new_array;
//             maximum_size = new_size;
//         }
//         current_size = new_size;
//     }

//     void append(const T* elements, int size) {
//         resize(current_size + size);
//         for (int i = 0; i < size; i++) {
//             array[current_size + i] = elements[i];
//         }
//         current_size += size;
//     }

//     void free() {
//         gpuErrchk(cudaFree(array));
//     }

// };
