#pragma once

#include "DafnyRuntime.h"
#include <cstdlib>

using namespace std;

namespace Extern {

  class __default {
    public: 
      template <typename T>
      static DafnyArray<T> newArrayFill(uint64 size, T v) {
        DafnyArray<T> ret = DafnyArray<T>(size);
        for (uint64 i = 0; i < size; i++) {
          (ret)[i] = v;
        }
        return ret;
      }

#define fatal(m) aux_fatal(__FUNCTION__, __FILE__, __LINE__, m)

      static void aux_fatal(const char* fn, const char* file, int line, DafnySequence<char> m) {
        cout << "!!! FATAL(" << m << ") at " << fn << " -- " << file << ":" << line << " !!!" << endl;
        abort();
      }

#define fatal_assume() aux_fatal_assume(__FUNCTION__, __FILE__, __LINE__)

      static void aux_fatal_assume(const char* fn, const char* file, int line)
      {
        cout << "!!! fatal_assume at " << fn << " -- " << file << ":" << line << " !!!" << endl;
      }
  };
}
