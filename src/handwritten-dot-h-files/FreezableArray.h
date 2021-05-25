#include "DafnyRuntime.h"

namespace ColdArray_Compile {

  template <typename T>
  class FreezableArray {
    public:
      FreezableArray(uint64 len) {
        contents = DafnySequence<T>(len);
      }

      T get(uint64 index) {
        return contents.select(index);
      }

      void put(uint64 index, T val) {
        *(contents.start + index) =  val;
      }

      void freeze() {}

      DafnySequence<T> to__seq() {
        return contents;
      }

    private:
      DafnySequence<T> contents;
  };
}
