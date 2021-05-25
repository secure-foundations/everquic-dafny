#pragma once

#include "DafnyRuntime.h"
namespace HandleFFIs {

  using handle_t = uint64;
  using voidptr = DafnyArray<uint64>;

  class __default {
    public:
      static handle_t create_event_handle(int32 bManualReset, int32 bInitialState);
      static void close_event_handle(handle_t h);
      static void wait_for_event_handle(handle_t a, uint32 b);
      static void set_event_handle(handle_t x);
      static void reset_event_handle(handle_t x);
      static handle_t engine_send_data_ready();

      static voidptr  monitor_init();
      static void monitor_enter(voidptr x);
      static void monitor_exit(voidptr x);
      static uint64 get_system_time();
      static uint32 qsort_reversed(DafnyArray<uint64> acks, uint32 ackcount);

      static void set_single_timer(voidptr t, uint64 time);
      static void cancel_timer(voidptr t);
      static void set_periodic_timer(voidptr t, uint32 period);

      static uint8 random_byte(); 
  };
}
