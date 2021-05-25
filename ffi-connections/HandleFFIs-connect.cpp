#include "common.h"
#include "handwritten-dot-h-files/HandleFFIs.h"
#include <algorithm>
#include <chrono>
#include <cstdlib>
#include <deque> // because vector<mutex> isn't possible to do, due to move/copy constructor issues
#include <future>
#include <mutex>
#include <random>

namespace HandleFFIs {

using namespace QConnection_Compile;

using handle_t = uint64;

typedef struct event {
  bool closed = false;
  bool manual_reset;
  bool is_set = false;
  std::promise<void> p;
} event;

static vector<event> events;
static std::mutex event_mtx;

handle_t __default::create_event_handle(int32 bManualReset,
                                        int32 bInitialState) {

  cerr << "[DEBUGCALL].....create_event_handle....." << endl;

  if (bInitialState != 0 || bManualReset != 0) {
    abort_with("[ERROR] unexpected handle creation args");
  }

  event_mtx.lock();

  if (events.size() == 0) {
    events.emplace_back();
  }

  events.emplace_back();
  handle_t index = events.size() - 1;
  events[index].manual_reset = bManualReset;
  events[index].closed = false;
  events[index].is_set = false;

  event_mtx.unlock();
  return index;
}

void check_event_handle(handle_t h) {
  if (h == 0 || h >= events.size()) {
    abort_with("[ERROR] invalid handle received: " + std::to_string(h));
  }
  if (events[h].closed) {
    abort_with("[ERROR] closed handle received: " + std::to_string(h));
  }
}

void __default::close_event_handle(handle_t h) {
#ifdef DEBUG
  cerr << "[DEBUGCALL].....close_event_handle(" << h << ")....." << endl;
#endif
  event_mtx.lock();
  check_event_handle(h);
  events[h].closed = true;
  event_mtx.unlock();
}

void __default::wait_for_event_handle(handle_t h, uint32 wait_milliseconds) {
  check_event_handle(h);

#ifdef DEBUG
  cerr << "[DEBUG] wait handle(" << h << ")" << endl;
#endif
  std::chrono::milliseconds span(wait_milliseconds);
  auto res = events[h].p.get_future().wait_for(span);

  event_mtx.lock();
  if ((!events[h].manual_reset) && (res == future_status::ready)) {
    std::promise<void>().swap(events[h].p);
    events[h].is_set = false;
  }
  event_mtx.unlock();
}

void __default::set_event_handle(handle_t h) {
  check_event_handle(h);

  event_mtx.lock();

  if (events[h].is_set) {
#ifdef DEBUG
    cerr << "[WARN] ignored set handle(" << h << ")" << endl;
#endif
  } else {
#ifdef DEBUG
    cerr << "[DEBUG] set handle(" << h << ")" << endl;
#endif
    events[h].is_set = true;
    events[h].p.set_value();
  }

  event_mtx.unlock();
}

void __default::reset_event_handle(handle_t h) {
#ifdef DEBUG
  cerr << "[DEBUG reset_event_handle(" << h << ")" << endl;
#endif
  check_event_handle(h);

  if (!events[h].manual_reset) {
    abort_with("[ERROR] reset_event_handle called on non-manual reset handle");
  }

  event_mtx.lock();

  std::promise<void>().swap(events[h].p);
  events[h].is_set = false;

  event_mtx.unlock();
}

static std::mutex engine_send_data_ready_mtx;
static handle_t engine_send_data_ready_handle;
static bool engine_send_data_ready_initialized = false;

handle_t __default::engine_send_data_ready() {
  engine_send_data_ready_mtx.lock();
  if (!engine_send_data_ready_initialized) {
    engine_send_data_ready_handle = create_event_handle(0, 0);
    engine_send_data_ready_initialized = true;
  }
  engine_send_data_ready_mtx.unlock();
  return engine_send_data_ready_handle;
}

static std::mutex monitor_mtx;
static deque<std::mutex> monitors;

voidptr __default::monitor_init() {
#ifdef DEBUG
  cerr << "[DEBUGCALL].....monitor_init....." << endl;
#endif
  monitor_mtx.lock();
  uint64 ret = monitors.size();
  monitors.emplace_back();
  monitor_mtx.unlock();
  DafnyArray<uint64> arr(1);
  arr.at(0) = (uint64)ret + 1;
  return arr;
}

void monitor_handle_check(uint64 m) {
  if (m >= monitors.size()) {
    abort_with("[ERROR] non-existent monitor");
  }
}

void __default::monitor_enter(voidptr x) {
  monitor_mtx.lock();
  uint64 m = x[0] - 1;
  monitor_handle_check(m);
  monitor_mtx.unlock();
  monitors[m].lock();
}

void __default::monitor_exit(voidptr x) {
  // cerr << "[DEBUGCALL].....monitor_exit(" << (*x)[0] << ")....." << endl;
  monitor_mtx.lock();
  uint64 m = x[0] - 1;
  monitor_handle_check(m);
  monitor_mtx.unlock();
  monitors[m].unlock();
}

static bool compare_reversed(uint64 a, uint64 b) { return (a > b); }

uint32 __default::qsort_reversed(DafnyArray<uint64> acks, uint32 ackcount) {
  if (acks.size() < ackcount) {
    abort_with("[ERROR] invalid size for qsort_reversed");
  }
  auto begin = acks.begin();
  auto end = begin + ackcount;

  sort(begin, end, compare_reversed);
  auto unique_end = unique(begin, end);

#ifdef DEBUG
  cerr << "[DEBUG] sorted acks [";
  for (auto c = begin; c != unique_end; c++)
    cerr << *c << ", ";
  cerr << "]\n";
#endif

  return unique_end - begin;
}

uint64 __default::get_system_time() {
  auto t = std::chrono::high_resolution_clock::now();
  auto n = std::chrono::duration_cast<std::chrono::milliseconds>(
      t.time_since_epoch());
  return n / std::chrono::milliseconds(1);
  ;
}

void __default::set_single_timer(voidptr t, uint64 time) {
#ifdef DEBUG
  cerr << "[DEBUGCALL].....set_single_timer....." << endl;
#endif
  connection_timers_mtx.lock();

  uint64 i = (uint64)voidptr_to_voidstar(t);
  if (i >= connection_timers.size()) {
    abort_with("[ERROR] Invalid timer argument for set_single_timer");
  }
  auto &timer = connection_timers[i];

  if (time < timer.scheduled_time || time - timer.scheduled_time < 100) {
    connection_timers_mtx.unlock();
    return;
  }

  timer.scheduled_time = time;

  uint64_t now = get_system_time();
  uint64_t ticks = 0;

  if (time > now) {
    ticks = time - now;
  } else {
    cerr << "[WARN] timer expires in the past, waking now" << endl;
  }

  std::thread([&timer, ticks]() {
    std::this_thread::sleep_for(std::chrono::milliseconds(ticks));
    timer.cv.notify_all();
  })
      .detach();

  connection_timers_mtx.unlock();
}

void __default::cancel_timer(voidptr t) {
#ifdef DEBUG
  cerr << "[DEBUGCALL].....cancel_timer....." << endl;
#endif
  connection_timers_mtx.lock();
  uint64 i = (uint64)voidptr_to_voidstar(t);
  if (i >= connection_timers.size()) {
    cerr << "[ERROR] Invalid timer argument for cancel_timer : " << i << endl;
    abort();
  }
  connection_timers[i].cancelled = true;
  connection_timers_mtx.unlock();
}

void __default::set_periodic_timer(voidptr t, uint32 period) {
#ifdef DEBUG
  cerr << "[DEBUGCALL].....set_periodic_timer....." << endl;
#endif
  connection_timers_mtx.lock();
  uint64 i = (uint64)voidptr_to_voidstar(t);
  if (i >= connection_timers.size()) {
    cerr << "!!! Invalid timer argument for set_periodic_timer : " << i << endl;
    abort();
  }
  auto &timer = connection_timers[i];

  std::thread([&timer, period]() {
    while (true) {
      std::this_thread::sleep_for(std::chrono::microseconds(period));
      timer.cv.notify_all();
    }
  })
      .detach();
  connection_timers_mtx.unlock();
}

static std::random_device rand_device;

uint8 __default::random_byte() { return rand_device(); }

} // namespace HandleFFIs
