include "NativeTypes.dfy"
include "QUICDataTypes.dfy"

module HandleFFIs {
    import opened NativeTypes
    import opened QUICDataTypes
    // This is implemented in QUICFStar.c and calls create_event_handleW with a NULL name and default security
    method {:extern "HandleFFIs", "create_event_handle"} create_event_handle(bManualReset:int32, bInitialState:int32) returns (x: handle_t)

    method {:extern "HandleFFIs", "close_event_handle"} close_event_handle(h: handle_t)

    // with a timeout in milliseconds
    method {:extern "HandleFFIs", "wait_for_event_handle"} wait_for_event_handle(h: handle_t, b:uint32)

    method {:extern "HandleFFIs", "set_event_handle"} set_event_handle(x:handle_t)

    method {:extern "HandleFFIs", "reset_event_handle"} reset_event_handle(x:handle_t)

    method wait_and_close(h: handle_t) {
        if h == NONE_HANDLE { return; }
        wait_for_event_handle (h, 0xffffffff); // block until the message is ACK'd
        close_event_handle(h);
    }

    function method {:extern "HandleFFIs", "engine_send_data_ready"} engine_send_data_ready() : handle_t

    // Implemented in QUICFStar.c, calls InitializeCriticalsection
    method {:extern "HandleFFIs", "monitor_init"} monitor_init() returns (x:voidptr)

    // Implemented in QUICFStar.c, calls EnterCriticalsection
    method {:extern "HandleFFIs", "monitor_enter"} monitor_enter(x:voidptr)

    // Implemented in QUICFStar.c, calls LeaveCriticalsection
    method {:extern "HandleFFIs", "monitor_exit"} monitor_exit(x:voidptr)

    /* Get the system time, in UTC, measured in Windows FILETIME units (10,000ns)
    The absolute value doesn't matter, as all computation is relative. */
    method {:extern "HandleFFIs", "get_system_time"} get_system_time() returns (x:uint64)

    predicate reverse_sorted(a: buffer<uint62>)
        requires a != null;
        reads a;
    {
        forall j, k :: 0 <= j < k < a.Length ==> a[j] >= a[k]
    }

    method {:extern "HandleFFIs", "qsort_reversed"} qsort_reversed(acks:buffer<uint62>, ackcount:uint32) returns (x:uint32)
        requires acks != null && ackcount != 0;
        ensures reverse_sorted(acks);
        ensures 0 < x as int <= acks.Length;

    // Set a one-shot timer. time is milliseconds since epcoh
    method {:extern "HandleFFIs", "set_single_timer"} set_single_timer(t:voidptr, time:uint64)

    // Cancel a timer.
    method {:extern "HandleFFIs", "cancel_timer"} cancel_timer(t:voidptr)

    // Set a repeating timer, with period specified in milliseconds
    method {:extern "HandleFFIs", "set_periodic_timer"} set_periodic_timer(t:voidptr, period:uint32)

    method {:extern "HandleFFIs", "random_byte"} random_byte() returns (x:uint8)
}
