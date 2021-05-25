include "NativeTypes.dfy"
// include "BitVectors.dfy"

module QUICDataTypes {
    import opened NativeTypes

    type handle_t = uint64
    const NONE_HANDLE :handle_t := 0;

	type Pointer<T> = a:array?<T> | a == null || a.Length == 1

    type {:extern "struct"} state_s
    type state = Pointer<state_s>
    type voidptr = Pointer<uint64>

    type buffer<T> = a:array?<T> | a == null || a.Length < 0x100000000
    type buffer_t = buffer<byte>

    type quic_state = voidptr
    type quic_key = buffer<byte> //= intptr_t // an opaque handle to a crypto key
    type mitls_secret_native = voidptr // backed by a C mitls_secret (4 bytes, 4 bytes, 20 bytes)
    type quic_hash = mitls_hash
    type quic_aead = mitls_aead
    type quic_secret = mitls_secret
    type quic_secret_native = mitls_secret_native
    type quic_ticket = mitls_ticket

    type stream_id_t = uint62

    function method isStreamBidi (stream_id: uint62) : bool
    {
        and64(stream_id as uint64, 2) == 0
    }

    function method isStreamUni (stream_id: uint62) :bool
    {
        and64(stream_id as uint64, 2) != 0
    }

    function method isStreamClientInitiated (stream_id:stream_id_t) :bool
    {
        and64(stream_id as uint64, 1) == 0
    }

    function method isStreamServerInitiated (stream_id:stream_id_t) :bool
    {
        and64(stream_id  as uint64, 1) != 0
    }

    type packet_num_t = uint62

    // mitls_hash enum, from mitls FFI
    datatype mitls_hash =
        TLS_hash_MD5
        | TLS_hash_SHA1
        | TLS_hash_SHA224
        | TLS_hash_SHA256
        | TLS_hash_SHA384
        | TLS_hash_SHA512

    // mitls_aead, from mitls FFI
    datatype mitls_aead =
        TLS_aead_AES_128_GCM
        | TLS_aead_AES_256_GCM
        | TLS_aead_CHACHA20_POLY1305

    // F* representation of mitls_secret, which is serialized into an array of bytes and pinned, for interop.  Used for FFI.Node
    datatype mitls_secret = mitls_secret( // ()
        // hash datatype
        hash: mitls_hash,
        // aead datatype
        ae: mitls_aead,
        // secret length, in bytes
        secret_length: uint32,
        // secret value
        secret: buffer<byte>
    )

    // A miTLS ticket
    datatype mitls_ticket = mitls_ticket(
        ticket_len: uint64,
        ticket: buffer<byte>,
        session_len: uint64,
        session: buffer<byte>
    )

    datatype qstream_segment_raw = qstream_segment_raw ( // ()
        // starting offset 
        offset:uint62,
        data:seq<byte>,
        datalength:uint32,
        fin:bool,
        isApplicationOwned:bool,
        // a waitable handle
        available: handle_t,
        stream_id: stream_id_t
   )

    type qstream_segment_fixed = seg:qstream_segment_raw |
        |seg.data| == seg.datalength as int &&
        seg.offset as int + seg.datalength as int <= UINT62_MAX as int
        witness qstream_segment_raw(0, [], 0, false, false, 0, 0)

    // A fixed-value frame, queued for transmission.  Used for frames other than
    //    the dynamic ones (ACK, STREAM).  *)
    datatype fixed_frame_raw = fixed_frame_raw ( // ()
        framedata:seq<byte>,
        framelength:uint32,
        // Waitable event HANDLE, or 0 if the event is async
        handle:handle_t
    )

    type fixed_frame_fixed = frame:fixed_frame_raw |
        |frame.framedata| == frame.framelength as int
        witness fixed_frame_raw([1 as byte], 1, 0)

    // The QUIC view of a Send Stream
    datatype quic_send_stream_state =
        //| SendStreamReady
        | SendStreamSend
        | SendStreamDataSent
        | SendStreamResetSent
        | SendStreamDataRecvd // terminal state
        | SendStreamResetRecvd // terminal state

    // The QUIC view of a Recv Stream
    datatype quic_recv_stream_state =
    | RecvStreamRecv
    //| RecvStreamSizeKnown
    //| RecvStreamDataRecvd
    | RecvStreamResetRecvd
    | RecvStreamDataRead  // terminal state
    | RecvStreamResetRead // terminal state

    // Helper, with encoding of ACK frames
    datatype ack_block_raw = ack_block_raw (
        gap: uint62,
        start: uint62,
        range: uint62 
    )

    // acks [=start..=start-range] (both inclusive)

    type ackblock_fixed = block: ack_block_raw |
        && block.start as int >= block.range as int
        witness ack_block_raw(1, 1, 1)

    datatype packet_space =
        | INITIAL_SPACE
        | HANDSHAKE_SPACE
        | APPLICATION_SPACE

    function method ps_str(ps: packet_space) : string
    {
        match ps {
            case INITIAL_SPACE => "INITIAL_SPACE"
            case HANDSHAKE_SPACE => "HANDSHAKE_SPACE"
            case APPLICATION_SPACE => "APPLICATION_SPACE"
        }
    }

    type reset_token_t = t:seq<uint8> | |t| == 16
        witness [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

    datatype ack_frame_raw = ack_frame_raw (
        ack_blocks:seq<ackblock_fixed>,
        block_count: uint32,
        ack_delay: uint64,
        pn_space: packet_space
    )

    type ack_frame_fixed = t:ack_frame_raw |
        |t.ack_blocks| == t.block_count as int
        && t.block_count != 0
        witness ack_frame_raw([ack_block_raw(1, 1, 1)], 1, 0, INITIAL_SPACE)

    datatype loss_tracker_fixed =
        | crypto_tracker(c:qstream_segment_fixed)
        | stream_tracker(s:qstream_segment_fixed)
        | ack_tracker(a:ack_frame_fixed)
        | fixed_frame_tracker(f:fixed_frame_fixed)

    datatype sent_packet_raw = sent_packet_raw(
        sent_time: uint64,
        pn_space: packet_space,
        packet_number: packet_num_t,
        size: uint16,
        trackers: seq<loss_tracker_fixed>, 
        tracker_count : uint32, 
        ack_eliciting: bool, // if contains frame other than ACK, PADDING, CONNECTION_CLOSE 
        ack_only: bool // if contains only ACK 
    )

    type sent_packet_fixed = packet:sent_packet_raw |
        |packet.trackers| == packet.tracker_count as int
        witness sent_packet_raw(0, INITIAL_SPACE, 0, 0, [] , 0, false, true)

    // States of a QUIC connection
    datatype connection_state =
        | Start
        | ServerStatelessRetry
        | Running
        | Closed

    // A queue of packets that have arrived but haven't been processed yet
    datatype packet_holder_raw = packet_holder_raw (
        packet:seq<byte>,
        packet_len:uint32
    )

    type packet_holder_fixed = holder: packet_holder_raw |
        |holder.packet| != 0 &&
        |holder.packet| == holder.packet_len as int
        witness packet_holder_raw([1 as byte], 1)

    /*
    DCID Len:
    The byte following the version contains the length in bytes of the Destination Connection ID field that follows it. This length is encoded as an 8-bit unsigned integer. In QUIC version 1, this value MUST NOT exceed 20. Endpoints that receive a version 1 long header with a value larger than 20 MUST drop the packet. Servers SHOULD be able to read longer connection IDs from other QUIC versions in order to properly form a version negotiation packet.
    */

    type cil_t = cil:uint8 | 0 <= cil <= 20

    const ENGINE_CIL :cil_t := 20;

    datatype connection_id_raw = connection_id_raw (
        cid: seq<byte>,  // whose length in bytes is cil
        len: cil_t
    )

    type connection_id_fixed = id: connection_id_raw |
        |id.cid| == id.len as int
        witness connection_id_raw([], 0)

    // A pair of crypto keys
    datatype key_pair = key_pair(
        reader: quic_key,
        writer: quic_key
    )

    // Compute the end of a segment (offset+datalength)
    function method compute_segment_end(seg:qstream_segment_fixed) : (x:uint62)
    {
        seg.offset + (seg.datalength as uint62)
    }

    method print_segment(seg: qstream_segment_fixed)
    {
        var current_start := seg.offset;
        var current_end := compute_segment_end(seg);
        if seg.fin {
            print("(", current_start, ", ", current_end, " FIN) ");
        } else {
            print("(", current_start, ", ", current_end, ") ");
        }
    }

    // Data returned from quic_RecvStream
    datatype data_recv  = data_recv(
        stream_id: uint62,
        segment : qstream_segment_fixed
    )

    datatype reset_recv = reset_recv(
        rst_stream_id: uint62,
        rst_error_code: uint62
    )

    datatype stream_recv =
        | ReceivedData(d:data_recv)
        | Reset(r:reset_recv)
        | ConnectionError(err:string)

    datatype decrypt_result = decrypt_result (
        start_offset: uint32,
        end_offset : uint32,
        next_packet_offset : uint32,
        cid : connection_id_fixed,
        pn : packet_num_t
    )

    datatype encrypt_result = encrypt_result(
        packet_number : packet_num_t,
        written_bytes: uint32
    )

    datatype process_result = process_result(
        offset: uint32,
        ack_eliciting: bool
    )

    datatype prepare_result = prepare_result(
        offset: uint32,
        ack_eliciting: bool
    )

    datatype api_prepare_result = api_prepare_result(
        status: uint8,
        packet_len: uint32
    )
}
