include "NativeTypes.dfy"
include "PrivateDLL.dfy"
include "QUICDataTypes.dfy"
include "QUICConstants.dfy"
include "HandleFFIs.dfy"
include "Extern.dfy"
include "QUICCrypto.dfy"
include "OverFlowCheck.dfy"
include "QUICUtils.dfy"
include "Options.dfy"

module QPacketSpace {

import opened NativeTypes
import opened PrivateDLL
import opened QUICDataTypes
import opened QUICConstants
import opened HandleFFIs
import opened Extern
import opened QUICCrypto
import opened OverFlowCheck
import opened QUICUtils
import opened Options

// State associated with a packet space.  There are three spaces: Initial, Handshake, and Application
class packet_space_state
{
    var crypto_state_ready: bool;

    var numberNotYetAcked: uint64; // number of unacknowledged packets
    var maxReceivedPacketNumber: uint62; // highest packet number seen so far

    var outgoing_acks: buffer<packet_num_t>; // queue of outgoing ACKs of length MAX_OUTGOING_ACKS
    var outgoging_ack_count: uint32; // count of entries in outgoing_acks
    var ack_only_packet: bool; // set when it's OK to send an ACK-only packet
    var ack_eliciting: bool;

    constructor()
        ensures Valid();
        ensures this.numberNotYetAcked == 0;
        ensures this.maxReceivedPacketNumber == 0;
        ensures this.outgoing_acks.Length == MAX_OUTGOING_ACKS as int;
        ensures this.outgoging_ack_count == 0;
        ensures this.ack_only_packet == false;
        ensures fresh(outgoing_acks);
    {
        this.numberNotYetAcked := 0;
        this.maxReceivedPacketNumber := 0;

        var ack_buffer := new uint62[MAX_OUTGOING_ACKS];
        this.outgoing_acks := ack_buffer;

        this.outgoging_ack_count := 0;
        this.ack_only_packet := false;
        this.crypto_state_ready := false;
        this.ack_eliciting := false;
    }

    predicate Valid()
        reads this, outgoing_acks
    {
        && outgoing_acks != null
        && outgoing_acks.Length == MAX_OUTGOING_ACKS as int
        && outgoging_ack_count as int < outgoing_acks.Length
    }

    method outgoing_ack_pending() returns (x: bool)
    {
        x := (outgoging_ack_count != 0 && (ack_eliciting && ack_only_packet));
    }

    // Register arrival of a packet, so an ACK will be sent later
    method register_ack(pn:packet_num_t, p_ack_eliciting: bool)
        requires Valid();
        modifies this`outgoging_ack_count, this`ack_eliciting, this.outgoing_acks;
        ensures outgoing_acks == old(outgoing_acks);
        ensures Valid();
    {
        var index := outgoging_ack_count;
        if index >= MAX_OUTGOING_ACKS - 1 {
            fatal("max outgoing acks reached\n");
        }
        outgoing_acks[index] := pn;
        outgoging_ack_count := index + 1;
        if p_ack_eliciting {
            ack_eliciting := true;
        }
    }

    method re_register_ack_range(start: uint62, length: uint62)
        requires Valid();
        modifies this`outgoging_ack_count, this`ack_eliciting, this.outgoing_acks;
        ensures outgoing_acks == old(outgoing_acks);
        ensures Valid();
    {
        FailOnOverflowAdd_u62(start, length);

        var i :uint62 := 0;
        while i < length
            invariant Valid();
            invariant outgoing_acks == old(outgoing_acks);
        {
            var pn := start + i;
            register_ack(pn, true);
            i := i + 1;
        }
    }

    // Handle loss of a frame of ACK data
    method on_lost_ACK_frame(tracker:ack_frame_fixed)
        requires Valid();
        modifies this`outgoging_ack_count, this`ack_eliciting, this.outgoing_acks;
        ensures Valid();
        ensures outgoing_acks == old(outgoing_acks);
    {
        var i, count := 0, tracker.block_count;
        var blocks := tracker.ack_blocks;

        while i < count
            invariant Valid();
            invariant outgoing_acks == old(outgoing_acks);
        {
            var ack_block := blocks[i];
            re_register_ack_range(ack_block.start, ack_block.range);
            i := i + 1;
        }
    }

    method reset_ack_buffer()
        requires Valid()
        modifies this`ack_only_packet, this`ack_eliciting, this`outgoging_ack_count;
        ensures Valid()
    {
        ack_only_packet := false;
        print("[DEBUG DFY] resetting ACK count: Sending ", outgoging_ack_count, " acks\n");
        outgoging_ack_count := 0;
        ack_eliciting := false;
    }

    static method count_ack_blocks(packet_numbers:buffer<packet_num_t>, pn_count:uint32) returns (x:uint32)
        requires packet_numbers != null && pn_count >= 1;
        requires pn_count as int <= packet_numbers.Length;
        ensures 1 <= x <= pn_count;
    {
        var i, block_count := 1, 1;  // there is at least one block
        var previous_pn := packet_numbers[0];

        // count the number of blocks
        while i < pn_count
            invariant 1 <= block_count <= i;
            invariant i <= pn_count;
        {
            var current_pn := packet_numbers[i];
            if (previous_pn == 0) { fatal("previous pn makes no sense"); }

            if current_pn != previous_pn - 1 { // there is a gap
                block_count := block_count + 1;
            }

            previous_pn := current_pn;
            i := i + 1;
        }

        x := block_count;
    }

    method build_ack_blocks(pn_space: packet_space) returns (x: ack_frame_fixed)
        requires Valid();
        requires outgoging_ack_count != 0;
    {
        var packet_numbers := outgoing_acks;
        var pn_count := outgoging_ack_count;

        // the acks are sorted & uniqued,
        pn_count := qsort_reversed(packet_numbers, pn_count);

        // get block count
        var block_count := count_ack_blocks(packet_numbers, pn_count);
        var ack_blocks := new ackblock_fixed[block_count];

        var i, block_index := 1, 0;
        var interval_start := packet_numbers[0];
        var previous_pn := packet_numbers[0];

        while i < pn_count
        {
            var current_pn := packet_numbers[i];
            if previous_pn == 0 { fatal("previous pn makes no sense"); }

            if (current_pn < previous_pn - 1) { // there is a gap
                // current_pn: marks the start of a new interval
                // previous_pn: marks the end of the previous interval

                if block_index >= block_count { fatal("something is wrong with block_index"); }
                append_ack_block(ack_blocks, block_index, interval_start, previous_pn);

                interval_start := current_pn;
                block_index := block_index + 1;
            }

            previous_pn := current_pn;
            i := i + 1;
        }

        if block_index >= block_count { fatal("something is wrong with block_index"); }
        append_ack_block(ack_blocks, block_index, interval_start, packet_numbers[pn_count-1]);

        x := ack_frame_raw(ack_blocks[..], block_count, 0, pn_space);
    }

    // interval_start and interval_end are both inclusive
    static method append_ack_block(ack_blocks:buffer<ackblock_fixed>, index:uint32, interval_start:uint62, interval_end:uint62)
        requires ack_blocks != null && index as int < ack_blocks.Length;
        modifies ack_blocks;
    {
        var gap := 0;
        if interval_start as uint64 == UINT62_MAX {fatal("interval_start makes no sense"); }
        if interval_start < interval_end { fatal("interval_start should not be less than interval_end"); }
        // since both are inclusive, range is the actual count - 1
        var range := interval_start - interval_end;

        // if this is not the first block, compute the gap
        if index != 0 {
            var pre_block := ack_blocks[index - 1];
            var pre_interval_end := pre_block.start - pre_block.range;
            if pre_interval_end <= interval_start { // should not be equal
                fatal("pre_interval_end makes no sense");
            }
            gap := pre_interval_end - interval_start;  // do not account for the encoding here
        }

        print("[DEBUG DFY] append ack range (", interval_start, ", " , interval_end, ")\n");
        ack_blocks[index] := ack_block_raw(gap, interval_start, range);
    }

}

class PspaceManager
{
    var initial_space: packet_space_state;
    var handshake_space: packet_space_state;
    var application_space: packet_space_state;
    var crypto_states: seq<state>;

    ghost var crypto_states_repr : set<state>;

    ghost var ps_states_repr : set<packet_space_state>;
    ghost var ack_buffers_repr : set<buffer<packet_num_t>>;

    predicate reprs_valid()
        reads this, ps_states_repr;
    {
        && ps_states_repr ==
            {initial_space, handshake_space, application_space}
        && ack_buffers_repr ==
            {initial_space.outgoing_acks, handshake_space.outgoing_acks, application_space.outgoing_acks}
        && crypto_states_repr == set x | x in crypto_states
    }

    predicate Valid()
        reads this, ps_states_repr, ack_buffers_repr;
    {
        && reprs_valid()
        && initial_space.Valid()
        && application_space.Valid()
        && handshake_space.Valid()
        && initial_space != handshake_space
        && initial_space != application_space
        && handshake_space != application_space
        && initial_space.outgoing_acks != handshake_space.outgoing_acks
        && initial_space.outgoing_acks != application_space.outgoing_acks
        && handshake_space.outgoing_acks != application_space.outgoing_acks
        && (forall k :: 0 <= k < |crypto_states| ==> crypto_states[k] != null)
        && (forall i, j :: 0 <= i < |crypto_states| &&
            0 <= j < |crypto_states| && i != j ==> crypto_states[i] != crypto_states[j])
        && |crypto_states| == 6
    }

    static method initialize_quic_crypto_state(packet_number: packet_num_t, secret: buffer_t)
        returns (x: state)
        requires secret != null;
        ensures x != null && fresh(x);
    {
        var state_ptr := new state[1];
        state_ptr[0] := null;
        var result_ptr := new error_code[1];

        create_in_st(state_ptr, packet_number, secret, result_ptr);

        if result_ptr[0] != Success {
            fatal("failed to initialize quic crypto state");
        }
        return state_ptr[0];
    }

    constructor()
        ensures Valid();
        ensures fresh(ps_states_repr);
        ensures fresh(crypto_states_repr);
        ensures fresh(ack_buffers_repr);
    {
        // these are just place holders
        var i, states := 0 as uint64, new state[6];

        var temp := new byte[1];
        states[0] := initialize_quic_crypto_state(0, temp);
        states[1] := initialize_quic_crypto_state(0, temp);
        states[2] := initialize_quic_crypto_state(0, temp);
        states[3] := initialize_quic_crypto_state(0, temp);
        states[4] := initialize_quic_crypto_state(0, temp);
        states[5] := initialize_quic_crypto_state(0, temp);

        crypto_states := states[..];

        var pss_1 := new packet_space_state();
        var pss_2 := new packet_space_state();
        var pss_3 := new packet_space_state();

        initial_space := pss_1;
        handshake_space := pss_2;
        application_space := pss_3;

        ps_states_repr := {pss_1, pss_2, pss_3};
        ack_buffers_repr := {pss_1.outgoing_acks, pss_2.outgoing_acks, pss_3.outgoing_acks};

        new;

        crypto_states_repr := set x | x in crypto_states;
    }

    method get_packet_space_state(ps: packet_space) returns (x: packet_space_state)
        requires Valid();
        ensures state_in_manager(x);
    {
        match ps
        {
            case INITIAL_SPACE => x := initial_space;
            case HANDSHAKE_SPACE => x := handshake_space;
            case APPLICATION_SPACE => x := application_space;
        }
    }

    method retransmit_ack_frame(ps:packet_space, tracker:ack_frame_fixed)
        requires Valid();
        modifies this.ps_states_repr, this.ack_buffers_repr;
        ensures Valid();
    {
        var pss := get_packet_space_state(ps);
        pss.on_lost_ACK_frame(tracker);
    }

    method enable_ack_only_packet(ps: packet_space)
        requires Valid();
        modifies this.ps_states_repr;
        ensures Valid();
    {
        var pss := get_packet_space_state(ps);
        if pss.outgoging_ack_count != 0 {
            pss.ack_only_packet := true;
        }
    }

    method register_packet_space_ack(ps: packet_space, packet_num: packet_num_t, ack_eliciting: bool)
        requires Valid();
        modifies this.ps_states_repr, this.ack_buffers_repr;
        ensures Valid();
    {
        print("[DEBUG DFY] registering ack for ", ps_str(ps), " ", packet_num,"\n");

        var pss := get_packet_space_state(ps);
        pss.register_ack(packet_num, ack_eliciting);
    }

    static method get_reader_index(ps: packet_space) returns (x : uint32)
        ensures x <= 5;
    {
        match ps
        {
            case INITIAL_SPACE => x := 0;
            case HANDSHAKE_SPACE => x := 2;
            case APPLICATION_SPACE => x := 4;
        }
    }

    static method get_writer_index(ps: packet_space) returns (x : uint32)
        ensures x <= 5;
    {
        match ps
        {
            case INITIAL_SPACE => x := 1;
            case HANDSHAKE_SPACE => x := 3;
            case APPLICATION_SPACE => x := 5;
        }
    }

    method get_decrypt_state(ps: packet_space) returns (x: state)
        requires Valid();
        ensures x in this.crypto_states_repr;
    {
        var i := get_reader_index(ps);
        print("[DEBUG DFY] getting decrypt state ", i, "\n");
        return crypto_states[i];
    }

    method get_encrypt_state(ps: packet_space) returns (x: state)
        requires Valid();
        ensures x in this.crypto_states_repr;
    {
        var i := get_writer_index(ps);
        return crypto_states[i];
    }

    predicate state_in_manager(pss: packet_space_state)
        reads this, this.ps_states_repr
    {
        pss in ps_states_repr
    }

    method seq_update_6<T>(s:seq<T>, i:uint32, x:T) returns (s2:seq<T>)
      requires 0 <= i as int < |s|;
      requires |s| == 6;
      ensures s2 == s[i as int := x]
    {
      var a := newArrayFill(6, s[0]);
      a[0] := s[0];
      a[1] := s[1];
      a[2] := s[2];
      a[3] := s[3];
      a[4] := s[4];
      a[5] := s[5];
      a[i] := x;
      return a[..];
    }

    method update_crypto_state(ps: packet_space, inital_packet_num: packet_num_t, traffic_secret: quic_key, is_reader: bool)
        requires Valid();
        requires traffic_secret != null;

        modifies this`crypto_states;
        modifies this`crypto_states_repr;
        modifies this.ps_states_repr;
        ensures fresh(crypto_states_repr - old(crypto_states_repr));

        ensures Valid();
    {
        var pss := get_packet_space_state(ps);

        pss.crypto_state_ready := true;

        if is_reader {
            var i := get_reader_index(ps);
            var decrypt_state := initialize_quic_crypto_state(inital_packet_num, traffic_secret);
            print("[DEBUG DFY] setting decrypt state ", i, "\n");
            crypto_states := seq_update_6(crypto_states, i, decrypt_state);
        } else {
            var j := get_writer_index(ps);
            var encrypt_state := initialize_quic_crypto_state(inital_packet_num, traffic_secret);
            print("[DEBUG DFY] setting encrypt state ", j, "\n");
            crypto_states := seq_update_6(crypto_states, j, encrypt_state);
        }

        crypto_states_repr := set x | x in crypto_states;
    }

    method crypto_state_ready(ps: packet_space) returns (x: bool)
        requires Valid();
    {
        var pss := get_packet_space_state(ps);
        x := pss.crypto_state_ready;
    }

    static method compute_written_bytes(h: header, plain_len: uint32) returns (x: uint32)
    {
        var h_len := header_len(h);

        if h_len as uint64 + plain_len as uint64 + AUTH_TAG_LENGTH as uint64 > UINT32_MAX as uint64 {
            fatal("trying to send too many bytes");
        }

        x := h_len + plain_len as uint32 + AUTH_TAG_LENGTH;
    }

    method encrypt_packet(ps: packet_space, h: header, src: buffer<byte>, src_len: uint32, dst: buffer<byte>)
        returns (x :encrypt_result) // returns dst_pn
        requires has_payload_length(h) ==> h.spec.payload_length as int == src_len as int + 16;

        requires Valid();
        requires src != null && src_len as int <= src.Length;
        requires dst != null && dst.Length >= header_len(h) as int + (if is_retry(h) then 0 else src_len as int + 16);

        modifies this.crypto_states_repr;
        modifies dst;
    {
        if src_len < 3 { fatal("insufficient length to encrypt"); }
        if is_retry(h) { fatal("unecpected retry packet"); }

        var state := get_encrypt_state(ps);
        var r := new error_code[1];

        var dst_pn := new uint62[1];

        encrypt(state, dst, dst_pn, h, src, src_len, r);

        if r[0] != Success {
            fatal("packet encryption failed!");
        }

        var written_bytes := compute_written_bytes(h, src_len);

        return encrypt_result(dst_pn[0], written_bytes);
    }

    method decrypt_pakcet(ps: packet_space, cid_len: cil_t, src: buffer<byte>, src_len: uint32, src_offset: uint32)
        returns (x :Err<decrypt_result>)

        requires Valid();
        
        requires buffer_offset_valid_pre(src, src_len, src_offset);

        modifies src;
        modifies this.ps_states_repr, this.ack_buffers_repr;
        modifies this.crypto_states_repr;

        ensures x.Ok? ==> (x.value.start_offset as int < x.value.end_offset as int <= src.Length)
            && (src_offset < x.value.next_packet_offset <= src_len)
        ensures Valid();
    {
        var cipher_length := src_len - src_offset;
        if cipher_length < 21 { return Fail("insufficient length to decrypt"); }

        var state := get_decrypt_state(ps);
        var r := new error_code[1];
        var dst := new result[1];

        decrypt(state, dst, src, src_offset, cipher_length, cid_len, r);

        if r[0] != Success {
            return Fail("packet decryption failed!");
        }

        var result := dst[0];
        var header := result.header;

        var cid := connection_id_raw([], 0);

        if header.BLong? {
            var scid := header.scid;
            if scid == null {
                fatal("null scid");
            }
            cid := connection_id_raw (scid[..], header.scil);
        }

        var payload_len, header_len, total_len := result.plain_len, result.header_len, result.total_len;

        if payload_len == 0 {
            return Fail("empty decrypted packet?");
        }
        print("[DEBUG DFY] decrypted packet pn=", result.pn, "\n");

        assert header_len as int + payload_len as int <= total_len as int;
        assert src_offset as int + total_len as int <= src.Length;
        assert src_offset as int + header_len as int + payload_len as int <= src.Length;
        assert src_offset < src_offset + result.total_len <= src_len;

        var start_offset := src_offset + header_len;
        var end_offset := start_offset + payload_len;
        var next_packet_offset := src_offset + result.total_len;

        print("[DEBUG DFY] header_len=", header_len, " payload_len=", payload_len);
        print(" total_len", result.total_len, "\n");

        x := Ok(decrypt_result(start_offset, end_offset, next_packet_offset, cid, result.pn));
    }
}

}
