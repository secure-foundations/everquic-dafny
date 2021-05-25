include "Options.dfy"
include "NativeTypes.dfy"
include "PrivateDLL.dfy"
include "Misc.dfy"
include "DynamicArray.dfy"
include "QUICDataTypes.dfy"
include "QUICConstants.dfy"
include "HandleFFIs.dfy"
include "QConnection.dfy"
include "Extern.dfy"

module QEngine {
import opened Options
import opened NativeTypes
import opened PrivateDLL
import opened Misc
import opened DynamicArray
import opened QUICDataTypes
import opened QUICConstants
import opened HandleFFIs
import opened QConnection
import opened Extern

type connectionholder_list = PrivateDoublyLinkedList<connection>

type newConnectionCallback = handle_t // (intptr, Option<connection>) ~> intptr

datatype versionreply_fixed = versionreply_fixed (
    replyid:connection_id_fixed,
    replyapp_state:voidptr
)

type versionreply_list = PrivateDoublyLinkedList<versionreply_fixed>

// All state associated with this client or server application
datatype engine = engine (
    eis_client:bool, // ()
    emonitor: voidptr,
    ehostname:seq<char>,
    connections:connectionholder_list,
    // List of version nego replies, ready to send
    versionreplies:versionreply_list,
    // App callback, called when a new connection object is created
    // newconnection: newConnectionCallback,
    // Opaque value passed to the app callback
    newconnection_state: voidptr,
    // Length of an outgoing ClientID
    eng_cil:cil_t
)

function flat<T>(s:set<set<T>>) : (r:set<T>)
  ensures forall x :: x in s ==> x <= r;
{
  set x, y | y in s && x in y :: x
}

predicate connection_disjoint(c1:connection, c2:connection)
  reads c1, c2;
  reads c1.short_header_packets, c2.short_header_packets;
  reads c1.fixedframes, c2.fixedframes;
  reads c1.lrcc_manager, c2.lrcc_manager;
  reads c1.lrcc_manager.sent_packets, c2.lrcc_manager.sent_packets;
  reads c1.stream_manager, c2.stream_manager;
  reads c1.pspace_manager, c2.pspace_manager;
{
  && c1 != c2
  && (c1.short_header_packets != c2.short_header_packets)
  && (c1.short_header_packets.buffer != c2.short_header_packets.buffer)
  && (c1.fixedframes != c2.fixedframes)
  && (c1.fixedframes.buffer != c2.fixedframes.buffer)
  && (c1.lrcc_manager != c2.lrcc_manager)
  && (c1.lrcc_manager.sent_packets != c2.lrcc_manager.sent_packets)
  && (c1.lrcc_manager.sent_packets.Repr !! c2.lrcc_manager.sent_packets.Repr)

  && (c1.stream_manager != c2.stream_manager)
  && (c1.stream_manager.quic_streams_repr !! c2.stream_manager.quic_streams_repr)
  && (c1.stream_manager.stream_nodes_repr !! c2.stream_manager.stream_nodes_repr)
  && (c1.stream_manager.stream_lists_repr !! c2.stream_manager.stream_lists_repr)
  && (c1.stream_manager.segment_lists_repr !! c2.stream_manager.segment_lists_repr)
  && (c1.stream_manager.segment_nodes_repr !! c2.stream_manager.segment_nodes_repr)

  && (c1.pspace_manager != c2.pspace_manager)
  && (c1.pspace_manager.ps_states_repr !! c2.pspace_manager.ps_states_repr)
  && (c1.pspace_manager.ack_buffers_repr !! c2.pspace_manager.ack_buffers_repr)
  && (c1.pspace_manager.crypto_states_repr !! c2.pspace_manager.crypto_states_repr)
}

predicate engine_valid(e:engine)
  reads e.connections;
  reads e.connections.Repr;
  reads e.connections.Vals;

  reads set c | c in e.connections.Vals :: c.short_header_packets;
  reads set c | c in e.connections.Vals :: c.short_header_packets.buffer;
  reads set c | c in e.connections.Vals :: c.fixedframes;
  reads set c | c in e.connections.Vals :: c.fixedframes.buffer;
  reads set c | c in e.connections.Vals :: c.lrcc_manager;
  reads set c | c in e.connections.Vals :: c.lrcc_manager.sent_packets;
  reads flat(set c | c in e.connections.Vals :: c.lrcc_manager.sent_packets.Repr);
  reads set c | c in e.connections.Vals :: c.stream_manager;
  reads flat(set c | c in e.connections.Vals :: c.stream_manager.quic_streams_repr);
  reads flat(set c | c in e.connections.Vals :: c.stream_manager.stream_nodes_repr);
  reads flat(set c | c in e.connections.Vals :: c.stream_manager.stream_lists_repr);
  reads flat(set c | c in e.connections.Vals :: c.stream_manager.segment_lists_repr);
  reads flat(set c | c in e.connections.Vals :: c.stream_manager.segment_nodes_repr);
  reads set c | c in e.connections.Vals :: c.pspace_manager;
  reads flat(set c | c in e.connections.Vals :: c.pspace_manager.ps_states_repr);
  reads flat(set c | c in e.connections.Vals :: c.pspace_manager.ack_buffers_repr);
  reads flat(set c | c in e.connections.Vals :: c.pspace_manager.crypto_states_repr);
{
    ghost var cs : connectionholder_list := e.connections;
    && cs.Valid()
    && (forall c :: c in cs.Vals ==> c.Valid())
    && (forall i, j :: 0 <= i < j < |cs.Vals| ==> connection_disjoint(cs.Vals[i], cs.Vals[j]))
}

}
