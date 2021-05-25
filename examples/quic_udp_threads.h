#pragma once

#include "udp_connection.h"

namespace QUIC_UDP_Threads {

using namespace QEngine_Compile;
using namespace QUICAPIs_Compile;
using namespace QUICConstants_Compile;

void send_thorugh_udp(DafnyArray<engine> eng, UDPConnection *udp) {
  while (udp->is_open) {
    uint32 packet_len = 4096;
    DafnyArray<uint8> packet(packet_len);

#ifdef DEBUG
    cerr << "[DEBUG] udp send thread - waiting for prepared packet from QUIC\n";
#endif

    auto result = QUICAPI::QUIC__prepare__packet((eng)[0], packet, packet_len);

    if (result.status == __default::PREPARE__ERROR__OTHER) {
      abort_with("[ERROR] udp send thread - failed to prepare packet");
    }

    if (result.status == __default::PREPARE__ERROR__CLOSED) {
      cerr << "[WARN] udp send thread - connection closed\n";
      break;
    }

    packet_len = result.packet__len;

    if (packet_len == 0) {
      cerr << "[WARN] udp send thread - received 0 bytes from quic, ignored\n";
      continue;
    }

    size_t num_bytes = udp->send((packet).ptr(), packet_len);

#ifdef DEBUG
    cerr << "[DEBUG] udp send thread - sending prepared packet " << num_bytes
         << " bytes\n";
#endif
  }

  cerr << "[INFO] udp send thread - exit\n";
  exit(0);
}

void recv_thorugh_udp(DafnyArray<engine> eng, UDPConnection *udp) {
  const uint32 max_size = 4096;
  unsigned char buf[max_size];
  while (udp->is_open) {
    uint32 packet_len;

#ifdef DEBUG
    cerr << "[DEBUG] udp receive thread - waiting to receive UDP data\n";
#endif

    packet_len = udp->recv(buf, max_size);

    if (packet_len == 0) {
      cerr << "[WARN] udp receive thread 0 bytes (skiping)\n";
      continue;
    }

    // Hand it to QUIC-dafny to process
    auto packet = DafnyArray<uint8>(buf, buf + packet_len);

    // Get the connection ID
    auto cid_ = QUICAPI::QUIC__get__connection__id(eng, packet, packet_len);
    if (cid_.is_Err_Fail()) {
      cerr << "[WARN] udp receive thread, failed to get connection ID.\n";
      continue;
    }
    auto cid = cid_.dtor_value();

#ifdef DEBUG
    cerr << "[DEBUG] udp receive thread - sending to quic for processing\n";
#endif

    QUICAPI::QUIC__process__packet((eng)[0], cid, packet, packet_len);
  }
  cerr << "[INFO] udp receive thread exit\n";
  exit(0);
}
} // namespace QUIC_UDP_Threads
