#include <iostream>

#include "ffi-connections.cpp"
#include "quic_udp_threads.h"

using namespace std;
using namespace Options_Compile;
using namespace QUICDataTypes_Compile;
using namespace QStream_Compile;
using namespace QUICAPIs_Compile;
using namespace QUIC_UDP_Threads;

void client_read_through_quic(shared_ptr<connection> connection) {
  FILE *fp = fopen("./result.bin", "w");
  if (fp == NULL) {
    abort_with("[ERROR] client failed to open a file dump data");
  }

  while (true) {
#ifdef DEBUG
    cerr << "[DEBUG] app reader thread - waiting on stream data from QUIC\n";
#endif

    stream__recv recvd_data = QUICAPI::QUIC__recv__stream(connection);
    if (recvd_data.is_stream__recv_ReceivedData()) {
      data__recv d = recvd_data.dtor_d();
      qstream__segment__raw seg = d.segment;
      /*
      uint64 offset;
      DafnySequence<uint8> data;
      uint32 datalength;
      bool fin;
      bool isApplicationOwned;
      uint64 available;
      */

      fwrite(seg.data.sptr.get(), 1, seg.datalength, fp);

      if (seg.fin) {
        fclose(fp);
        cerr << "[INFO] app reader thread - received the final segment\n";
        break;
      }
    } else if (recvd_data.is_stream__recv_Reset()) {
      abort_with("[ERROR] app reader thread - reset received");
    } else {
      abort_with("[ERROR] app reader thread - connection error");
    }
  }
  cerr << "[INFO] app reader thread - exit\n";
}

const size_t buflen = 500;

void client_write_through_quic(shared_ptr<connection> connection,
                               shared_ptr<quic__stream__mutable> stream) {
  unsigned char buf[buflen];
  memset(buf, 0x42, buflen);

  bool reached_eof = true;

#ifdef DEBUG
  cerr << "[DEBUG] app writer thread - writing app data to QUIC\n";
#endif

  auto databuf = DafnyArray<uint8>(buf, buf + buflen);
  auto ret = QUICAPI::QUIC__send__stream(connection, stream, databuf, buflen,
                                         reached_eof);

  if (ret.is_Err_Fail()) {
    cerr << "[INFO] send stream failed: " << ret.dtor_err() << endl;
  } else if (ret.dtor_value() != true) {
    abort_with("[ERROR] send stream unexpectedly failed.");
  }

  cerr << "[INFO] app writer thread - exit\n";
}

const int stream_id = 4321;

extern "C" {
void EverCrypt_AutoConfig2_init();
}

int main(int argc, char **argv) {
  if (argc != 2) {
    cerr << "Usage: " << argv[0] << " {config file}" << endl;
    exit(0);
  }

  app_config config;
  if (parse_config(argv[1], &config) != 0) {
    abort_with("failed to parse config");
  }

  const int BYTE_LEN_FOR_CONN_ID = 8;

  EverCrypt_AutoConfig2_init();
  int ret_mitls_init = QUICFFI::ffi_mitls_init();
  cerr << "[INFO] QUICFFI::ffi_mitls_init() = " << ret_mitls_init << endl;

  auto eng = QUICAPI::QUIC__init__client(
      DafnySequenceFromString(string(config.address)), BYTE_LEN_FOR_CONN_ID);

  auto udp =
      UDPConnection::connect(config.address, config.port, config.drop_rate);

  std::thread send_thread(send_thorugh_udp, eng, udp);
  std::thread recv_thread(recv_thorugh_udp, eng, udp);

  auto connection = QUICAPI::QUIC__get__client(eng);

  if (connection == NULL) {
    abort_with("[ERROR] get client failed");
  }

  bool handshake_success = QUICAPI::QUIC__handshake(connection);

  if (!handshake_success) {
    abort_with("[ERROR] handshake failed");
  }

  // QUICConnection_quic_GetTicket could be used to get a ticket for
  // future 0-RTT here.

  auto stream = QUICAPI::QUIC__open__stream(connection, stream_id);

  if (stream == NULL) {
    abort_with("[ERROR] open stream failed");
  }

  cerr << "[INFO] client - opening stream" << endl;

  std::thread reader_thread(client_read_through_quic, connection);
  std::thread writer_thread(client_write_through_quic, connection, stream);

  writer_thread.join();
  reader_thread.join();

  cerr << "[INFO] client - app threads joined\n";

  // std::this_thread::sleep_for(std::chrono::milliseconds(200));
  QUICAPI::QUIC__close__client(connection);
  udp->shutdown_udp();

  recv_thread.join();
  send_thread.join();

  cerr << "[INFO] client - udp threads joined\n";

  return 0;
}
