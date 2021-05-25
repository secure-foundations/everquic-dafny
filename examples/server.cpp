#include <cstdio>
#include <iostream>

#include "ffi-connections.cpp"
#include "quic_udp_threads.h"

using namespace std;
using namespace std::chrono_literals;

using namespace Options_Compile;
using namespace QUICDataTypes_Compile;
using namespace QStream_Compile;
using namespace QUICAPIs_Compile;
using namespace QUIC_UDP_Threads;

bool finished = false;
shared_ptr<quic__stream__mutable> stream = nullptr;

char *file_path;

void server_read_through_quic(shared_ptr<connection> connection) {
  while (!finished) {
#ifdef DEBUG
    cerr << "[DEBUG] app reader thread - waiting on stream data from QUIC"
         << endl;
#endif
    stream__recv recvd_data = QUICAPI::QUIC__recv__stream(connection);
    if (recvd_data.is_stream__recv_ReceivedData()) {
      data__recv d = recvd_data.dtor_d();
      qstream__segment__raw seg = d.segment;

      if (stream == nullptr) {
        stream = QUICAPI::QUIC__open__stream(connection, d.stream__id);
        if (stream == nullptr) {
          abort_with("[ERROR] app reader thread - stream is null");
        }
        cerr << "[INFO] app reader thread - stream set\n";
      }

      if (seg.fin) {
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

void server_write_through_quic(shared_ptr<connection> connection) {
  FILE *fp = fopen(file_path, "r");

  if (fp == NULL) {
    abort_with("[ERROR] server failed to open the file to transfer");
  }

  const size_t bufsize = 1300; 
  DafnyArray<uint8> databuf(bufsize);

  bool reached_eof = false;

  while (!finished) {
    if (stream == nullptr) {
      std::this_thread::sleep_for(std::chrono::milliseconds(200));
      continue;
    }

#ifdef DEBUG
    cerr << "[DEBUG] app writer thread - writing app data to QUIC\n";
#endif

    size_t bytes_read = fread(databuf.ptr(), 1, bufsize, fp);

    if (bytes_read != bufsize) {
      reached_eof = true;
    }

    auto ret = QUICAPI::QUIC__send__stream(connection, stream, databuf,
                                           bytes_read, reached_eof);

    if (ret.is_Err_Fail()) {
      cerr << "[INFO] send stream failed: " << ret.dtor_err() << endl;
    } else if (ret.dtor_value() != true) {
      abort_with("[ERROR]  unexpectedly failed");
    }

    if (reached_eof) {
      finished = true;
      break;
    }
  }
  fclose(fp);

  cerr << "[INFO] app writer thread - exit\n";
}

std::thread reader_thread;
std::thread writer_thread;

shared_ptr<QUICFFI::connection> client_connection;
bool new_connection = false;
std::mutex new_connection_mtx;
std::condition_variable new_connection_cv;

QUICFFI::voidptr newconnection_cb(QUICFFI::voidptr connection_state,
                                  shared_ptr<QUICFFI::connection> connection) {
  cerr << "[INFO] server handling a new connection" << endl;
  reader_thread = std::thread(server_read_through_quic, connection);
  writer_thread = std::thread(server_write_through_quic, connection);

  reader_thread.detach();
  writer_thread.detach();

  client_connection = connection;

  return voidstar_to_voidptr(NULL);
};

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

  file_path = config.file_path;

  const int BYTE_LEN_FOR_CONN_ID = 8;

  EverCrypt_AutoConfig2_init();
  int ret_mitls_init = QUICFFI::ffi_mitls_init();
  cerr << "[INFO] ffi_mitls_init = " << ret_mitls_init << "\n";

  QUICFFI::con_cb = newconnection_cb;

  auto eng = QUICAPI::QUIC__init__server(
      DafnySequenceFromString(string(config.address)), NULL,
      BYTE_LEN_FOR_CONN_ID);

  auto udp = UDPConnection::listener(config.port, 0);

  std::thread send_thread(send_thorugh_udp, eng, udp);
  std::thread recv_thread(recv_thorugh_udp, eng, udp);

  send_thread.detach();
  recv_thread.detach();

  while (true) {
    std::this_thread::sleep_for(2s);
  }
}
