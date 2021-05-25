#pragma once

#include <arpa/inet.h>
#include <errno.h>
#include <netdb.h>
#include <netinet/in.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/types.h>
#include <unistd.h>
#include <iostream>
#include <sstream>

using namespace std;

class UDPConnection {
  int sockfd;
  addrinfo *info;
  size_t drop_rate = 0;
  size_t recv_packet_count = 0;
  size_t dropped_packet_count = 0;

  struct sockaddr_storage their_addr;
  socklen_t their_addrlen;

  bool is_listener;

  UDPConnection() {}

  // get sockaddr, IPv4 or IPv6:
  static void *get_in_addr(struct sockaddr *sa) {
    if (sa->sa_family == AF_INET) {
      return &(((struct sockaddr_in *)sa)->sin_addr);
    }

    return &(((struct sockaddr_in6 *)sa)->sin6_addr);
  }

public:
  bool is_open;

  static UDPConnection *listener(const char *port, size_t dr) {
    UDPConnection *r = (UDPConnection *)calloc(1, sizeof(UDPConnection));
    r->is_listener = true;
    r->drop_rate = dr;

    struct addrinfo hints;
    int rv;
    char s[INET6_ADDRSTRLEN];
    addrinfo *servinfo;

    memset(&hints, 0, sizeof hints);
    hints.ai_family = AF_UNSPEC; // set to AF_INET to force IPv4
    hints.ai_socktype = SOCK_DGRAM;
    hints.ai_flags = AI_PASSIVE; // use my IP

    if ((rv = getaddrinfo(NULL, port, &hints, &servinfo)) != 0) {
      cerr << "[ERROR] udp listener - failed getaddrinfo";
      abort();
    }

    // loop through all the results and bind to the first we can
    for (r->info = servinfo; r->info != NULL; r->info = r->info->ai_next) {
      if ((r->sockfd = socket(r->info->ai_family, r->info->ai_socktype,
                              r->info->ai_protocol)) == -1) {
        cerr << "[WARN] listener bind: " << strerror(errno) << endl;
        continue;
      }

      if (bind(r->sockfd, r->info->ai_addr, r->info->ai_addrlen) == -1) {
        close(r->sockfd);
        cerr << "[WARN] listener bind: " << strerror(errno) << endl;
        continue;
      }

      break;
    }

    if (r->info == NULL) {
      cerr << "[ERROR] udp listener - failed to bind socket";
      abort();
    }

    cerr << "[INFO] Set up UDP listener on port " << port << endl;
    r->is_open = true;
    return r;
  }

  size_t recv(unsigned char *buf, size_t buflen) {
    if (!is_open) {
      cerr << "[WARN] connection closed, dropping recv\n";
      return 0;
    }

    int numbytes;

    their_addrlen = sizeof their_addr;
    if ((numbytes = recvfrom(sockfd, buf, buflen, 0,
                             (struct sockaddr *)&their_addr, &their_addrlen)) ==
        -1) {
      cerr << "[ERROR] recvfrom: " << strerror(errno) << endl;
      abort();
    }

    if (numbytes == 0) {
      is_open = false;
      return 0;
    }

    uint32_t num = rand() % 100;

    if (num < drop_rate && (recv_packet_count > 5)) {
      dropped_packet_count += 1;
      cerr << "[INFO] dropping packet, dropped: " << dropped_packet_count 
      << " received: " << recv_packet_count << endl;
      return 0;
    }

#ifdef DEBUG
    cerr << "[DEBUG] Received " << numbytes << " bytes on UDP." << endl;
#endif
    recv_packet_count += 1;
    return numbytes;
  }

  void shutdown_udp() {
    shutdown(sockfd, SHUT_RDWR);
    is_open = false;

    cerr << "[INFO] Shut down socket." << endl;
  }

  static UDPConnection *connect(const char *addr, const char *port, size_t dr) {
    UDPConnection *r = (UDPConnection *)calloc(1, sizeof(UDPConnection));
    r->is_listener = false;
    r->drop_rate = dr;

    struct addrinfo hints;
    int rv;
    addrinfo *servinfo;

    memset(&hints, 0, sizeof hints);
    hints.ai_family = AF_UNSPEC;
    hints.ai_socktype = SOCK_DGRAM;

    if ((rv = getaddrinfo(addr, port, &hints, &servinfo)) != 0) {
      cerr << "[ERROR] getaddrinfo: " << gai_strerror(rv) << endl;
      abort();
    }

    // loop through all the results and make a socket
    for (r->info = servinfo; r->info != NULL; r->info = r->info->ai_next) {
      if ((r->sockfd = socket(r->info->ai_family, r->info->ai_socktype,
                              r->info->ai_protocol)) == -1) {
        cerr << "[WARN] talker socket: " << strerror(errno) << endl;
        continue;
      }

      break;
    }

    if (r->info == NULL) {
      cerr << "[ERROR] failed to create socket" << endl;
      abort();
    }

#ifdef DEBUG
    cerr << "[DEBUG] connected to " << addr << ":" << port << endl;
#endif
    r->is_open = true;
    return r;
  }

  size_t send(const unsigned char *buf, size_t buflen) const {
    if (!is_open) {
      cerr << "[WARN] connection closed, dropping send\n";
      return 0;
    }

    int numbytes;
    const struct sockaddr *destaddr =
        is_listener ? (const struct sockaddr *)&their_addr : info->ai_addr;
    socklen_t destaddrlen = is_listener ? their_addrlen : info->ai_addrlen;
    if ((numbytes = sendto(sockfd, buf, buflen, 0, destaddr, destaddrlen)) ==
        -1) {
      cerr << "[ERROR] talker sendto: " << strerror(errno) << endl;
      abort();
    }
    return numbytes;
  }
};
