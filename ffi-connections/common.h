#pragma once

#include <cassert>
#include <condition_variable>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <deque>
#include <iomanip>
#include <iostream>
#include <mutex>
#include <sstream>
#include <stdlib.h>

using namespace std;
using namespace QConnection_Compile;
using voidptr = DafnyArray<uint64>;

void abort_with(std::string message) {
  cerr << message << "\n";
  abort();
}

std::string dump(const unsigned char *buffer, size_t offset, size_t len) {
  std::ostringstream oss;
  std::hash<std::string> str_hash; // we cannot use std::hash<char*>
  uint8_t *sub_array = (uint8_t *)malloc(len);
  memcpy(sub_array, buffer + offset, len);

  std::string sub_string((char *)sub_array, len);
  assert(sub_string.length() == len);

  if (len == 0) {
    oss << "[empty]";
  } else {
    oss << "[" << offset << ", =" << offset + len - 1 << "] "
        << "<0x" << std::hex << str_hash(sub_string) << std::dec << ">";
  }

  oss << " [";
  for (size_t i = 0; i < len; i++) {
    oss << std::setfill('0') << std::setw(2) << std::hex
        << (0xff & (unsigned int)sub_string[i]);
  }
  oss << "]\n" << std::dec;

  oss.flush();

  free(sub_array);
  return oss.str();
}

std::string dump(DafnyArray<uint8_t> v) { return dump(v.ptr(), 0, v.size()); }

std::string dump(DafnyArray<uint8_t> v, uint32_t offset, uint32_t len) {
  if (offset + len > v.size()) {
    abort_with("[ERROR] dumping invalid buffer");
  }

  return dump(v.ptr(), offset, len);
}

struct app_config {
  char *address;
  char *port;
  char *file_path;
  size_t drop_rate; // 0 - 100
};

char *parse_line(FILE *fp, const char *expected) {
  char *line = NULL;
  char *value = NULL;
  size_t len = 0;
  int read = -1;

  if (((read = getline(&line, &len, fp)) != -1) ||
      (line[(size_t)read - 2] != '\"')) {
    line[read - 2] = '\0';
    value = strstr(line, expected) + strlen(expected);
    if (value != NULL) {
      value = strdup(value);
    }
  }

  free(line);
  if (value == NULL) {
    abort_with("[ERROR] failed to parse config file");
  }
  std::cout << "[INFO] using " << expected << value << "\"\n";
  return value;
}

int parse_config(const char *config_file_path, app_config *config) {
  auto fp = fopen(config_file_path, "r");
  if (fp == NULL) {
    return -1;
  }

  config->address = parse_line(fp, "address:\"");
  config->port = parse_line(fp, "port:\"");
  config->file_path = parse_line(fp, "in_path:\"");
  config->drop_rate = atoi(parse_line(fp, "loss:\""));
  return 0;
}

void *voidptr_to_voidstar(voidptr v) { return (void *)(v)[0]; }
voidptr voidstar_to_voidptr(void *u) {
  DafnyArray<uint64> ret(1);
  ret.at(0) = (uint64)u;
  return ret;
}

typedef struct {
  bool cancelled;
  std::mutex mtx;
  std::condition_variable cv;
  shared_ptr<connection> conn;
  uint64_t scheduled_time;
} connection_timer;

static deque<connection_timer> connection_timers;
static std::mutex connection_timers_mtx;
