# Some constants

BOLD:="\033[1m"
RED:="\033[31m"
BRIGHTRED:="\033[1;31m"
BRIGHTCYAN:="\033[1;36m"
RESET:="\033[0m"

DAFNY?=dafny
DAFNY_DIR?=$(patsubst %/Binaries/,%,$(dir $(realpath $(shell which $(DAFNY)))))
DAFNY_RUNTIME_DIR:=$(DAFNY_DIR)/Binaries

CXX:=clang++

DEBUG?=0
SANITIZE?=0
OPTIMIZE?=1

ifeq (,$(KREMLIN_HOME))
  $(error please define KREMLIN_HOME to point to the root of your KReMLin git checkout)
endif

CXXFLAGS += \
	-std=c++17 \
	-Werror \
	-Wall \
	-Wextra \
	-Wpedantic \
	-Wno-unused-parameter \
	-Wno-implicitly-unsigned-literal \
	-Wno-unused-variable \
	-Wno-nested-anon-types \
	-Wno-c99-extensions \
	-ferror-limit=5 \
	-Isrc/ \
	-Isrc/obj/ \
	-Iffi-connections/ \
	-ImiTLS/include/ \
	-Ieverquic/ \
	-Imipki/ \
	-I$(DAFNY_RUNTIME_DIR) \

ifeq ($(OPTIMIZE),1)
	CXXFLAGS += -O3 -mtune=native -march=native
endif

ifeq ($(DEBUG),1)
	CXXFLAGS += -g -D DEBUG
endif

STATIC_LINK_LIBRARIES := \
	everquic/libeverquic.a \
	miTLS/mitls/libmitls.a \
	miTLS/evercrypt/libevercrypt.a \
	miTLS/kremlib/libkremlib.a \

LDFLAGS += \
	-lcrypto \
	-lpthread \
	-Lmipki \
	-lmipki \

# Top level targets

all: compile

EXECUTABLES:=$(patsubst examples/%.cpp,obj/%,$(wildcard examples/*.cpp))

compile: $(EXECUTABLES)
	@true

verify:
	@$(MAKE) -C src/ verify

clean:
	@echo $(BOLD)"[+] Cleaning up src/"$(RESET)
	@$(MAKE) -C src/ clean >/dev/null
	@echo $(BOLD)"[+] Cleaning up ffi-connections/"$(RESET)
	@$(MAKE) -C ffi-connections/ clean >/dev/null
	@echo $(BOLD)"[+] Cleaning up miTLS/"$(RESET)
	@$(MAKE) -C miTLS/ clean >/dev/null
	@echo $(BOLD)"[+] Cleaning up everquic/"$(RESET)
	@$(MAKE) -C everquic/ clean >/dev/null
	@echo $(BOLD)"[+] Removing obj/ directory"$(RESET)
	@rm -rf obj/

# Compilation internals

obj:
	@echo $(BOLD)"[+] Making $@/ directory"$(RESET)
	@mkdir $@

src/%: FORCE
	@$(MAKE) -C src/ $*

ffi-connections/%: FORCE
	@echo $(BOLD)"[+] Building $@"$(RESET)
	$(MAKE) -C ffi-connections/ 

everquic/%: FORCE
	@echo $(BOLD)"[+] Building $@"$(RESET)
	@$(MAKE) -C everquic/ $* >/dev/null

miTLS/%: FORCE
	@$(MAKE) -C miTLS/ $*

format-examples-doth:
	@echo $(BOLD)"[+] Formatting examples/*.h"$(RESET)
	@clang-format -i examples/*.h

DEBUG_print_fail: FORCE | ffi-connections/obj/ffi-connections.a
	@sed -i 's/ result.tag = Err::TAG_Fail/ cerr << "Fail called with - " << err << endl;result.tag = Err::TAG_Fail/' src/obj/QUICAPIs.cpp

$(EXECUTABLES): obj/%: examples/%.cpp $(wildcard examples/*.h) ffi-connections/obj/ffi-connections.a $(STATIC_LINK_LIBRARIES) $(if $(DEBUG), DEBUG_print_fail) | obj
	@echo $(BOLD)"[+] Compiling $*"$(RESET)
	$(CXX) $(CXXFLAGS) $< $(STATIC_LINK_LIBRARIES) -o $@ $(LDFLAGS)

# Special directives

.PRECIOUS: obj

.PRECIOUS: everquic/%

.PHONY: all compile verify clean FORCE
