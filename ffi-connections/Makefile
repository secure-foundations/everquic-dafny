DAFNY?=dafny
DAFNY_DIR?=$(patsubst %/Binaries/,%,$(dir $(realpath $(shell which $(DAFNY)))))
DAFNY_RUNTIME_DIR:=$(DAFNY_DIR)/Binaries

CXXFLAGS += \
	-std=c++17 \
	-Werror \
	-Wall \
	-Wextra \
	-Wpedantic \
	-Wno-unused-parameter \
	-Wno-implicitly-unsigned-literal \
	-Wno-unused-variable \
	-ferror-limit=5

BOLD:="\033[1m"
RED:="\033[31m"
BRIGHTRED:="\033[1;31m"
RESET:="\033[0m"

ifeq (,$(KREMLIN_HOME))
  $(error please define KREMLIN_HOME to point to the root of your KReMLin git checkout)
endif

INCLUDEDIRS:= \
	../src \
	../src/obj \
	../miTLS/include/ \
	../everquic \
	../mipki \
	$(KREMLIN_HOME)/include \
	$(KREMLIN_HOME)/kremlib/dist/minimal \
	$(DAFNY_RUNTIME_DIR) \

CXX:=clang++
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
	$(foreach D,$(INCLUDEDIRS),-I$(D))

REBUILD_DEPENDENCIES := \
	$(foreach D,$(INCLUDEDIRS),$(wildcard $(D)/*.h)) \
	$(wildcard *-connect.cpp) \
	common.h \
	../src/obj/QUICAPIs.cpp

all: compile

compile: obj/ffi-connections.a

FORMATTARGETS:=$(addprefix format-,$(wildcard *.cpp *.h))

format: $(FORMATTARGETS)

$(FORMATTARGETS): format-%: %
	@echo $(BOLD)"[+] Formatting $<"$(RESET)
	@clang-format -i $<

clean:
	@echo $(BOLD)"[+] Removing obj/ directory"$(RESET)
	@rm -rf obj/

obj:
	@echo $(BOLD)"[+] Making $@/ directory"$(RESET)
	@mkdir $@

.PRECIOUS: obj

../src/obj/QUICAPIs.cpp: $(wildcard ../src/*.h) $(wildcard ../src/*.dfy)
	@echo $(BOLD)"[+] Building $@"$(RESET)
	@$(MAKE) -C ../src/ obj/QUICAPIs.cpp IGNORE_DEPENDENCY_GRAPH=1

.PRECIOUS: ../src/obj/QUICAPIs.cpp

obj/%.o: %.cpp $(REBUILD_DEPENDENCIES) | obj
	@echo $(BOLD)"[+] Compiling $*"$(RESET)
	@$(CXX) $(CXXFLAGS) -c -o $@ $<

obj/ffi-connections.a: obj/ffi-connections.o | obj
	@echo $(BOLD)"[+] Generating archive $(notdir $@)"$(RESET)
	@ar rcs $@ $^
