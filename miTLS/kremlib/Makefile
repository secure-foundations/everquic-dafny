# Note: please backport any changes here to ../Kremlin-Internal-Test/Makefile

UNAME		= $(shell uname)
MARCH		?= x86_64

ifeq ($(OS),Windows_NT)
  PATH := $(MITLS_HOME)/src/pki:$(PATH)
  SO = dll
  CC ?= x86_64-w64-mingw32-gcc
  LDOPTS += 
  export PATH
else ifeq ($(UNAME),Darwin)
  VARIANT = -Darwin
  DYLD_LIBRARY_PATH :=$(MITLS_HOME)/src/pki:$(DYLD_LIBRARY_PATH)
  SO = so
  export DYLD_LIBRARY_PATH
else ifeq ($(UNAME),Linux)
  VARIANT = -Linux
  CFLAGS := -fPIC $(CFLAGS)
  LD_LIBRARY_PATH :=  $(MITLS_HOME)/src/pki:$(LD_LIBRARY_PATH)
  LDOPTS := -lpthread -Xlinker -z -Xlinker noexecstack -Wl,-z,defs $(LDOPTS)
  SO = so
  export LD_LIBRARY_PATH
endif

# Force-include RegionAllocator.h and enable heap regions in all builds
CFLAGS := $(CFLAGS) -include RegionAllocator.h -DUSE_HEAP_REGIONS

ifndef NO_OPENSSL
ifeq ($(OS),Windows_NT)
  PATH := $(MLCRYPTO_HOME)/openssl:$(PATH)
else ifeq ($(UNAME),Darwin)
  DYLD_LIBRARY_PATH := $(MLCRYPTO_HOME)/openssl:$(DYLD_LIBRARY_PATH)
else
  LD_LIBRARY_PATH := $(MLCRYPTO_HOME)/openssl:$(LD_LIBRARY_PATH)
endif
endif

INCLUDE_DIRS 	= ../include .

# we are now packaging most miTLS modules into meaningful C compilation units
# See src/tls/Makefile.Kremlin for the list of bundles that are used
# All extracted C files should be part of the DLL
FILES = $(patsubst %.c,%,$(wildcard *.c))

CFLAGS := $(addprefix -I,$(INCLUDE_DIRS)) $(CFLAGS) -Wall -Werror -Wno-deprecated-declarations \
  -Wno-unused-variable -Wno-parentheses -Wno-unknown-warning-option \
  -Wno-unused-but-set-variable -Wno-infinite-recursion -g -fwrapv \
  -D_BSD_SOURCE -D_DEFAULT_SOURCE -D__USE_MINGW_ANSI_STDIO \
  -Wno-missing-braces -Wno-error-tautological-compare -Wno-error-int-to-void-pointer-cast \
  -Wno-error-enum-conversion

all: libkremlib.$(SO) libkremlib.a

clean:
	rm -fr *.o *.a *.d *.d.* *.dll *.so *~

%.d: %.c
	@set -e; rm -f $@; \
	  $(CC) -MM $(CFLAGS) $< > $@.$$$$; \
	  sed 's,\($(notdir $*)\)\.o[ :]*,$(dir $@)\1.o $@ : ,g' < $@.$$$$ > $@; \
	  rm -f $@.$$$$

-include $(addsuffix .d,$(FILES))

%.a: $(addsuffix .o,$(FILES))
	$(AR) cr $@ $^

%.$(SO): $(addsuffix .o,$(FILES))
	$(CC) $^ -shared -o $@ $(LDOPTS)


