# Note: please backport any changes here to ../Kremlin-Internal-Test/Makefile

UNAME		= $(shell uname)
MARCH		?= x86_64

LDOPTS += -L../evercrypt -levercrypt -lcrypto
LDOPTS += -L../kremlib -lkremlib

ifeq ($(OS),Windows_NT)
  SO = dll
  CC ?= x86_64-w64-mingw32-gcc
  CFLAGS := -pthread $(CFLAGS) -include log_to_choice.h
else ifeq ($(UNAME),Darwin)
  VARIANT = -Darwin
  SO = so
else ifeq ($(UNAME),Linux)
  VARIANT = -Linux
  CFLAGS := -fPIC $(CFLAGS)
  LDOPTS := -lpthread -Xlinker -z -Xlinker noexecstack -Xlinker --unresolved-symbols=report-all $(LDOPTS)
  SO = so
endif

# Force-include RegionAllocator.h and enable heap regions in all builds
CFLAGS := $(CFLAGS) -include RegionAllocator.h -DUSE_HEAP_REGIONS

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

all: libmitls.$(SO) libmitls.a

clean:
	 rm -fr *.o *.a *.d *.d.* *.dll *.so *~

%.d: %.c
	@set -e; rm -f $@; \
	  $(CC) -MM $(CFLAGS) $< > $@.$$$$; \
	  sed 's,\($(notdir $*)\)\.o[ :]*,$(dir $@)\1.o $@ : ,g' < $@.$$$$ > $@; \
	  rm -f $@.$$$$

-include $(addsuffix .d,$(FILES))

../kremlib/libkremlib.$(SO):
	@echo "Please run make in ../kremlib" && false

../evercrypt/libevercrypt.$(SO):
	@echo "Please run make in ../evercrypt" && false

libmitls.$(SO): ../kremlib/libkremlib.$(SO) ../evercrypt/libevercrypt.$(SO)

%.$(SO): $(addsuffix .o,$(FILES))
	$(CC) $(CFLAGS) -shared -o $@ $^ $(LDOPTS)

%.a: $(addsuffix .o,$(FILES))
	$(AR) cr $@ $^

