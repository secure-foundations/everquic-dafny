# This is the universal Makefile that will build any distribution of EverCrypt.
# - It is copied from hacl-star/providers/dist/Makefile
# - It relies on the KreMLin-generated Makefile.basic and Makefile.include
#
# This Makefile detects whether OpenSSL and BCrypt are enabled automatically. It
# does so by checking for the presence of EverCrypt_OpenSSL.h and
# EverCrypt_BCrypt.h ; as such, it assumes -bundle EverCrypt.OpenSSL and -bundle
# EverCrypt.BCrypt.
#
# This Makefile may (conservatively) link in some Vale assemblies that may end
# up un-needed in the final shared object.
#
# Additionally, this Makefile works out of the box on Linux, OSX and
# Cygwin/MinGW.
#
# The Makefile assumes KREMLIN_HOME and HACL_HOME to be suitably defined. When
# using OpenSSL, it also expects OPENSSL_HOME to be defined.
#
# The Makefile produces:
# - libevercrypt.so, a shared object where unused symbols have been removed
# - libevercrypt.a, a static archive that includes libhacl.a and libkremlib.a

# 1. The usual pseudo auto-configuration

UNAME		= $(shell uname)
MARCH		= x86_64
ifeq ($(UNAME),Darwin)
  VARIANT	= -darwin
  PKG_CONFIG    = pkg-config
  SO		= so
else ifeq ($(UNAME),Linux)
  CFLAGS	+= -fPIC #-fstack-check
  VARIANT	= -linux
  SO 		= so
  PKG_CONFIG    = pkg-config
  LDFLAGS	+= -Xlinker -z -Xlinker noexecstack -Xlinker --unresolved-symbols=report-all
else ifeq ($(OS),Windows_NT)
  CFLAGS        += -fno-asynchronous-unwind-tables
  CC		= $(MARCH)-w64-mingw32-gcc
  AR		= $(MARCH)-w64-mingw32-ar
  PKG_CONFIG    = $(MARCH)-w64-mingw32-pkg-config
  VARIANT	= -mingw
  SO		= dll
  LDFLAGS	= -Wl,--out-implib,libevercrypt.dll.a
endif

# 2. Parameters we want to compile with, for the generated Makefile
CFLAGS  += -I. -I ../include
CFLAGS  += -Wall -Wextra -Werror -std=c11 -Wno-unused-variable \
  -Wno-unknown-warning-option -Wno-unused-but-set-variable \
  -Wno-unused-parameter -Wno-infinite-recursion \
  -g -fwrapv -D_BSD_SOURCE -D_DEFAULT_SOURCE
ifeq ($(OS),Windows_NT)
CFLAGS  += -D__USE_MINGW_ANSI_STDIO
else
CFLAGS  += -fPIC
endif
CFLAGS  += $(USER_CFLAGS)
AR ?= ar

# 3. Honor configurations

LDFLAGS += -L../kremlib -lkremlib

# This is the "auto-detection". Since the parent Makefile runs with -bundle
# EverCrypt.OpenSSL, in case the static configuration doesn't call into
# OpenSSL, then EverCrypt_OpenSSL.h is not generated, meaning if the header
# doesn't exist we are not intend to compile against OpenSSL.
ifneq (,$(wildcard EverCrypt_OpenSSL.h))
  ifneq (,$(MLCRYPTO_HOME))
    CFLAGS      += -I$(MLCRYPTO_HOME)/openssl/include
    LDFLAGS     += -L$(MLCRYPTO_HOME)/openssl -lcrypto
  else
    CFLAGS	+= `$(PKG_CONFIG) --cflags libcrypto`
    LDFLAGS     += -lcrypto
  endif
  SOURCES	+= evercrypt_openssl.c
  ifneq ($(OS),Windows_NT)
  LDFLAGS       += -ldl -lpthread
  endif
endif

ifneq (,$(wildcard EverCrypt_BCrypt.h))
  LDFLAGS	+= -lbcrypt
  SOURCES	+= evercrypt_bcrypt.c
endif

OBJS 		+= $(patsubst %.S,%.o,$(wildcard amd64/*-$(MARCH)$(VARIANT).S))

include Makefile.include

SOURCES += $(ALL_C_FILES) $(USER_C_FILES)
OBJS    += $(patsubst %.c,%.o,$(SOURCES))

CFLAGS		+= -Wno-parentheses -Wno-deprecated-declarations -g -std=gnu11 -O3

Hacl_Poly1305_128.o Hacl_Chacha20_Vec128.o Hacl_Chacha20Poly1305_128.o: CFLAGS += -mavx
Hacl_Poly1305_256.o Hacl_Chacha20_Vec256.o Hacl_Chacha20Poly1305_256.o: CFLAGS += -mavx -mavx2

all: libevercrypt.$(SO) libevercrypt.a

clean:
	rm -fr *.o *.a *.d *.d.* *.dll *.so *~

libevercrypt.$(SO): ../kremlib/libkremlib.$(SO)
       
../kremlib/libkremlib.$(SO):
	@echo "Please run make in ../kremlib" && false

%.d: %.c
	@set -e; rm -f $@; \
	$(CC) -MM $(CFLAGS) $< > $@.$$$$; \
	sed 's,\($(notdir $*)\)\.o[ :]*,$(dir $@)\1.o $@ : ,g' < $@.$$$$ > $@; \
	rm -f $@.$$$$

-include $(patsubst %.c,%.d,$(SOURCES))

%.$(SO): $(OBJS)
	$(CC) $(CFLAGS) -shared -o $@ $^ $(LDFLAGS)

%.a: $(OBJS)
	$(AR) cr $@ $^

