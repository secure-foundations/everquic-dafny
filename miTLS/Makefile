BOLD:="\033[1m"
RED:="\033[31m"
BRIGHTRED:="\033[1;31m"
BRIGHTCYAN:="\033[1;36m"
RESET:="\033[0m"

CC := clang


TARGETS := $(foreach T, \
	kremlib \
	evercrypt \
	mitls \
	quiccrypto \
	, $(T)/lib$(T))

all: $(foreach T, $(TARGETS), $(T).a $(T).so)

kremlib/libkremlib.%:
	@echo $(BOLD)"[+] Building $@"$(RESET)
	@$(MAKE) -C kremlib libkremlib.$* >/dev/null

evercrypt/libevercrypt.%: kremlib/libkremlib.%
	@echo $(BOLD)"[+] Building $@"$(RESET)
	@$(MAKE) -C evercrypt libevercrypt.$* >/dev/null

mitls/libmitls.%: kremlib/libkremlib.% evercrypt/libevercrypt.%
	@echo $(BOLD)"[+] Building $@"$(RESET)
	@$(MAKE) -C mitls libmitls.$* >/dev/null

quiccrypto/libquiccrypto.%: kremlib/libkremlib.% evercrypt/libevercrypt.%
	@echo $(BOLD)"[+] Building $@"$(RESET)
	@$(MAKE) -C quiccrypto libquiccrypto.$* >/dev/null

clean:
	@echo $(BOLD)"[+] Cleaning up"$(RESET)
	@$(MAKE) -C kremlib clean >/dev/null
	@$(MAKE) -C evercrypt clean >/dev/null
	@$(MAKE) -C mitls clean >/dev/null
	@$(MAKE) -C quiccrypto clean >/dev/null
	@rm -rf *~

update-dist: remove-dist
	@echo $(BOLD)"[+] Updating miTLS distribution from everest-dist/msquic."$(RESET)
	@git clone https://github.com/project-everest/everest-dist 2>/dev/null
	@cd everest-dist && git checkout adl_traffic_secrets && cd ..
	@cd everest-dist && git rev-parse HEAD > ../latest-commit-hash && cd ..
	@rm everest-dist/msquic/portable/Makefile
	@cp -r everest-dist/msquic/portable/* .
	@rm -rf everest-dist

remove-dist:
	@echo $(BRIGHTRED)"[+] Cleaning up current distribution."$(RESET)
	@rm -rf kremlib/ evercrypt/ mitls/ quiccrypto/ *~

.PHONY: all clean dist-clean update-dist remove-dist
