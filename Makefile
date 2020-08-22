COQ_MAKEFILE := Makefile.coq
COQ_PROJECT := _CoqProject

all: default

default: $(COQ_MAKEFILE)
	$(MAKE) -f $(COQ_MAKEFILE)

quick: $(COQ_MAKEFILE)
	$(MAKE) -f $(COQ_MAKEFILE) quick

install: $(COQ_MAKEFILE)
	$(MAKE) -f $(COQ_MAKEFILE) install

clean: $(COQ_MAKEFILE)
	$(MAKE) -f $(COQ_MAKEFILE) cleanall
	$(RM) $(COQ_MAKEFILE) $(COQ_MAKEFILE).conf

$(COQ_MAKEFILE): $(COQ_PROJECT)
	coq_makefile -f $(COQ_PROJECT) -o $(COQ_MAKEFILE)

.PHONY: all default quick install clean
