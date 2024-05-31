
COQMAKEFILE ?= Makefile.coq

all: $(COQMAKEFILE)
	$(MAKE) -f $^ $@

$(COQMAKEFILE): _CoqProject
	$(COQBIN)coq_makefile -f $^ -o $@

clean: $(COQMAKEFILE)
	$(MAKE) -f $^ cleanall

cleanall: $(COQMAKEFILE)
	$(MAKE) -f $^ cleanall
	$(RM) $^ $^.conf

.PHONY: all clean cleanall
