all: Makefile.coq
	@+$(MAKE) -f Makefile.coq all

dep:
	opam pin add -y -n -k git https://github.com/traiansf/sets-in-coq.git
	opam upgrade -y coq-sets.dev

clean: Makefile.coq
	@+$(MAKE) -f Makefile.coq cleanall
	@rm -f Makefile.coq Makefile.coq.conf

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

force _CoqProject Makefile: ;

%: Makefile.coq force
	@+$(MAKE) -f Makefile.coq $@

.PHONY: dep all clean force vlsm-opam
