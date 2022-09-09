.PHONY: all aarch32 ppc32 ppc64 clean

all: clean aarch32 ppc32 ppc64

aarch32:
	$(MAKE) -C aarch32 all

ppc32:
	$(MAKE) -C ppc32 all

ppc64:
	$(MAKE) -C ppc all

clean:
	$(MAKE) -C aarch32 realclean
	$(MAKE) -C ppc32 realclean
	$(MAKE) -C ppc realclean
