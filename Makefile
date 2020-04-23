all:
	+$(MAKE) -C src
	cp src/meta-cedille .

stack:
	+$(MAKE) stack -C src

.PHONY: all clean stack
clean:
	+$(MAKE) clean -C src
