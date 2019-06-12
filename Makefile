all:
	+$(MAKE) -C src
	cp src/meta-cedille .

.PHONY: all clean
clean:
	+$(MAKE) clean -C src
