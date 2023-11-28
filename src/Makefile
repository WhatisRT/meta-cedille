AGDACMD = agda --ghc --ghc-flag=-O2 --ghc-flag=-j4 --ghc-flag=-with-rtsopts=-A64m --ghc-flag=-rtsopts meta-cedille.agda
#agda --ghc --ghc-flag=-prof --ghc-flag=-fprof-auto meta-cedille.agda

Main: *.agda
	$(AGDACMD)

stack:
	stack --resolver lts-19 exec --package ieee --package bytestring-trie --package containers -- $(AGDACMD)

.PHONY: clean stack
clean:
	rm *.agdai meta-cedille
	rm -rf MAlonzo
