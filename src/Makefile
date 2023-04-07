Main: *.agda
	agda --ghc --ghc-flag=-O2 --ghc-flag=-j4 meta-cedille.agda
#agda --ghc --ghc-flag=-prof --ghc-flag=-fprof-auto meta-cedille.agda

stack:
	stack --resolver lts-19 exec --package ieee --package bytestring-trie --package containers -- agda --ghc meta-cedille.agda

.PHONY: clean stack
clean:
	rm *.agdai meta-cedille
	rm -rf MAlonzo
