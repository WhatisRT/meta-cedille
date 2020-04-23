Main: *.agda
	agda --ghc meta-cedille.agda
#agda --ghc --ghc-flag=-prof --ghc-flag=-fprof-auto meta-cedille.agda

stack:
	stack exec --package ieee --package bytestring-trie -- agda --ghc meta-cedille.agda

.PHONY: clean stack
clean:
	rm *.agdai meta-cedille
	rm -rf MAlonzo
