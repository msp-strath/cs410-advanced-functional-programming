AGDA ?= agda

check-install:
	${AGDA} -c 0-Install.agda --ghc-dont-call-ghc
	cabal run

clean:
	rm -rf MAlonzo
	rm -rf dist-newstyle
