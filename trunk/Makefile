# Main Rules
# ==========
#
# make [all]: does a sandboxed install of RepLib and trellys-core.
#             Assumes you have Cabal installed, and that the default
#             Cabal install dir is on your path (~/.cabal/bin for
#             default "per-user" setup).  A trellys binary will be
#             installed in .capri/install/bin/trellys, and symlinked
#             to test/trellys (the only place you're expected to run
#             `trellys`).
#
# make test:  runs all tests in ./test.
#
# make sandbox-trellys: 
#             does a sandboxed install or trellys-core.  Quicker than
#             `make all`. Assumes you ran `make all` previously, and
#             that your sandboxed RepLib is up to date.
#
# make install: does a `cabal install` of RepLib and trellys-core.

.PHONY: all sandbox-install sandbox-uninstall sandbox-replib sandbox-trellys \
	    install uninstall clean test 

all: sandbox-install

sandbox-install: sandbox-replib sandbox-trellys

sandbox-uninstall:
	-rm -rf .capri

sandbox-replib: .capri 
	capri import lib/replib-read-only

# This has no dependencies to allow `make sandbox-trellys` to run
# quickly.
sandbox-trellys:
	capri import src
	ln -fs `pwd`/.capri/install/bin/trellys test

# You need to have the cabal install dir on your path (by default
# ~/.cabal/bin) so that `capri` command is found.
.capri:
	cabal install capri
	capri bootstrap
    # some trellys depend needs base < 4, and base < 4 needs syb
	cabal install syb #so that we have something to clone.
	capri clone syb 'base-3*'

install: 
	cd lib/replib-read-only && cabal install
	cd src && cabal install

uninstall:
	-ghc-pkg unregister `ghc-pkg list | grep trellys`
	-ghc-pkg unregister `ghc-pkg list | grep RepLib`
	@echo
	@echo You need to manually delete any trellys binaries on your path.
	@echo You can find them with \`which trellys\`

clean:
	-rm -rf lib/replib-read-only/dist
	-rm -rf src/dist

test:
	cd test && make

etags:
	find ./ -name .svn -prune -o -name '*.hs' -print | xargs hasktags --etags
