install: fix-replib
	cd lib/replib-read-only && cabal install
	cd src && cabal install

uninstall:
	-ghc-pkg unregister `ghc-pkg list | grep trellys`
	-ghc-pkg unregister `ghc-pkg list | grep RepLib`

clean:
	-rm -rf lib/replib-read-only/dist
	-rm -rf src/dist

# HACK: bump the RepLib version number so that cabal won't get
# confused when hackage tells cabal that RepLib-0.3 requires base >=
# 4.3.
fix-replib:
	cd lib/replib-read-only && sed -i -e 's/^version:.*0.3$$/version: 0.3.1/' RepLib.cabal
