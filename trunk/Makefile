install:
	cd lib/replib-read-only && cabal install
	cd src && cabal install

uninstall:
	-ghc-pkg unregister `ghc-pkg list | grep trellys`
	-ghc-pkg unregister `ghc-pkg list | grep RepLib`

clean:
	-rm -rf lib/replib-read-only/dist
	-rm -rf src/dist
