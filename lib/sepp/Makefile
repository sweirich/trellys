default:
	@echo You probably want to do 'cabal install seppp.cabal' ...

# You may need to run './Setup configure'.  If that complains and
# missing packages, and you've already installed them, see
# http://www.haskell.org/cabal/FAQ.html#runghc-setup-complains-of-missing-packages
~/.cabal/bin/sep: Setup Language/SepPP/*hs
	./Setup build && ./Setup install

Setup:	Setup.hs
	ghc --make Setup.hs
