

REMOVE = rm -f

AGDA = agda

# Especially the composition proof runs out of stack space quickly.
AGDA_TC = $(AGDA) -v 0 +RTS -K40m -RTS

all: type-check

type-check:
	# NOTE: Files that still contain holes are commented out for now.
	
	# Foundations of formalization
	$(AGDA_TC) Utilities.agda
	$(AGDA_TC) Haskell.agda
	$(AGDA_TC) Identity.agda
	$(AGDA_TC) Monad.agda
	$(AGDA_TC) Polymonad.agda
	
	# Proofs related to Hicks original formulation
	$(AGDA_TC) Hicks/Polymonad.agda
	$(AGDA_TC) Hicks/Equivalency.agda
	$(AGDA_TC) Hicks/UniqueBinds.agda
	
	# General polymonad proofs
	$(AGDA_TC) Polymonad/Composable.agda
	$(AGDA_TC) Polymonad/Principal.agda
	$(AGDA_TC) Polymonad/Identity.agda
	$(AGDA_TC) Polymonad/UniqueBinds.agda
	
	# Composition of polymonads
	$(AGDA_TC) Polymonad/Composition.agda
	$(AGDA_TC) Polymonad/Composition/Composable.agda
	# $(AGDA_TC) Polymonad/Composition/Principal.agda
	$(AGDA_TC) Polymonad/Composition/Principal/Examples.agda
	
	# Composition of polymonads via morphisms between them
	# $(AGDA_TC) Polymonad/MorphMonad.agda
	# $(AGDA_TC) Polymonad/MaybeList.agda
	# $(AGDA_TC) Polymonad/MorphMonad/Types.agda
	# $(AGDA_TC) Polymonad/MorphMonad/Closure.agda
	# $(AGDA_TC) Polymonad/MorphMonad/Diamond1.agda
	# $(AGDA_TC) Polymonad/MorphMonad/Diamond2.agda
	
	# Standard Monads
	$(AGDA_TC) Monad/Identity.agda
	$(AGDA_TC) Monad/List.agda
	$(AGDA_TC) Monad/Maybe.agda
	$(AGDA_TC) Monad/Polymonad.agda
	$(AGDA_TC) Monad/Composable.agda
	$(AGDA_TC) Monad/Principal.agda
	
	# Parameterized Monads
	$(AGDA_TC) Parameterized/IndexedMonad.agda
	$(AGDA_TC) Parameterized/IndexedMonad/Polymonad.agda
	$(AGDA_TC) Parameterized/IndexedMonad/Composable.agda
	# $(AGDA_TC) Parameterized/IndexedMonad/Principal.agda
	# $(AGDA_TC) Parameterized/IndexedMonad/SessionTypes.agda
	# $(AGDA_TC) Parameterized/EffectMonad.agda


clean:
	$(REMOVE) *.agdai
	$(REMOVE) Monad/*.agdai
	$(REMOVE) Parameterized/*.agdai
	$(REMOVE) Parameterized/IndexedMonad/*.agdai
	$(REMOVE) Polymonad/*.agdai
	$(REMOVE) Polymonad/MorphMonad/*.agdai