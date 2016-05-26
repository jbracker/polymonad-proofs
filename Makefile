
# NOTE: Files that still contain holes are commented out for now.

REMOVE = rm -f

AGDA = agda

# Especially the Polymonad.Union proof runs out of stack space quickly.
AGDA_TC = $(AGDA) -v 0 +RTS -K40m -RTS

all: type-check

type-check: | only-base only-hicks only-hicks only-monad only-parameterized only-supermonads
	# Union of polymonads via morphisms between them
	# $(AGDA_TC) MorphMonad/MorphMonad.agda
	# $(AGDA_TC) MorphMonad/MaybeList.agda
	# $(AGDA_TC) MorphMonad/Types.agda
	# $(AGDA_TC) MorphMonad/Closure.agda
	# $(AGDA_TC) MorphMonad/Diamond1.agda
	# $(AGDA_TC) MorphMonad/Diamond2.agda
	
only-base:
	# Foundations of formalization
	$(AGDA_TC) Utilities.agda
	$(AGDA_TC) Haskell.agda
	$(AGDA_TC) Identity.agda
	$(AGDA_TC) Functor.agda
	$(AGDA_TC) Applicative.agda
	$(AGDA_TC) Monad.agda
	$(AGDA_TC) Polymonad.agda
	$(AGDA_TC) Constrained/ConstrainedFunctor.agda
	$(AGDA_TC) Constrained/ConstrainedMonad.agda

only-hicks:
	# Proofs related to Hicks original formulation
	$(AGDA_TC) Hicks/Polymonad.agda
	$(AGDA_TC) Hicks/Equivalency.agda
	$(AGDA_TC) Hicks/UniqueBinds.agda

only-polymonad:
	# General polymonad proofs
	$(AGDA_TC) Polymonad/Unionable.agda
	$(AGDA_TC) Polymonad/Principal.agda
	$(AGDA_TC) Polymonad/Identity.agda
	$(AGDA_TC) Polymonad/UniqueBinds.agda
	
	# Union of polymonads
	$(AGDA_TC) Polymonad/Union.agda
	$(AGDA_TC) Polymonad/Union/Unionable.agda
	$(AGDA_TC) Polymonad/Union/Properties.agda
	$(AGDA_TC) Polymonad/Union/Principal.agda
	$(AGDA_TC) Polymonad/Union/Principal/Utilities.agda
	
only-monad:
	# Standard Monads
	$(AGDA_TC) Monad/Identity.agda
	$(AGDA_TC) Monad/List.agda
	$(AGDA_TC) Monad/Maybe.agda
	$(AGDA_TC) Monad/Polymonad.agda
	$(AGDA_TC) Monad/Unionable.agda
	$(AGDA_TC) Monad/Principal.agda
	$(AGDA_TC) Monad/PrincipalUnion.agda

only-parameterized:
	# Parameterized Monads
	$(AGDA_TC) Parameterized/PhantomIndices.agda
	$(AGDA_TC) Parameterized/IndexedMonad.agda
	$(AGDA_TC) Parameterized/IndexedMonad/Functor.agda
	$(AGDA_TC) Parameterized/IndexedMonad/Polymonad.agda
	$(AGDA_TC) Parameterized/IndexedMonad/Unionable.agda
	$(AGDA_TC) Parameterized/IndexedMonad/PhantomMonad.agda
	# $(AGDA_TC) Parameterized/IndexedMonad/Principal.agda
	# $(AGDA_TC) Parameterized/IndexedMonad/SessionTypes.agda
	$(AGDA_TC) Parameterized/IndexedMonad/DynState.agda
	$(AGDA_TC) Parameterized/EffectMonad.agda
	$(AGDA_TC) Parameterized/EffectMonad/Functor.agda
	$(AGDA_TC) Parameterized/EffectMonad/Polymonad.agda

only-supermonads: only-base
	# Super Monads
	$(AGDA_TC) Supermonad/Definition.agda
	$(AGDA_TC) Supermonad/Monad.agda
	$(AGDA_TC) Supermonad/IxMonad.agda
	$(AGDA_TC) Supermonad/EffectMonad.agda
	$(AGDA_TC) Supermonad/ConstrainedMonad.agda
	# $(AGDA_TC) Supermonad/Polymonad.agda

clean:
	$(REMOVE) *.agdai
	$(REMOVE) Monad/*.agdai
	$(REMOVE) Parameterized/*.agdai
	$(REMOVE) Parameterized/IndexedMonad/*.agdai
	$(REMOVE) Parameterized/EffectMonad/*.agdai
	$(REMOVE) Polymonad/*.agdai
	$(REMOVE) Polymonad/Union/*.agdai
	$(REMOVE) MorphMonad/*.agdai


