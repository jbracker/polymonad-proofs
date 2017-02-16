
# NOTE: Files that still contain holes are commented out for now.

REMOVE = rm -f

AGDA = agda

# Especially the Polymonad.Union proof runs out of stack space quickly.
AGDA_TC = $(AGDA) -v 0 +RTS -K40m -RTS

all: type-check

type-check: | only-base only-haskell only-hicks only-hicks only-parameterized only-supermonads only-cat-theory
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
	$(AGDA_TC) Substitution.agda
	$(AGDA_TC) Congruence.agda
	$(AGDA_TC) Haskell.agda
	$(AGDA_TC) Identity.agda

only-haskell:
	$(AGDA_TC) Haskell/Functor.agda
	$(AGDA_TC) Haskell/Applicative.agda
	$(AGDA_TC) Haskell/Monad.agda
	# Standard Monads
	$(AGDA_TC) Haskell/Monad/Identity.agda
	$(AGDA_TC) Haskell/Monad/List.agda
	$(AGDA_TC) Haskell/Monad/Maybe.agda
	$(AGDA_TC) Haskell/Monad/Polymonad.agda
	$(AGDA_TC) Haskell/Monad/Unionable.agda
	$(AGDA_TC) Haskell/Monad/Principal.agda
	$(AGDA_TC) Haskell/Monad/PrincipalUnion.agda
	# Constrained Monads & Functors
	$(AGDA_TC) Haskell/Constrained/ConstrainedFunctor.agda
	$(AGDA_TC) Haskell/Constrained/ConstrainedMonad.agda

only-hicks:
	# Proofs related to Hicks original formulation
	$(AGDA_TC) Hicks/Polymonad.agda
	$(AGDA_TC) Hicks/Equivalency.agda
	$(AGDA_TC) Hicks/UniqueBinds.agda

only-polymonad:
	# General polymonad proofs
	$(AGDA_TC) Polymonad/Definition.agda
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

only-parameterized:
	# Parameterized Monads
	$(AGDA_TC) Haskell/Parameterized/PhantomIndices.agda
	$(AGDA_TC) Haskell/Parameterized/IndexedMonad.agda
	$(AGDA_TC) Haskell/Parameterized/IndexedMonad/Functor.agda
	$(AGDA_TC) Haskell/Parameterized/IndexedMonad/Polymonad.agda
	$(AGDA_TC) Haskell/Parameterized/IndexedMonad/Unionable.agda
	$(AGDA_TC) Haskell/Parameterized/IndexedMonad/PhantomMonad.agda
	# $(AGDA_TC) Haskell/Parameterized/IndexedMonad/Principal.agda
	# $(AGDA_TC) Haskell/Parameterized/IndexedMonad/SessionTypes.agda
	$(AGDA_TC) Haskell/Parameterized/IndexedMonad/DynState.agda
	$(AGDA_TC) Haskell/Parameterized/EffectMonad.agda
	$(AGDA_TC) Haskell/Parameterized/EffectMonad/Functor.agda
	$(AGDA_TC) Haskell/Parameterized/EffectMonad/Polymonad.agda

only-supermonads:
	# Super Monads
	$(AGDA_TC) Supermonad/Definition.agda
	$(AGDA_TC) Supermonad/Monad.agda
	$(AGDA_TC) Supermonad/IxMonad.agda
	$(AGDA_TC) Supermonad/EffectMonad.agda
	$(AGDA_TC) Supermonad/ConstrainedMonad.agda
	# $(AGDA_TC) Supermonad/Polymonad.agda
	$(AGDA_TC) Supermonad/DefinitionWithCategory.agda
	$(AGDA_TC) Supermonad/DefinitionWithCategory/SubsetOfDefinition.agda

only-cat-theory:
	$(AGDA_TC) Theory/Triple.agda
	$(AGDA_TC) Theory/ProofIrrelevance.agda
	$(AGDA_TC) Theory/Category.agda
	$(AGDA_TC) Theory/Subcategory.agda
	$(AGDA_TC) Theory/Functor.agda
	$(AGDA_TC) Theory/ConstrainedFunctor.agda
	$(AGDA_TC) Theory/NaturalTransformation.agda
	$(AGDA_TC) Theory/NaturalTransformation/Whisker.agda
	$(AGDA_TC) Theory/NaturalIsomorphism.agda
	$(AGDA_TC) Theory/DinaturalTransformation.agda
	$(AGDA_TC) Theory/MonoidalCategory.agda
	$(AGDA_TC) Theory/Monad.agda
	$(AGDA_TC) Theory/AtkeyParameterizedMonad.agda
	$(AGDA_TC) Theory/Kleisli.agda
	$(AGDA_TC) Theory/RelativeMonad.agda
	$(AGDA_TC) Theory/Monoid.agda
	$(AGDA_TC) Theory/Preorder.agda
	$(AGDA_TC) Theory/TwoCategory.agda
	$(AGDA_TC) Theory/TwoFunctor.agda
	$(AGDA_TC) Theory/Examples/Category.agda
	$(AGDA_TC) Theory/Examples/Subcategory.agda
	$(AGDA_TC) Theory/Examples/Functor.agda
	$(AGDA_TC) Theory/Examples/TwoCategory.agda
	# Haskell Examples
	$(AGDA_TC) Theory/Examples/Haskell/FunctorEndomorphisms.agda
	$(AGDA_TC) Theory/Examples/Haskell/FunctorSet/Base.agda
	$(AGDA_TC) Theory/Examples/Haskell/FunctorSet/Nub.agda
	$(AGDA_TC) Theory/Examples/Haskell/FunctorSet/Sort.agda
	$(AGDA_TC) Theory/Examples/Haskell/FunctorSet/NubAndSort.agda
	# $(AGDA_TC) Theory/Examples/Haskell/FunctorSet/ListMap.agda # Discontinued approach
	$(AGDA_TC) Theory/Examples/Haskell/FunctorMonotonicSet.agda
	# Functor (Categorical) <===> Functor (Haskell)
	$(AGDA_TC) Theory/Examples/FunctorToHaskellFunctor.agda
	$(AGDA_TC) Theory/Examples/HaskellFunctorToFunctor.agda
	# Monad (Categorical) <===> Monad (Haskell)
	$(AGDA_TC) Theory/Examples/MonadToHaskellMonad.agda
	$(AGDA_TC) Theory/Examples/HaskellMonadToMonad.agda
	# Lax 2-Functor <===> Monad (Categorical)
	$(AGDA_TC) Theory/Examples/MonadToTwoFunctor.agda
	$(AGDA_TC) Theory/Examples/TwoFunctorToMonad.agda
	# Lax 2-Functor <===> Atkey Parameterized Monad
	$(AGDA_TC) Theory/Examples/AtkeyParameterizedMonadToTwoFunctor.agda
	# $(AGDA_TC) Theory/Examples/TwoFunctorToAtkeyParameterizedMonad.agda
	# IxMonad <===> Atkey Parameterized Monad
	$(AGDA_TC) Theory/Examples/AtkeyParameterizedMonadToIxMonad.agda
	# $(AGDA_TC) Theory/Examples/IxMonadToAtkeyParameterizedMonad.agda

clean:
	$(REMOVE) `find . -type f -name "*.agdai" | tr "\n" " "`
	$(REMOVE) `find . -type f -name "*.agda~" | tr "\n" " "`
