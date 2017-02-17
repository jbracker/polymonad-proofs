
SOURCE_DIR = src

# NOTE: Files that still contain holes are commented out for now.

REMOVE = rm -f

AGDA = agda

# Especially the Polymonad.Union proof runs out of stack space quickly.
AGDA_TC = $(AGDA) -i$(SOURCE_DIR) -v 0 +RTS -K40m -RTS


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
	$(AGDA_TC) $(SOURCE_DIR)/Utilities.agda
	$(AGDA_TC) $(SOURCE_DIR)/Substitution.agda
	$(AGDA_TC) $(SOURCE_DIR)/Congruence.agda
	$(AGDA_TC) $(SOURCE_DIR)/Haskell.agda
	$(AGDA_TC) $(SOURCE_DIR)/Identity.agda

only-haskell:
	$(AGDA_TC) $(SOURCE_DIR)/Haskell/Functor.agda
	$(AGDA_TC) $(SOURCE_DIR)/Haskell/Applicative.agda
	$(AGDA_TC) $(SOURCE_DIR)/Haskell/Monad.agda
	# Standard Monads
	$(AGDA_TC) $(SOURCE_DIR)/Haskell/Monad/Identity.agda
	$(AGDA_TC) $(SOURCE_DIR)/Haskell/Monad/List.agda
	$(AGDA_TC) $(SOURCE_DIR)/Haskell/Monad/Maybe.agda
	$(AGDA_TC) $(SOURCE_DIR)/Haskell/Monad/Polymonad.agda
	$(AGDA_TC) $(SOURCE_DIR)/Haskell/Monad/Unionable.agda
	$(AGDA_TC) $(SOURCE_DIR)/Haskell/Monad/Principal.agda
	$(AGDA_TC) $(SOURCE_DIR)/Haskell/Monad/PrincipalUnion.agda
	# Constrained Monads & Functors
	$(AGDA_TC) $(SOURCE_DIR)/Haskell/Constrained/ConstrainedFunctor.agda
	$(AGDA_TC) $(SOURCE_DIR)/Haskell/Constrained/ConstrainedMonad.agda

only-hicks:
	# Proofs related to Hicks original formulation
	$(AGDA_TC) $(SOURCE_DIR)/Hicks/Polymonad.agda
	$(AGDA_TC) $(SOURCE_DIR)/Hicks/Equivalency.agda
	$(AGDA_TC) $(SOURCE_DIR)/Hicks/UniqueBinds.agda

only-polymonad:
	# General polymonad proofs
	$(AGDA_TC) $(SOURCE_DIR)/Polymonad/Definition.agda
	$(AGDA_TC) $(SOURCE_DIR)/Polymonad/Unionable.agda
	$(AGDA_TC) $(SOURCE_DIR)/Polymonad/Principal.agda
	$(AGDA_TC) $(SOURCE_DIR)/Polymonad/Identity.agda
	$(AGDA_TC) $(SOURCE_DIR)/Polymonad/UniqueBinds.agda
	
	# Union of polymonads
	$(AGDA_TC) $(SOURCE_DIR)/Polymonad/Union.agda
	$(AGDA_TC) $(SOURCE_DIR)/Polymonad/Union/Unionable.agda
	$(AGDA_TC) $(SOURCE_DIR)/Polymonad/Union/Properties.agda
	$(AGDA_TC) $(SOURCE_DIR)/Polymonad/Union/Principal.agda
	$(AGDA_TC) $(SOURCE_DIR)/Polymonad/Union/Principal/Utilities.agda

only-parameterized:
	# Parameterized Monads
	$(AGDA_TC) $(SOURCE_DIR)/Haskell/Parameterized/PhantomIndices.agda
	$(AGDA_TC) $(SOURCE_DIR)/Haskell/Parameterized/IndexedMonad.agda
	$(AGDA_TC) $(SOURCE_DIR)/Haskell/Parameterized/IndexedMonad/Functor.agda
	$(AGDA_TC) $(SOURCE_DIR)/Haskell/Parameterized/IndexedMonad/Polymonad.agda
	$(AGDA_TC) $(SOURCE_DIR)/Haskell/Parameterized/IndexedMonad/Unionable.agda
	$(AGDA_TC) $(SOURCE_DIR)/Haskell/Parameterized/IndexedMonad/PhantomMonad.agda
	# $(AGDA_TC) Haskell/Parameterized/IndexedMonad/Principal.agda
	# $(AGDA_TC) Haskell/Parameterized/IndexedMonad/SessionTypes.agda
	$(AGDA_TC) $(SOURCE_DIR)/Haskell/Parameterized/IndexedMonad/DynState.agda
	$(AGDA_TC) $(SOURCE_DIR)/Haskell/Parameterized/EffectMonad.agda
	$(AGDA_TC) $(SOURCE_DIR)/Haskell/Parameterized/EffectMonad/Functor.agda
	$(AGDA_TC) $(SOURCE_DIR)/Haskell/Parameterized/EffectMonad/Polymonad.agda

only-supermonads:
	# Super Monads
	$(AGDA_TC) $(SOURCE_DIR)/Supermonad/Definition.agda
	$(AGDA_TC) $(SOURCE_DIR)/Supermonad/Monad.agda
	$(AGDA_TC) $(SOURCE_DIR)/Supermonad/IxMonad.agda
	$(AGDA_TC) $(SOURCE_DIR)/Supermonad/EffectMonad.agda
	$(AGDA_TC) $(SOURCE_DIR)/Supermonad/ConstrainedMonad.agda
	# $(AGDA_TC) Supermonad/Polymonad.agda
	$(AGDA_TC) $(SOURCE_DIR)/Supermonad/DefinitionWithCategory.agda
	$(AGDA_TC) $(SOURCE_DIR)/Supermonad/DefinitionWithCategory/SubsetOfDefinition.agda

only-cat-theory:
	$(AGDA_TC) $(SOURCE_DIR)/Theory/Triple.agda
	$(AGDA_TC) $(SOURCE_DIR)/Theory/ProofIrrelevance.agda
	$(AGDA_TC) $(SOURCE_DIR)/Theory/Category.agda
	$(AGDA_TC) $(SOURCE_DIR)/Theory/Isomorphism.agda
	$(AGDA_TC) $(SOURCE_DIR)/Theory/Subcategory.agda
	$(AGDA_TC) $(SOURCE_DIR)/Theory/Functor.agda
	$(AGDA_TC) $(SOURCE_DIR)/Theory/ConstrainedFunctor.agda
	$(AGDA_TC) $(SOURCE_DIR)/Theory/NaturalTransformation.agda
	$(AGDA_TC) $(SOURCE_DIR)/Theory/NaturalTransformation/Whisker.agda
	$(AGDA_TC) $(SOURCE_DIR)/Theory/NaturalIsomorphism.agda
	$(AGDA_TC) $(SOURCE_DIR)/Theory/DinaturalTransformation.agda
	$(AGDA_TC) $(SOURCE_DIR)/Theory/MonoidalCategory.agda
	$(AGDA_TC) $(SOURCE_DIR)/Theory/MonoidalFunctor.agda
	$(AGDA_TC) $(SOURCE_DIR)/Theory/Monad.agda
	$(AGDA_TC) $(SOURCE_DIR)/Theory/AtkeyParameterizedMonad.agda
	$(AGDA_TC) $(SOURCE_DIR)/Theory/Kleisli.agda
	$(AGDA_TC) $(SOURCE_DIR)/Theory/RelativeMonad.agda
	$(AGDA_TC) $(SOURCE_DIR)/Theory/Monoid.agda
	$(AGDA_TC) $(SOURCE_DIR)/Theory/Preorder.agda
	$(AGDA_TC) $(SOURCE_DIR)/Theory/TwoCategory.agda
	$(AGDA_TC) $(SOURCE_DIR)/Theory/TwoFunctor.agda
	$(AGDA_TC) $(SOURCE_DIR)/Theory/Examples/Category.agda
	$(AGDA_TC) $(SOURCE_DIR)/Theory/Examples/Subcategory.agda
	$(AGDA_TC) $(SOURCE_DIR)/Theory/Examples/Functor.agda
	$(AGDA_TC) $(SOURCE_DIR)/Theory/Examples/TwoCategory.agda
	# Haskell Examples
	$(AGDA_TC) $(SOURCE_DIR)/Theory/Examples/Haskell/FunctorEndomorphisms.agda
	$(AGDA_TC) $(SOURCE_DIR)/Theory/Examples/Haskell/FunctorSet/Base.agda
	$(AGDA_TC) $(SOURCE_DIR)/Theory/Examples/Haskell/FunctorSet/Nub.agda
	$(AGDA_TC) $(SOURCE_DIR)/Theory/Examples/Haskell/FunctorSet/Sort.agda
	$(AGDA_TC) $(SOURCE_DIR)/Theory/Examples/Haskell/FunctorSet/NubAndSort.agda
	# $(AGDA_TC) $(SOURCE_DIR)/Theory/Examples/Haskell/FunctorSet/ListMap.agda # Discontinued approach
	$(AGDA_TC) $(SOURCE_DIR)/Theory/Examples/Haskell/FunctorMonotonicSet.agda
	# Functor (Categorical) <===> Functor (Haskell)
	$(AGDA_TC) $(SOURCE_DIR)/Theory/Examples/FunctorToHaskellFunctor.agda
	$(AGDA_TC) $(SOURCE_DIR)/Theory/Examples/HaskellFunctorToFunctor.agda
	# Monad (Categorical) <===> Monad (Haskell)
	$(AGDA_TC) $(SOURCE_DIR)/Theory/Examples/MonadToHaskellMonad.agda
	$(AGDA_TC) $(SOURCE_DIR)/Theory/Examples/HaskellMonadToMonad.agda
	# Lax 2-Functor <===> Monad (Categorical)
	$(AGDA_TC) $(SOURCE_DIR)/Theory/Examples/MonadToTwoFunctor.agda
	$(AGDA_TC) $(SOURCE_DIR)/Theory/Examples/TwoFunctorToMonad.agda
	# Lax 2-Functor <===> Atkey Parameterized Monad
	$(AGDA_TC) $(SOURCE_DIR)/Theory/Examples/AtkeyParameterizedMonadToTwoFunctor.agda
	# $(AGDA_TC) $(SOURCE_DIR)/Theory/Examples/TwoFunctorToAtkeyParameterizedMonad.agda
	# IxMonad <===> Atkey Parameterized Monad
	$(AGDA_TC) $(SOURCE_DIR)/Theory/Examples/AtkeyParameterizedMonadToIxMonad.agda
	# $(AGDA_TC) $(SOURCE_DIR)/Theory/Examples/IxMonadToAtkeyParameterizedMonad.agda

clean:
	$(REMOVE) `find $(SOURCE_DIR) -type f -name "*.agdai" | tr "\n" " "`
	$(REMOVE) `find $(SOURCE_DIR) -type f -name "*.agda~" | tr "\n" " "`
