
open import Level

open import Data.Product


open import Bijection renaming ( refl to brefl ; sym to bsym ; trans to btrans )

open import Theory.Monoid
open import Theory.Category.Definition
open import Theory.Category.Examples.Monoid renaming ( monoidCategory to MonCat )
open import Theory.Functor.Definition
open import Theory.Haskell.Parameterized.Graded.Monad
open import Theory.Haskell.Parameterized.Indexed.Monad
open import Theory.TwoCategory.Examples.Monoid renaming ( monoidTwoCategory to MonTwoCat )
open import Theory.TwoFunctor.Properties.IsomorphicIndexedMonad
open import Theory.TwoFunctor.Properties.IsomorphicGradedMonad

module Theory.Haskell.Parameterized.Indexed.Monad.Properties.IsomorphicGradedMonad where

open Category

IndexedMonad↔GradedMonad : {ℓMon ℓC₀ ℓC₁ : Level}
                         → {Mon : Set ℓMon}
                         → (monoid : Monoid Mon)
                         → {C : Category {ℓC₀} {ℓC₁}} 
                         → (Σ ({i j : Obj (MonCat monoid)} → Hom (MonCat monoid) i j → Functor C C) (IndexedMonad (MonCat monoid))) 
                         ↔ (Σ (Mon → Functor C C) (GradedMonad monoid))
IndexedMonad↔GradedMonad {ℓMon} {ℓC₀} {ℓC₁} {Mon} monoid {C} = 
  btrans (IndexedMonad↔LaxTwoFunctor {I = MonCat monoid} {C = C}) (bsym (GradedMonad↔ConstLaxTwoFunctor C monoid))
