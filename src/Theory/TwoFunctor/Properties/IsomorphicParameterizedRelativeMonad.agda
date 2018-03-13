
open import Level

open import Data.Product

open import Bijection renaming ( refl to brefl ; sym to bsym ; trans to btrans )
open import Theory.Category.Definition
open import Theory.Functor.Definition
open import Theory.TwoCategory.Examples.Functor
open import Theory.TwoCategory.Examples.DiscreteHomCat
open import Theory.TwoFunctor.ConstZeroCell

open import Theory.Haskell.Parameterized.Indexed.Monad
open import Theory.Haskell.Parameterized.Relative.Monad

open import Theory.TwoFunctor.Properties.IsomorphicIndexedMonad
open import Theory.Haskell.Parameterized.Relative.Monad.Properties.IsomorphicIndexedMonad

module Theory.TwoFunctor.Properties.IsomorphicParameterizedRelativeMonad 
  {ℓC₀ ℓC₁ ℓI₀ ℓI₁ : Level}
  {C : Category {ℓC₀} {ℓC₁}} {I : Category {ℓI₀} {ℓI₁}}where

open Category

LaxTwoFunctor↔ParameterizedRelativeMonad 
  : (ConstLaxTwoFunctor (discreteHomCatTwoCategory I) (Cat {ℓC₀} {ℓC₁}) C)
  ↔ Σ ({i j : Obj I} → Hom I i j → Obj C → Obj C) (λ F → ParameterizedRelativeMonad I F Id[ C ])
LaxTwoFunctor↔ParameterizedRelativeMonad = btrans LaxTwoFunctor↔IndexedMonad IndexedMonad↔ParameterizedRelativeMonad

ParameterizedRelativeMonad↔LaxTwoFunctor
  : Σ ({i j : Obj I} → Hom I i j → Obj C → Obj C) (λ F → ParameterizedRelativeMonad I F Id[ C ])
  ↔ (ConstLaxTwoFunctor (discreteHomCatTwoCategory I) (Cat {ℓC₀} {ℓC₁}) C)
ParameterizedRelativeMonad↔LaxTwoFunctor = bsym LaxTwoFunctor↔ParameterizedRelativeMonad
