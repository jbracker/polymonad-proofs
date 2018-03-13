
open import Level

open import Bijection renaming ( refl to brefl ; sym to bsym ; trans to btrans )

open import Theory.Category.Definition
open import Theory.Category.Examples.Discrete renaming ( discreteCategory to Disc )
open import Theory.Category.Examples.Codiscrete renaming ( codiscreteCategory to Codisc )
open import Theory.Monad.Atkey
open import Theory.TwoCategory.Examples.Functor
open import Theory.TwoCategory.Examples.DiscreteHomCat
open import Theory.TwoFunctor.ConstZeroCell
open import Theory.TwoFunctor.Properties.IsomorphicIndexedMonad

open import Theory.Haskell.Parameterized.Indexed.Monad.Properties.IsomorphicAtkeyParameterizedMonad

module Theory.TwoFunctor.Properties.IsomorphicAtkeyParameterizedMonad
  {ℓC₀ ℓC₁ ℓI : Level}
  {C : Category {ℓC₀} {ℓC₁}} {I : Set ℓI}
  where

open Category

private
  _∘I_ = _∘_ (Codisc I)

LaxTwoFunctor↔AtkeyParameterizedMonad : ConstLaxTwoFunctor (discreteHomCatTwoCategory (Codisc I)) (Cat {ℓC₀} {ℓC₁}) C ↔ AtkeyParameterizedMonad C (Disc I)
LaxTwoFunctor↔AtkeyParameterizedMonad = btrans LaxTwoFunctor↔IndexedMonad IndexedMonad↔AtkeyParameterizedMonad

AtkeyParameterizedMonad↔LaxTwoFunctor : AtkeyParameterizedMonad C (Disc I) ↔ ConstLaxTwoFunctor (discreteHomCatTwoCategory (Codisc I)) (Cat {ℓC₀} {ℓC₁}) C
AtkeyParameterizedMonad↔LaxTwoFunctor = bsym LaxTwoFunctor↔AtkeyParameterizedMonad
