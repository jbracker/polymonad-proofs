
open import Level

open import Data.Product


open import Bijection renaming ( refl to brefl ; sym to bsym ; trans to btrans )

open import Theory.Category.Definition
open import Theory.Category.Examples.Discrete renaming ( discreteCategory to Disc )
open import Theory.Category.Examples.Codiscrete renaming ( codiscreteCategory to Codisc )
open import Theory.Functor.Definition
open import Theory.Monad.Atkey
open import Theory.Haskell.Parameterized.Indexed.Monad

module Theory.Haskell.Parameterized.Indexed.Monad.Properties.IsomorphicAtkeyParameterizedMonad
  {ℓC₀ ℓC₁ ℓI : Level}
  {C : Category {ℓC₀} {ℓC₁}} {I : Set ℓI}
  where

open Category

IndexedMonad↔AtkeyParameterizedMonad 
  : (Σ ({i j : I} → Hom (Codisc I) i j → Functor C C) (IndexedMonad (Codisc I))) 
  ↔ AtkeyParameterizedMonad C (Disc I)
IndexedMonad↔AtkeyParameterizedMonad = bijection {!!} {!!} {!!} {!!}
