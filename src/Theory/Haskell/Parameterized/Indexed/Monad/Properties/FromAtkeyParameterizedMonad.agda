
open import Level
open import Function hiding ( id ; _∘_ )

open import Data.Product

open import Relation.Binary.HeterogeneousEquality renaming ( refl to hrefl ; sym to hsym ; trans to htrans ; cong to hcong )

open import Bijection renaming ( refl to brefl ; sym to bsym ; trans to btrans )

open import Theory.Category.Definition
open import Theory.Category.Examples.Discrete renaming ( discreteCategory to Disc )
open import Theory.Category.Examples.Codiscrete renaming ( codiscreteCategory to Codisc )
open import Theory.Functor.Definition
open import Theory.Monad.Atkey
open import Theory.Haskell.Parameterized.Indexed.Monad

module Theory.Haskell.Parameterized.Indexed.Monad.Properties.FromAtkeyParameterizedMonad
  {ℓC₀ ℓC₁ ℓI : Level}
  {C : Category {ℓC₀} {ℓC₁}} {I : Set ℓI}
  where

open Category

AtkeyParameterizedMonad→IndexedMonad
  : AtkeyParameterizedMonad C (Disc I)
  → (Σ ({i j : I} → Hom (Codisc I) i j → Functor C C) (IndexedMonad (Codisc I))) 
AtkeyParameterizedMonad→IndexedMonad APM =
  (λ {i j} f → natTransAtkeyFunctor j i T) ,
  indexedMonad (λ i → NatTrans-η i)
               (λ {i j k} f g → NatTrans-μ k j i)
               (λ {i j k l} {f} {g} → ≡-to-≅ $ AtkeyParameterizedMonad.assoc APM)
               (λ {i j} {f} {x} → ≡-to-≅ $ AtkeyParameterizedMonad.left-id APM)
               (λ {i j} {f} {x} → ≡-to-≅ $ AtkeyParameterizedMonad.right-id APM)
  where
    open AtkeyParameterizedMonad APM
    
