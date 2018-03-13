
-- Stdlib
open import Level

open import Data.Unit hiding ( _≤_ )

open import Relation.Binary.PropositionalEquality

open import Theory.Category.Definition

module Theory.Category.Examples.Codiscrete where  

data CodiscreteArrow {ℓ : Level} {A : Set ℓ} : A → A → Set ℓ where
  codisc : (a : A) → (b : A) → CodiscreteArrow a b

-- Category that has exactly one morphism for any pair of objects.
codiscreteCategory : {ℓ : Level} → (A : Set ℓ) → Category {ℓ} {ℓ}
codiscreteCategory {ℓ} A = category A CodiscreteArrow comp id assoc right-id left-id
  where
    comp : {a b c : A} → CodiscreteArrow b c → CodiscreteArrow a b → CodiscreteArrow a c
    comp (codisc b c) (codisc a .b) = codisc a c
    
    id : {a : A} → CodiscreteArrow a a
    id {a} = codisc a a
    
    assoc : {a b c d : A} 
          → {f : CodiscreteArrow a b} {g : CodiscreteArrow b c} {h : CodiscreteArrow c d}
          → comp h (comp g f) ≡ comp (comp h g) f
    assoc {a} {b} {c} {d} {codisc .a .b} {codisc .b .c} {codisc .c .d} = refl
    
    right-id : {a b : A} {f : CodiscreteArrow a b} → comp id f ≡ f
    right-id {a} {b} {codisc .a .b} = refl
    
    left-id : {a b : A} {f : CodiscreteArrow a b} → comp f id ≡ f
    left-id {a} {b} {codisc .a .b} = refl
