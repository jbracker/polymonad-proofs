
-- Stdlib
open import Level

open import Relation.Binary.PropositionalEquality

open import Theory.Category.Definition

module Theory.Category.Examples.Discrete where  

-- Category that only has identity morphisms.
discreteCategory : {ℓ₀ : Level} → (A : Set ℓ₀) → Category {ℓ₀} {ℓ₀}
discreteCategory {ℓ₀} A = category A (λ a b → a ≡ b) comp (λ {a} → refl) assoc left-id right-id
  where
    comp : {a b c : A} → b ≡ c → a ≡ b → a ≡ c
    comp refl refl = refl
    
    assoc : {a b c d : A} {f : a ≡ b} {g : b ≡ c} {h : c ≡ d}
          → comp h (comp g f) ≡ comp (comp h g) f
    assoc {f = refl} {refl} {refl} = refl
    
    left-id : {a b : A} {f : a ≡ b} → comp refl f ≡ f
    left-id {f = refl} = refl
    
    right-id : {a b : A} {f : a ≡ b} → comp f refl ≡ f
    right-id {f = refl} = refl
