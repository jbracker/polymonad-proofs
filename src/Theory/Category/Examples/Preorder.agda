
-- Stdlib
open import Level

open import Relation.Binary using ( Preorder )
open import Relation.Binary.PropositionalEquality

--open import Utilities
open import Extensionality
open import ProofIrrelevance
open import Theory.Category.Definition

module Theory.Category.Examples.Preorder where 

-- Category formed by a preorder
preorderCategory : {ℓC ℓEq ℓOrd : Level} 
                 → (P : Preorder ℓC ℓEq ℓOrd) 
                 → ((a b : Preorder.Carrier P) → ProofIrrelevance (Preorder._∼_ P a b))
                 → Category
preorderCategory P proof-irr-≤ = record
  { Obj = Preorder.Carrier P
  ; Hom = _≤_
  ; _∘_ = _∘_
  ; id = id
  ; assoc = assoc
  ; left-id = left-id
  ; right-id = right-id
  } where
    _≤_ = Preorder._∼_ P
    id = Preorder.refl P
    ptrans = Preorder.trans P
    
    _∘_ : {a b c : Preorder.Carrier P} → b ≤ c → a ≤ b → a ≤ c
    _∘_ b≤c a≤b = Preorder.trans P a≤b b≤c

    abstract
      assoc : {a b c d : Preorder.Carrier P} {f : a ≤ b} {g : b ≤ c} {h : c ≤ d} 
            → h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f
      assoc {a} {b} {c} {d} {f} {g} {h} = proof-irr-≤ a d (ptrans (ptrans f g) h) (ptrans f (ptrans g h))

    abstract
      right-id : {a b : Preorder.Carrier P} {f : a ≤ b} → id ∘ f ≡ f
      right-id {a} {b} {f} = proof-irr-≤ a b (ptrans f id) f

    abstract
      left-id : {a b : Preorder.Carrier P} {f : a ≤ b} → f ∘ id ≡ f
      left-id {a} {b} {f} = proof-irr-≤ a b (ptrans id f) f
 
