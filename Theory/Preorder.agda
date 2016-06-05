
module Theory.Preorder where

-- Stdlib
open import Level renaming ( suc to lsuc )
open import Data.Product
open import Data.Sum
open import Data.Unit hiding ( _≤_ )
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality renaming ( refl to eqRefl ; trans to eqTrans )
open ≡-Reasoning

-- Local
open import Theory.Category
open import Theory.ProofIrrelevance

record Preorder {ℓ : Level} (P : Set ℓ) : Set (lsuc ℓ) where
  field
    _≤_ : P → P → Set ℓ
    
    refl : {a : P} → a ≤ a
    trans : {a b c : P} → a ≤ b → b ≤ c → a ≤ c
 
  carrier : Set ℓ
  carrier = P

Preorder→Category : ∀ {ℓ} {P : Set ℓ} 
                  → (preorder : Preorder P) 
                  → ProofIrrelevance (Preorder._≤_ preorder)
                  → Category {ℓ = ℓ}
Preorder→Category {ℓ = ℓ} {P = P} preorder irrelevance = record
  { Obj = P
  ; Hom = _≤_
  ; _∘_ = _∘_
  ; id = id
  ; assoc = assoc
  ; idL = idL
  ; idR = idR
  } where
    _≤_ = Preorder._≤_ preorder
    
    id = Preorder.refl preorder
    
    _∘_ : {a b c : P} → b ≤ c → a ≤ b → a ≤ c
    _∘_ b≤c a≤b = Preorder.trans preorder a≤b b≤c
    
    assoc : ∀ {a b c d : P} {f : a ≤ b} {g : b ≤ c} {h : c ≤ d} 
          → h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f
    assoc {f = f} {g = g} {h = h} = irrelevance (h ∘ (g ∘ f)) ((h ∘ g) ∘ f)
    
    idL : ∀ {a b : P} {f : a ≤ b} → id ∘ f ≡ f
    idL {f = f} = irrelevance (id ∘ f) f

    idR : ∀ {a b : P} {f : a ≤ b} → f ∘ id ≡ f
    idR {f = f} = irrelevance (f ∘ id) f
