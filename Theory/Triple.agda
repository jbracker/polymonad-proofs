-- A special type for triples.
module Theory.Triple where

open import Level
open import Data.Product renaming ( _×_ to _×'_ ; _,_ to _,'_ ; proj₁ to proj₁' ; proj₂ to proj₂' )

-- The obvious definition of a Triple.
record Triple {ℓ₀ ℓ₁ ℓ₂ : Level} (A : Set ℓ₀) (B : Set ℓ₁) (C : Set ℓ₂) : Set (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂) where
  constructor _,_,_
  field
    proj₁ : A
    proj₂ : B
    proj₃ : C

-- A nice way to write the triple type
_×_×_ = Triple

-- Split the triple on the left side to compose it out of standard tuples/products
splitL : {ℓ₀ ℓ₁ ℓ₂ : Level} {A : Set ℓ₀} {B : Set ℓ₁} {C : Set ℓ₂} 
       → A × B × C → A ×' (B ×' C)
splitL (a , b , c) = a ,' (b ,' c)

-- Split the triple on the right side to compuse it out of standard tuples/products
splitR : {ℓ₀ ℓ₁ ℓ₂ : Level} {A : Set ℓ₀} {B : Set ℓ₁} {C : Set ℓ₂} 
       → A × B × C → (A ×' B) ×' C
splitR (a , b , c) = (a ,' b) ,' c
