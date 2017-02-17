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

-- Associate the triple to the right with standard tuples/products
assocTripleR : {ℓ₀ ℓ₁ ℓ₂ : Level} {A : Set ℓ₀} {B : Set ℓ₁} {C : Set ℓ₂} 
       → A × B × C → A ×' (B ×' C)
assocTripleR (a , b , c) = a ,' (b ,' c)

-- Associate the triple to the left with standard tuples/products
assocTripleL : {ℓ₀ ℓ₁ ℓ₂ : Level} {A : Set ℓ₀} {B : Set ℓ₁} {C : Set ℓ₂} 
       → A × B × C → (A ×' B) ×' C
assocTripleL (a , b , c) = (a ,' b) ,' c
