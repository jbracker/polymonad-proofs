
module Theory.TwoCategory where

-- Stdlib
open import Level renaming ( suc to lsuc ; zero to lzero )
open import Function hiding ( id ) renaming ( _∘_ to _∘F_ )
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Theory.Category
open import Theory.Functor
open import Theory.NaturalTransformation
open import Theory.Examples.Functor

-- open Functor


record TwoCategory {ℓ₀ ℓ₁ ℓ₂ : Level} : Set (lsuc (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    Cell₀ : Set ℓ₀
    Cell₁ : Cell₀ → Cell₀ → Category {ℓ₁} {ℓ₂}

    compF : {a b c : Cell₀} → Functor (Cell₁ b c ×C Cell₁ a b) (Cell₁ a c) 
    idF   : {a : Cell₀} → Functor ⊤-Cat (Cell₁ a a)
    
    assoc : {a b c d : Cell₀} → NaturalTransformation (biFunctor→triFunctor₁ [ Id[ Cell₁ c d ] ]×[ Id[ Cell₁ a c ] ] (compF {a} {b} {c})) {!subst () (biFunctor→triFunctor₂ ? ?)!}
    {-
    _∘_ : {a b c : Cell₀} → Functor [ Cat (Cell₁ b c) ]×[ Cat (Cell₁ a b) ] → (Cat (Cell₁ a c))
    id : {a : Cell₀} → Cell₁ a a

    assoc : {a b c d : Cell₀} {f : Cell₁ a b} {g : Cell₁ b c} {h : Cell₁ c d} 
          → h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f
    
    idL : {a b : Cell₀} {f : Cell₁ a b} → id ∘ f ≡ f
    idR : {a b : Cell₀} {f : Cell₁ a b} → f ∘ id ≡ f
-}
