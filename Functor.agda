module Functor where

open import Function
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Utilities
open import Polymonad
open import Haskell 
open import Identity

record Functor (F : TyCon) : Set₁ where
  field
    fmap : ∀ {α β : Type} → (α → β) → (F α → F β)
    
    lawId  : ∀ {α : Type} → fmap {α = α} identity ≡ identity
    lawDist : ∀ {α β γ : Type} 
            → (f : β → γ) → (g : α → β) 
            → fmap (f ∘ g) ≡ fmap f ∘ fmap g
