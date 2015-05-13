 
module Monad.Identity where

-- Stdlib
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Local
open import Utilities
open import Haskell
open import Monad
open import Identity

monadId : Monad Identity
monadId = record
  { _>>=_ = _>>=_
  ; return = return
  ; lawIdR = lawIdR
  ; lawIdL = lawIdL
  ; lawAssoc = lawAssoc
  } where
    _>>=_ : ∀ {α β : Type} → Identity α → (α → Identity β) → Identity β
    _>>=_ = bindId
    
    return : ∀ {α : Type} → α → Identity α
    return = identity
    
    lawIdR : ∀ {α β : Type} 
           → (a : α) → (k : α → Identity β) 
           → return a >>= k ≡ k a
    lawIdR a k = refl
    
    lawIdL : ∀ {α : Type} 
           → (m : Identity α)
           → m >>= return ≡ m
    lawIdL m = refl
    
    lawAssoc : ∀ {α β γ : Type} 
             → (m : Identity α) → (k : α → Identity β) → (h : β → Identity γ) 
             → m >>= (λ x → k x >>= h) ≡ (m >>= k) >>= h
    lawAssoc m k h = refl
