 
module Monad.Maybe where

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


data Maybe (α : Type) : Type where
  Just : α → Maybe α
  Nothing : Maybe α

bindMaybe : [ Maybe , Maybe ]▷ Maybe
bindMaybe (Just x) f = f x
bindMaybe Nothing f = Nothing

monadMaybe : Monad Maybe
monadMaybe = record
  { _>>=_ = _>>=_
  ; return = return
  ; lawIdR = lawIdR
  ; lawIdL = lawIdL
  ; lawAssoc = lawAssoc
  } where
    _>>=_ : ∀ {α β : Type} → Maybe α → (α → Maybe β) → Maybe β
    _>>=_ = bindMaybe
    
    return : ∀ {α : Type} → α → Maybe α
    return = Just
    
    lawIdR : ∀ {α β : Type} 
           → (a : α) → (k : α → Maybe β) 
           → return a >>= k ≡ k a
    lawIdR a k = refl
    
    lawIdL : ∀ {α : Type} 
           → (m : Maybe α)
           → m >>= return ≡ m
    lawIdL (Just x) = refl
    lawIdL Nothing = refl
    
    lawAssoc : ∀ {α β γ : Type} 
             → (m : Maybe α) → (k : α → Maybe β) → (h : β → Maybe γ) 
             → m >>= (λ x → k x >>= h) ≡ (m >>= k) >>= h
    lawAssoc (Just x) k h = refl
    lawAssoc Nothing k h = refl
