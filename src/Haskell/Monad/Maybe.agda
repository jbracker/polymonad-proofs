 
module Haskell.Monad.Maybe where

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
open import Haskell.Applicative
open import Haskell.Monad
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
  ; applicative = applicativeFromMonad _>>=_ return law-right-id law-left-id law-assoc
  ; law-right-id = law-right-id
  ; law-left-id = law-left-id
  ; law-assoc = law-assoc
  ; law-monad-fmap = λ f x → refl
  } where
    _>>=_ : ∀ {α β : Type} → Maybe α → (α → Maybe β) → Maybe β
    _>>=_ = bindMaybe
    
    return : ∀ {α : Type} → α → Maybe α
    return = Just
    
    law-left-id : ∀ {α β : Type} 
           → (a : α) → (k : α → Maybe β) 
           → return a >>= k ≡ k a
    law-left-id a k = refl
    
    law-right-id : ∀ {α : Type} 
           → (m : Maybe α)
           → m >>= return ≡ m
    law-right-id (Just x) = refl
    law-right-id Nothing = refl
    
    law-assoc : ∀ {α β γ : Type} 
             → (m : Maybe α) → (k : α → Maybe β) → (h : β → Maybe γ) 
             → m >>= (λ x → k x >>= h) ≡ (m >>= k) >>= h
    law-assoc (Just x) k h = refl
    law-assoc Nothing k h = refl
