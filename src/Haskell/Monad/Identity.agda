 
module Haskell.Monad.Identity where

-- Stdlib
open import Function
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Local
open import Utilities
open import Haskell
open import Haskell.Functor
open import Haskell.Applicative
open import Haskell.Monad
open import Identity

open Functor
open Applicative hiding ( fmap )

monadId : Monad Identity
monadId = record
  { _>>=_ = _>>=_
  ; return = return
  ; applicative = applicative
  ; law-right-id = law-right-id
  ; law-left-id = law-left-id
  ; law-assoc = law-assoc
  ; law-monad-fmap = law-monad-fmap
  } where
    _>>=_ : ∀ {α β : Type} → Identity α → (α → Identity β) → Identity β
    _>>=_ = bindId
    
    return : ∀ {α : Type} → α → Identity α
    return = identity
    
    law-left-id : ∀ {α β : Type} 
           → (a : α) → (k : α → Identity β) 
           → return a >>= k ≡ k a
    law-left-id a k = refl
    
    law-right-id : ∀ {α : Type} 
           → (m : Identity α)
           → m >>= return ≡ m
    law-right-id m = refl
    
    law-assoc : ∀ {α β γ : Type} 
             → (m : Identity α) → (k : α → Identity β) → (h : β → Identity γ) 
             → m >>= (λ x → k x >>= h) ≡ (m >>= k) >>= h
    law-assoc m k h = refl

    fmapId : ∀ {α β : Type} → (α → β) → Identity α → Identity β
    fmapId f ma = ma >>= (return ∘ f)
    
    apId : ∀ {α β : Type} → Identity (α → β) → Identity α → Identity β
    apId mf ma = mf >>= λ f → ma >>= λ a → return (f a)
    
    functorId : Functor Identity
    functorId = record 
      { fmap = fmapId
      ; law-id = λ {α} → refl 
      ; law-compose = λ {α} {β} {γ} f g → refl }

    applicative : Applicative Identity
    applicative = record
      { pure = return
      ; _<*>_ = apId
      ; functor = functorId
      ; law-id = λ {α} v → refl
      ; law-composition = λ {α} {β} {γ} u v w → refl
      ; law-homomorphism = λ x f → refl
      ; law-interchange = λ {α} {β} u x → refl
      ; law-applicative-fmap = λ {α} {β} f x → refl
      }

    law-monad-fmap : ∀ {α β : Type} 
                 → (f : α → β) → (x : Identity α) 
                 → fmap (functor applicative) f x ≡ x >>= (return ∘ f)
    law-monad-fmap f x = refl
