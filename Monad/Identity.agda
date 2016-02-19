 
module Monad.Identity where

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
open import Functor
open import Applicative
open import Monad
open import Identity

open Functor.Functor
open Applicative.Applicative

monadId : Monad Identity
monadId = record
  { _>>=_ = _>>=_
  ; return = return
  ; applicative = applicative
  ; lawIdR = lawIdR
  ; lawIdL = lawIdL
  ; lawAssoc = lawAssoc
  ; lawMonadFmap = lawMonadFmap
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

    fmapId : ∀ {α β : Type} → (α → β) → Identity α → Identity β
    fmapId f ma = ma >>= (return ∘ f)
    
    apId : ∀ {α β : Type} → Identity (α → β) → Identity α → Identity β
    apId mf ma = mf >>= λ f → ma >>= λ a → return (f a)
    
    functorId : Functor Identity
    functorId = record 
      { fmap = fmapId
      ; lawId = λ {α} → refl 
      ; lawDist = λ {α} {β} {γ} f g → refl }

    applicative : Applicative Identity
    applicative = record
      { pure = return
      ; _<*>_ = apId
      ; functor = functorId
      ; lawId = λ {α} v → refl
      ; lawComposition = λ {α} {β} {γ} u v w → refl
      ; lawHomomorphism = λ x f → refl
      ; lawInterchange = λ {α} {β} u x → refl
      ; lawApplicativeFmap = λ {α} {β} f x → refl
      }

    lawMonadFmap : ∀ {α β : Type} 
                 → (f : α → β) → (x : Identity α) 
                 → fmap (functor applicative) f x ≡ x >>= (return ∘ f)
    lawMonadFmap f x = refl
