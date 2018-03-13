
module Haskell.Constrained.ConstrainedFunctor where

open import Agda.Primitive
open import Level
open import Data.Unit.Base
open import Function
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Utilities
open import Haskell 
open import Identity
open import Haskell.Functor hiding ( functor )

record ConstrainedFunctor {ℓ : Level} (F : TyCon) : Set (lsuc ℓ) where
  field
    FunctorCts : Type → Type → Set ℓ

    fmap : ∀ {α β : Type} → FunctorCts α β → ( (α → β) → (F α → F β) )
    
    law-id  : ∀ {α : Type} → (cts : FunctorCts α α) → fmap {α = α} cts identity ≡ identity
    law-compose : ∀ {α β γ : Type} 
               → (cts-αγ : FunctorCts α γ)
               → (cts-αβ : FunctorCts α β)
               → (cts-βγ : FunctorCts β γ)
               → (f : β → γ) → (g : α → β) 
               → fmap cts-αγ (f ∘ g) ≡ fmap cts-βγ f ∘ fmap cts-αβ g 

Functor→ConstrainedFunctor : ∀ {ℓ} → (F : TyCon) → Functor F → ConstrainedFunctor {ℓ = ℓ} F
Functor→ConstrainedFunctor {ℓ} F functor = record 
  { FunctorCts = FunctorCts 
  ; fmap = fmap 
  ; law-id = law-id 
  ; law-compose = law-compose
  } where
    FunctorCts : Type → Type → Set ℓ
    FunctorCts _ _ = Lift ⊤
    
    fmap : ∀ {α β : Type} → FunctorCts α β → (α → β) → (F α → F β)
    fmap (lift tt) f ma = Functor.fmap functor f ma
    
    law-id  : ∀ {α : Type} → (cts : FunctorCts α α) 
           → fmap {α = α} cts identity ≡ identity
    law-id (lift tt) = Functor.law-id functor
    
    law-compose : ∀ {α β γ : Type} 
               → (cts-αγ : FunctorCts α γ)
               → (cts-αβ : FunctorCts α β)
               → (cts-βγ : FunctorCts β γ)
               → (f : β → γ) → (g : α → β) 
               → fmap cts-αγ (f ∘ g) ≡ fmap cts-βγ f ∘ fmap cts-αβ g 
    law-compose (lift tt) (lift tt) (lift tt) f g = Functor.law-compose functor f g
