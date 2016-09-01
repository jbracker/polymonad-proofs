
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
open import Haskell.Functor

record ConstrainedFunctor {ℓ : Level} (F : TyCon) : Set (lsuc ℓ) where
  field
    FunctorCts : Type → Type → Set ℓ

    fmap : ∀ {α β : Type} → FunctorCts α β → ( (α → β) → (F α → F β) )
    
    lawId  : ∀ {α : Type} → (cts : FunctorCts α α) → fmap {α = α} cts identity ≡ identity
    lawDist : ∀ {α β γ : Type} 
            → (cts-αγ : FunctorCts α γ)
            → (cts-αβ : FunctorCts α β)
            → (cts-βγ : FunctorCts β γ)
            → (f : β → γ) → (g : α → β) 
            → fmap cts-αγ (f ∘ g) ≡ fmap cts-βγ f ∘ fmap cts-αβ g 

Functor→ConstrainedFunctor : ∀ {ℓ} → (F : TyCon) → Functor F → ConstrainedFunctor {ℓ = ℓ} F
Functor→ConstrainedFunctor {ℓ} F functor = record 
  { FunctorCts = FunctorCts 
  ; fmap = fmap 
  ; lawId = lawId 
  ; lawDist = lawDist
  } where
    FunctorCts : Type → Type → Set ℓ
    FunctorCts _ _ = Lift ⊤
    
    fmap : ∀ {α β : Type} → FunctorCts α β → (α → β) → (F α → F β)
    fmap (lift tt) f ma = Functor.fmap functor f ma
    
    lawId  : ∀ {α : Type} → (cts : FunctorCts α α) 
           → fmap {α = α} cts identity ≡ identity
    lawId (lift tt) = Functor.lawId functor
    
    lawDist : ∀ {α β γ : Type} 
            → (cts-αγ : FunctorCts α γ)
            → (cts-αβ : FunctorCts α β)
            → (cts-βγ : FunctorCts β γ)
            → (f : β → γ) → (g : α → β) 
            → fmap cts-αγ (f ∘ g) ≡ fmap cts-βγ f ∘ fmap cts-αβ g 
    lawDist (lift tt) (lift tt) (lift tt) f g = Functor.lawDist functor f g
