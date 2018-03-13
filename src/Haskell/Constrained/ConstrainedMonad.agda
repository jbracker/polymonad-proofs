 
module Haskell.Constrained.ConstrainedMonad where

open import Agda.Primitive
open import Function
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Utilities
open import Haskell
open import Haskell.Constrained.ConstrainedFunctor

open ConstrainedFunctor

record ConstrainedMonad {ℓ : Level} (M : TyCon) : Set (lsuc ℓ) where
  field
    BindCts : Type → Type → Set ℓ
    ReturnCts : Type → Set ℓ
    
    bind : ∀ {α β : Type} → BindCts α β → ( M α → (α → M β) → M β )
    return : ∀ {α : Type} → ReturnCts α → ( α → M α )
    
    functor : ConstrainedFunctor {ℓ = ℓ} M
    
    law-right-id : ∀ {α β : Type}
           → (bcts : BindCts α β) → (rcts : ReturnCts α)
           → (a : α) → (k : α → M β) 
           → (bind bcts) (return rcts a) k ≡ k a
    law-left-id : ∀ {α : Type}
           → (bcts : BindCts α α) → (rcts : ReturnCts α)
           → (m : M α)
           → (bind bcts) m (return rcts) ≡ m
    law-assoc : ∀ {α β γ : Type}
             → (cts-αγ : BindCts α γ)
             → (cts-βγ : BindCts β γ)
             → (cts-αβ : BindCts α β)
             → (m : M α) → (k : α → M β) → (h : β → M γ)
             → (bind cts-αγ) m (λ x → (bind cts-βγ) (k x) h) ≡ (bind cts-βγ) ((bind cts-αβ) m k) h
    
    law-monad-fmap : ∀ {α β : Type}
                 → (fcts : FunctorCts functor α β)
                 → (bcts : BindCts α β)
                 → (rcts : ReturnCts β)
                 → (f : α → β) → (x : M α) 
                 → fmap functor fcts f x ≡ (bind bcts) x ((return rcts) ∘ f)
    
    lawUniqueBindCts : {α β : Type} → (b₁ b₂ : BindCts α β) → b₁ ≡ b₂
    lawUniqueReturnCts : {α : Type} → (r₁ r₂ : ReturnCts α) → r₁ ≡ r₂
    
  sequence : ∀ {α β : Type} → BindCts α β → M α → M β → M β
  sequence cts ma mb = (bind cts) ma (λ _ → mb)
   
