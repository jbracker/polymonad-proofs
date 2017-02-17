module Haskell.Functor where

open import Function
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Utilities
open import Haskell 
open import Identity

record Functor (F : TyCon) : Set₁ where
  field
    fmap : ∀ {α β : Type} → (α → β) → (F α → F β)
    
    lawId  : ∀ {α : Type} → fmap {α = α} identity ≡ identity
    lawCompose : ∀ {α β γ : Type} 
               → (f : β → γ) → (g : α → β) 
               → fmap (f ∘ g) ≡ fmap f ∘ fmap g

functorFromMonad : ∀ {M : TyCon}
                 → (_>>=_ : [ M , M ]▷ M)
                 → (return : ∀ {α : Type} → α → M α)
                 → (lawIdL : ∀ {α : Type} 
                           → (m : M α)
                           → m >>= return ≡ m)
                 → (lawIdR : ∀ {α β : Type} 
                           → (a : α) → (k : α → M β) 
                           → return a >>= k ≡ k a)
                 → (lawAssoc : ∀ {α β γ : Type} 
                             → (m : M α) → (k : α → M β) → (h : β → M γ)
                             → m >>= (λ x → k x >>= h) ≡ (m >>= k) >>= h)
                 → Functor M
functorFromMonad {M = M} _>>=_ return lawIdL lawIdR lawAssoc = record 
  { fmap = fmap 
  ; lawId = lawId 
  ; lawCompose = lawCompose
  } where
    fmap : ∀ {α β : Type} → (α → β) → M α → M β
    fmap f x = x >>= (return ∘ f)

    lawId : ∀ {α : Type} → fmap {α = α} identity ≡ identity
    lawId = funExt (λ ma → begin
      fmap identity ma 
        ≡⟨ refl ⟩
      ma >>= return
        ≡⟨ lawIdL ma ⟩
      identity ma ∎)
    
    lawCompose : ∀ {α β γ : Type} 
            → (f : β → γ) → (g : α → β) 
            → fmap (f ∘ g) ≡ fmap f ∘ fmap g
    lawCompose f g = funExt (λ ma → begin 
      fmap (f ∘ g) ma
        ≡⟨ refl ⟩
      ma >>= (λ x → return (f (g x)))
        ≡⟨ cong (λ X → ma >>= X) (funExt (λ x → sym (lawIdR (g x) (return ∘ f)))) ⟩
      ma >>= (λ x → return (g x) >>= (return ∘ f))
        ≡⟨ lawAssoc ma (return ∘ g) (return ∘ f) ⟩
      (ma >>= (return ∘ g)) >>= (return ∘ f)
        ≡⟨ refl ⟩
      (fmap f ∘ fmap g) ma ∎)
