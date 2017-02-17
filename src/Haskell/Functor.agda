module Haskell.Functor where

open import Function
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Extensionality
open import Haskell 
open import Identity

record Functor (F : TyCon) : Set₁ where
  field
    fmap : ∀ {α β : Type} → (α → β) → (F α → F β)
    
    law-id  : ∀ {α : Type} → fmap {α = α} identity ≡ identity
    law-compose : ∀ {α β γ : Type} 
               → (f : β → γ) → (g : α → β) 
               → fmap (f ∘ g) ≡ fmap f ∘ fmap g

functorFromMonad : ∀ {M : TyCon}
                 → (_>>=_ : [ M , M ]▷ M)
                 → (return : ∀ {α : Type} → α → M α)
                 → (law-left-id : ∀ {α : Type} 
                                → (m : M α)
                                → m >>= return ≡ m)
                 → (law-right-id : ∀ {α β : Type} 
                           → (a : α) → (k : α → M β) 
                           → return a >>= k ≡ k a)
                 → (law-assoc : ∀ {α β γ : Type} 
                             → (m : M α) → (k : α → M β) → (h : β → M γ)
                             → m >>= (λ x → k x >>= h) ≡ (m >>= k) >>= h)
                 → Functor M
functorFromMonad {M = M} _>>=_ return law-left-id law-right-id law-assoc = record 
  { fmap = fmap 
  ; law-id = law-id 
  ; law-compose = law-compose
  } where
    fmap : ∀ {α β : Type} → (α → β) → M α → M β
    fmap f x = x >>= (return ∘ f)

    law-id : ∀ {α : Type} → fmap {α = α} identity ≡ identity
    law-id = fun-ext (λ ma → begin
      fmap identity ma 
        ≡⟨ refl ⟩
      ma >>= return
        ≡⟨ law-left-id ma ⟩
      identity ma ∎)
    
    law-compose : ∀ {α β γ : Type} 
            → (f : β → γ) → (g : α → β) 
            → fmap (f ∘ g) ≡ fmap f ∘ fmap g
    law-compose f g = fun-ext (λ ma → begin 
      fmap (f ∘ g) ma
        ≡⟨ refl ⟩
      ma >>= (λ x → return (f (g x)))
        ≡⟨ cong (λ X → ma >>= X) (fun-ext (λ x → sym (law-right-id (g x) (return ∘ f)))) ⟩
      ma >>= (λ x → return (g x) >>= (return ∘ f))
        ≡⟨ law-assoc ma (return ∘ g) (return ∘ f) ⟩
      (ma >>= (return ∘ g)) >>= (return ∘ f)
        ≡⟨ refl ⟩
      (fmap f ∘ fmap g) ma ∎)
