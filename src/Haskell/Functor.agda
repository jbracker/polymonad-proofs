module Haskell.Functor where

open import Function
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Extensionality
open import Haskell 
open import Identity

record Functor (F : TyCon) : Set₁ where
  constructor functor
  
  field
    fmap : ∀ {α β : Type} → (α → β) → (F α → F β)
    
    law-id  : ∀ {α : Type} → fmap {α = α} identity ≡ identity
    law-compose : ∀ {α β γ : Type} 
               → (f : β → γ) → (g : α → β) 
               → fmap (f ∘ g) ≡ fmap f ∘ fmap g

functor-eq : {F : TyCon}
           → {fmap₀ : ∀ {α β : Type} → (α → β) → (F α → F β)}
           → {fmap₁ : ∀ {α β : Type} → (α → β) → (F α → F β)}
           → {law-id₀ : ∀ {α : Type} → fmap₀ {α = α} identity ≡ identity}
           → {law-id₁ : ∀ {α : Type} → fmap₁ {α = α} identity ≡ identity}
           → {law-compose₀ : ∀ {α β γ : Type} → (f : β → γ) → (g : α → β) → fmap₀ (f ∘ g) ≡ fmap₀ f ∘ fmap₀ g}
           → {law-compose₁ : ∀ {α β γ : Type} → (f : β → γ) → (g : α → β) → fmap₁ (f ∘ g) ≡ fmap₁ f ∘ fmap₁ g}
           → (λ {α} {β} → fmap₀ {α} {β}) ≡ fmap₁
           → functor fmap₀ law-id₀ law-compose₀ ≡ functor fmap₁ law-id₁ law-compose₁
functor-eq {F} {fmap} {._} {i₀} {i₁} {c₀} {c₁} refl = cong₂ (functor fmap) p1 p2
  where
    p1 : (λ {α} → i₀ {α}) ≡ i₁
    p1 = implicit-fun-ext 
       $ λ α → proof-irrelevance (i₀ {α}) (i₁ {α})
    
    p2 : (λ {α} {β} {γ} → c₀ {α} {β} {γ}) ≡ c₁
    p2 = implicit-fun-ext 
       $ λ α → implicit-fun-ext 
       $ λ β → implicit-fun-ext 
       $ λ γ → fun-ext 
       $ λ f → fun-ext 
       $ λ g → proof-irrelevance (c₀ {α} {β} {γ} f g) (c₁ {α} {β} {γ} f g)


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
