 
module SuperMonad.Laws where

-- Stdlib
open import Level
open import Function
open import Agda.Primitive
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Local
open import Utilities
open import Haskell
open import Identity
open import Functor
open import Applicative
open import Monad
open import Monad.Polymonad
open import Polymonad
open import SuperMonad.Definition 
open import SuperMonad.HaskSuperMonad

open SuperMonad {{ ... }}

p1 : ∀ {ℓ} {TyCons : Set ℓ} {α β : Type}
   → {{sm : SuperMonad TyCons}}
   → (M₁ M₂ N : TyCons)
   → (b₁ : Binds M₁ N) → (b₂ : Binds M₂ N)
   → (r₁ : Returns M₁) → (r₂ : Returns M₂)
   → (M₁◆N≡N : M₁ ◆ N ≡ N) → (M₂◆N≡N : M₂ ◆ N ≡ N)
   → (a : α) → (f : α → ⟨ N ⟩ β)
   → subst (λ X → ⟨ X ⟩ β) M₁◆N≡N (bind b₁ (return r₁ a) f) ≡ subst (λ X → ⟨ X ⟩ β) M₂◆N≡N (bind b₂ (return r₂ a) f)
p1 {β = β} M₁ M₂ N b₁ b₂ r₁ r₂ M₁◆N≡N M₂◆N≡N a f = begin
  subst (λ X → ⟨ X ⟩ β) M₁◆N≡N (bind b₁ (return r₁ a) f) 
    ≡⟨ lawIdR N M₁ M₁◆N≡N b₁ r₁ a f ⟩
  f a
    ≡⟨ sym (lawIdR N M₂ M₂◆N≡N b₂ r₂ a f) ⟩
  subst (λ X → ⟨ X ⟩ β) M₂◆N≡N (bind b₂ (return r₂ a) f) ∎

p2 : ∀ {ℓ} {TyCons : Set ℓ} {α β : Type}
   → {{sm : SuperMonad TyCons}}
   → (M₁ M₂ N : TyCons)
   → (b₁ : Binds N M₁) → (b₂ : Binds N M₂)
   → (r₁ : Returns M₁) → (r₂ : Returns M₂)
   → (N◆M₁≡N : N ◆ M₁ ≡ N) → (N◆M₂≡N : N ◆ M₂ ≡ N)
   → (m : ⟨ N ⟩ β)
   → subst (λ X → ⟨ X ⟩ β) N◆M₁≡N (bind b₁ m (return r₁)) ≡ subst (λ X → ⟨ X ⟩ β) N◆M₂≡N (bind b₂ m (return r₂))
p2 {β = β} M₁ M₂ N b₁ b₂ r₁ r₂ N◆M₁≡N N◆M₂≡N m = begin
  subst (λ X → ⟨ X ⟩ β) N◆M₁≡N (bind b₁ m (return r₁)) 
    ≡⟨ lawIdL N M₁ N◆M₁≡N b₁ r₁ m ⟩
  m
    ≡⟨ sym (lawIdL N M₂ N◆M₂≡N b₂ r₂ m) ⟩
  subst (λ X → ⟨ X ⟩ β) N◆M₂≡N (bind b₂ m (return r₂)) ∎

{-

 lawIdR : ∀ {α β : Type} 
           → (M N : TyCons)
           → (N◆M≡M : N ◆ M ≡ M )
           → (b : Binds N M) → (r : Returns N)
           → (a : α) → (k : α → ⟨ M ⟩ β)
           → subst (λ X → ⟨ X ⟩ β) N◆M≡M (bind {M = N} {N = M} b (return {M = N} r a) k) ≡ k a
    lawIdL : ∀ {α : Type} 
           → (M N : TyCons)
           → (M◆N≡M : M ◆ N ≡ M)
           → (b : Binds M N) → (r : Returns N)
           → (m : ⟨ M ⟩ α)
           → subst (λ X → ⟨ X ⟩ α) M◆N≡M (bind b m (return r)) ≡ m
    lawAssoc : ∀ {α β γ : Type} 
             → (M N P : TyCons)
             → (assoc : M ◆ (N ◆ P) ≡ (M ◆ N) ◆ P) 
             → (b₁ : Binds M (N ◆ P)) → (b₂ : Binds N P)
             → (b₃ : Binds (M ◆ N) P) → (b₄ : Binds M N)
             → (m : ⟨ M ⟩ α) → (f : α → ⟨ N ⟩ β) → (g : β → ⟨ P ⟩ γ)
             → subst (λ X → ⟨ X ⟩ γ) assoc (bind b₁ m (λ x → bind b₂ (f x) g)) 
               ≡ bind b₃ (bind b₄ m f) g

-}
