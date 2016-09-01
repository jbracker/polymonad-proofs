
module Parameterized.IndexedMonad.Functor where

-- Stdlib
open import Function
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
open import Parameterized.IndexedMonad

-- -----------------------------------------------------------------------------
-- Indexed Monads are Functors
-- -----------------------------------------------------------------------------

open IxMonad hiding ( _>>=_ ; return )

IxMonad→Functor : ∀ {ℓ}
                → (Ixs : Set ℓ)
                → (M : Ixs → Ixs → TyCon)
                → IxMonad Ixs M 
                → ∀ (i j : Ixs) → Functor (M i j)
IxMonad→Functor Ixs M monad i j = record 
  { fmap = fmap 
  ; lawId = lawId 
  ; lawDist = lawDist
  } where
    F = IxMonadTC i j
    
    _>>=_ = IxMonad._>>=_ monad
    return = IxMonad.return monad
    
    fmap : ∀ {α β : Type} → (α → β) → M i j α → M i j β
    fmap f ma = ma >>= (return ∘ f)
        
    lawId : ∀ {α : Type} → fmap {α = α} identity ≡ identity
    lawId = funExt lawId'
      where
        lawId' : {α : Type} → (ma : M i j α) → fmap {α = α} identity ma ≡ identity ma 
        lawId' ma = begin
          fmap identity ma 
            ≡⟨ refl ⟩
          ma >>= return
            ≡⟨ lawIdL monad ma ⟩
          identity ma ∎
        
    lawDist : ∀ {α β γ : Type} 
            → (f : β → γ) → (g : α → β) 
            → fmap (f ∘ g) ≡ fmap f ∘ fmap g
    lawDist {α = α} f g = funExt lawDist'
      where
        lawDist' : (ma : M i j α)
                 → fmap (f ∘ g) ma ≡ (fmap f ∘ fmap g) ma
        lawDist' ma = begin 
          fmap (f ∘ g) ma
            ≡⟨ refl ⟩
          ma >>= (λ x → return (f (g x)))
            ≡⟨ cong (λ X → ma >>= X) (funExt (λ x → sym (lawIdR monad (g x) (return ∘ f)))) ⟩
          ma >>= (λ x → return (g x) >>= (return ∘ f))
            ≡⟨ lawAssoc monad ma (return ∘ g) (return ∘ f) ⟩
          (ma >>= (return ∘ g)) >>= (return ∘ f)
            ≡⟨ refl ⟩
          (fmap f ∘ fmap g) ma ∎
