
module Haskell.Parameterized.IndexedMonad.Functor where

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
open import Extensionality
open import Haskell
open import Identity
open import Haskell.Functor hiding ( functor )
open import Haskell.Parameterized.IndexedMonad

-- -----------------------------------------------------------------------------
-- Indexed Monads are Functors
-- -----------------------------------------------------------------------------

open IxMonad hiding ( _>>=_ ; return ; fmap )

IxMonad→Functor : ∀ {ℓ}
                → (Ixs : Set ℓ)
                → (M : Ixs → Ixs → TyCon)
                → IxMonad Ixs M 
                → ∀ (i j : Ixs) → Functor (M i j)
IxMonad→Functor Ixs M monad i j = record 
  { fmap = fmap 
  ; law-id = law-id 
  ; law-compose = law-compose
  } where
    F = IxMonadTC i j
    
    _>>=_ = IxMonad._>>=_ monad
    return = IxMonad.return monad
    
    fmap : ∀ {α β : Type} → (α → β) → M i j α → M i j β
    fmap f ma = ma >>= (return ∘ f)
        
    law-id : ∀ {α : Type} → fmap {α = α} identity ≡ identity
    law-id = fun-ext law-id'
      where
        law-id' : {α : Type} → (ma : M i j α) → fmap {α = α} identity ma ≡ identity ma 
        law-id' ma = begin
          fmap identity ma 
            ≡⟨ refl ⟩
          ma >>= return
            ≡⟨ law-left-id monad ma ⟩
          identity ma ∎
        
    law-compose : ∀ {α β γ : Type} 
               → (f : β → γ) → (g : α → β) 
               → fmap (f ∘ g) ≡ fmap f ∘ fmap g
    law-compose {α = α} f g = fun-ext lawDist'
      where
        lawDist' : (ma : M i j α)
                 → fmap (f ∘ g) ma ≡ (fmap f ∘ fmap g) ma
        lawDist' ma = begin 
          fmap (f ∘ g) ma
            ≡⟨ refl ⟩
          ma >>= (λ x → return (f (g x)))
            ≡⟨ cong (λ X → ma >>= X) (fun-ext (λ x → sym (law-right-id monad (g x) (return ∘ f)))) ⟩
          ma >>= (λ x → return (g x) >>= (return ∘ f))
            ≡⟨ law-assoc monad ma (return ∘ g) (return ∘ f) ⟩
          (ma >>= (return ∘ g)) >>= (return ∘ f)
            ≡⟨ refl ⟩
          (fmap f ∘ fmap g) ma ∎
