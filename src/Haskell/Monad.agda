 
module Haskell.Monad where

open import Function renaming ( id to idF )
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Extensionality
open import Haskell
open import Haskell.Functor
open import Haskell.Applicative

open Functor hiding ( fmap )
open Applicative hiding ( fmap )

record Monad (M : TyCon) : Set₁ where
  field
    _>>=_ : ∀ {α β : Type} → M α → (α → M β) → M β
    return : ∀ {α : Type} → α → M α
    
    applicative : Applicative M

  open Applicative applicative public
  
  field
    law-left-id : ∀ {α β : Type} 
           → (a : α) → (k : α → M β) 
           → return a >>= k ≡ k a
    law-right-id : ∀ {α : Type} 
           → (m : M α)
           → m >>= return ≡ m
    law-assoc : ∀ {α β γ : Type} 
             → (m : M α) → (k : α → M β) → (h : β → M γ)
             → m >>= (λ x → k x >>= h) ≡ (m >>= k) >>= h
    
    law-monad-fmap : ∀ {α β : Type} 
                 → (f : α → β) → (x : M α) 
                 → fmap f x ≡ x >>= (return ∘ f)
    
  _>>_ : {α β : Type} → M α → M β → M β
  ma >> mb = ma >>= λ a → mb
  
  join : {α : Type} → M (M α) → M α
  join mma = mma >>= idF

  bind = _>>=_
  sequence = _>>_

private
  module MonadProperties {M : TyCon} (monad : Monad M) where
    open Monad monad

    monadFmap : {α β : Type} → (α → β) → (M α → M β)
    monadFmap f ma = ma >>= (return ∘ f)

    law-monad-functor-id : {α : Type} → (ma : M α)
                      → monadFmap (λ a → a) ma ≡ ma
    law-monad-functor-id ma = law-right-id ma

    law-monad-functor-compose : {α β γ : Type} 
                        → (g : α → β) (f : β → γ) (ma : M α) 
                        → monadFmap (f ∘ g) ma ≡ monadFmap f (monadFmap g ma)
    law-monad-functor-compose g f ma = begin
      monadFmap (λ a → f (g a)) ma 
        ≡⟨ refl ⟩
      ma >>= (λ a → return (f (g a))) 
        ≡⟨ refl ⟩
      ma >>= (λ x → (λ a' → return (f a')) (g x) ) 
        ≡⟨ cong (λ X → ma >>= X) (sym (fun-ext (λ x → law-left-id (g x) (λ a' → return (f a'))))) ⟩
      ma >>= (λ x → (return (g x)) >>= (λ a' → return (f a'))) 
        ≡⟨ refl ⟩
      ma >>= (λ x → ((λ a → return (g a)) x) >>= (λ a' → return (f a'))) 
        ≡⟨ law-assoc ma (λ a → return (g a)) (λ a' → return (f a')) ⟩
      (ma >>= (λ a → return (g a))) >>= (λ a' → return (f a')) 
        ≡⟨ refl ⟩
      monadFmap f (monadFmap g ma) ∎

    law-commute-fmap-bind : {α β γ : Type}
                    → (m : M α) → (f : α → M β) → (g : β → γ)
                    → fmap g (m >>= f) ≡ m >>= (λ x → fmap g (f x))
    law-commute-fmap-bind m f g = begin
      fmap g (m >>= f)
        ≡⟨ law-monad-fmap g (m >>= f) ⟩
      (m >>= f) >>= (return ∘ g)
        ≡⟨ sym (law-assoc m f (return ∘ g)) ⟩
      m >>= (λ x → f x >>= (return ∘ g)) 
        ≡⟨ cong (λ X → m >>= X) (fun-ext (λ x → sym (law-monad-fmap g (f x)))) ⟩
      m >>= (λ x → fmap g (f x)) ∎

    law-decompose-fmap-intro : {α β γ : Type}
                       → (m : M α) → (f : α → β) → (g : β → M γ)
                       → m >>= (g ∘ f) ≡ fmap f m >>= g
    law-decompose-fmap-intro m f g = begin
      m >>= (g ∘ f) 
        ≡⟨ cong (λ X → m >>= X) (fun-ext (λ x → sym (law-left-id (f x) g))) ⟩
      m >>= (λ x → return (f x) >>= g)
        ≡⟨ law-assoc m (return ∘ f) g ⟩
      (m >>= (return ∘ f)) >>= g
        ≡⟨ cong (λ X → X >>= g) (sym (law-monad-fmap f m)) ⟩
      fmap f m >>= g ∎

open MonadProperties public
