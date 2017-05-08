 
module Haskell.Monad where

open import Function renaming ( id to idF ; _∘_ to _∘F_ )
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Extensionality
open import Congruence
open import Haskell
open import Haskell.Functor
open import Haskell.Applicative

open Functor hiding ( fmap )
open Applicative hiding ( fmap )

record Monad (M : TyCon) : Set₁ where
  constructor monad
  
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
                 → fmap f x ≡ x >>= (return ∘F f)
    
  _>>_ : {α β : Type} → M α → M β → M β
  ma >> mb = ma >>= λ a → mb
  
  join : {α : Type} → M (M α) → M α
  join mma = mma >>= idF

  bind = _>>=_
  sequence = _>>_

monad-eq : {M : TyCon}
         → {_>>=₀_ : ∀ {α β : Type} → M α → (α → M β) → M β}
         → {_>>=₁_ : ∀ {α β : Type} → M α → (α → M β) → M β}
         → {return₀ : ∀ {α : Type} → α → M α}
         → {return₁ : ∀ {α : Type} → α → M α}
         → {applicative₀ : Applicative M}
         → {applicative₁ : Applicative M}
         → {law-left-id₀ : ∀ {α β : Type} → (a : α) → (k : α → M β) → return₀ a >>=₀ k ≡ k a}
         → {law-left-id₁ : ∀ {α β : Type} → (a : α) → (k : α → M β) → return₁ a >>=₁ k ≡ k a}
         → {law-right-id₀ : ∀ {α : Type} → (m : M α) → m >>=₀ return₀ ≡ m}
         → {law-right-id₁ : ∀ {α : Type} → (m : M α) → m >>=₁ return₁ ≡ m}
         → {law-assoc₀ : ∀ {α β γ : Type} → (m : M α) → (k : α → M β) → (h : β → M γ) → m >>=₀ (λ x → k x >>=₀ h) ≡ (m >>=₀ k) >>=₀ h}
         → {law-assoc₁ : ∀ {α β γ : Type} → (m : M α) → (k : α → M β) → (h : β → M γ) → m >>=₁ (λ x → k x >>=₁ h) ≡ (m >>=₁ k) >>=₁ h}
         → {law-monad-fmap₀ : ∀ {α β : Type}  → (f : α → β) → (x : M α) → Applicative.fmap applicative₀ f x ≡ x >>=₀ (return₀ ∘F f)}
         → {law-monad-fmap₁ : ∀ {α β : Type}  → (f : α → β) → (x : M α) → Applicative.fmap applicative₁ f x ≡ x >>=₁ (return₁ ∘F f)}
         → (λ {α} {β} → _>>=₀_ {α} {β}) ≡ _>>=₁_
         → (λ {α} → return₀ {α}) ≡ return₁
         → applicative₀ ≡ applicative₁
         → monad _>>=₀_ return₀ applicative₀ law-left-id₀ law-right-id₀ law-assoc₀ law-monad-fmap₀
         ≡ monad _>>=₁_ return₁ applicative₁ law-left-id₁ law-right-id₁ law-assoc₁ law-monad-fmap₁
monad-eq {M} {b} {.b} {r} {.r} {a} {.a} {li₀} {li₁} {ri₀} {ri₁} {as₀} {as₁} {mf₀} {mf₁} refl refl refl
  = cong₄ (monad {M = M} b r a) p1 p2 p3 p4
  where
    p1 : (λ {α β} → li₀ {α} {β}) ≡ li₁
    p1 = implicit-fun-ext
       $ λ α → implicit-fun-ext
       $ λ β → fun-ext
       $ λ a → fun-ext
       $ λ f → proof-irrelevance (li₀ a f) (li₁ a f)

    p2 : (λ {α} → ri₀ {α}) ≡ ri₁
    p2 = implicit-fun-ext
       $ λ α → fun-ext
       $ λ ma → proof-irrelevance (ri₀ ma) (ri₁ ma)
    
    p3 : (λ {α β γ} → as₀ {α} {β} {γ}) ≡ as₁
    p3 = implicit-fun-ext
       $ λ α → implicit-fun-ext
       $ λ β → implicit-fun-ext
       $ λ γ → fun-ext
       $ λ ma → fun-ext
       $ λ f → fun-ext
       $ λ g → proof-irrelevance (as₀ ma f g) (as₁ ma f g)
    
    p4 : (λ {α β} → mf₀ {α} {β}) ≡ mf₁
    p4 = implicit-fun-ext
       $ λ α → implicit-fun-ext
       $ λ β → fun-ext
       $ λ f → fun-ext
       $ λ ma → proof-irrelevance (mf₀ f ma) (mf₁ f ma)

private
  module MonadProperties {M : TyCon} (monad : Monad M) where
    open Monad monad

    monadFmap : {α β : Type} → (α → β) → (M α → M β)
    monadFmap f ma = ma >>= (return ∘F f)

    law-monad-functor-id : {α : Type} → (ma : M α)
                      → monadFmap (λ a → a) ma ≡ ma
    law-monad-functor-id ma = law-right-id ma

    law-monad-functor-compose : {α β γ : Type} 
                        → (g : α → β) (f : β → γ) (ma : M α) 
                        → monadFmap (f ∘F g) ma ≡ monadFmap f (monadFmap g ma)
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
      (m >>= f) >>= (return ∘F g)
        ≡⟨ sym (law-assoc m f (return ∘F g)) ⟩
      m >>= (λ x → f x >>= (return ∘F g)) 
        ≡⟨ cong (λ X → m >>= X) (fun-ext (λ x → sym (law-monad-fmap g (f x)))) ⟩
      m >>= (λ x → fmap g (f x)) ∎

    law-decompose-fmap-intro : {α β γ : Type}
                       → (m : M α) → (f : α → β) → (g : β → M γ)
                       → m >>= (g ∘F f) ≡ fmap f m >>= g
    law-decompose-fmap-intro m f g = begin
      m >>= (g ∘F f) 
        ≡⟨ cong (λ X → m >>= X) (fun-ext (λ x → sym (law-left-id (f x) g))) ⟩
      m >>= (λ x → return (f x) >>= g)
        ≡⟨ law-assoc m (return ∘F f) g ⟩
      (m >>= (return ∘F f)) >>= g
        ≡⟨ cong (λ X → X >>= g) (sym (law-monad-fmap f m)) ⟩
      fmap f m >>= g ∎

open MonadProperties public
