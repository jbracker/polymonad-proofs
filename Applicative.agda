 
module Applicative where

open import Function hiding ( id ; _∘_ ) renaming ( _∘′_ to _∘_ )
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Utilities
open import Polymonad
open import Haskell 
open import Identity
open import Functor

record Applicative (F : TyCon) : Set₁ where
  infixl 4 _*>_ _<*_ _<*>_
  field
    pure : ∀ {α : Type} → α → F α
    _<*>_ : ∀ {α β : Type} → F (α → β) → F α → F β
    
    functor : Functor F
    
    lawId  : ∀ {α : Type} 
           → (v : F α) 
           → pure (id refl) <*> v ≡ v
    lawComposition : ∀ {α β γ : Type} 
                   → (u : F (β → γ)) → (v : F (α → β)) → (w : F α) 
                   → (pure _∘_) <*> u <*> v <*> w ≡ u <*> (v <*> w)
    lawHomomorphism : ∀ {α β : Type} 
                    → (x : α) → (f : α → β) 
                    → pure f <*> pure x ≡ pure (f x)
    lawInterchange : ∀ {α β : Type} 
                   → (u : F (α → β)) → (x : α) 
                   → u <*> pure x ≡ pure (λ f → f $ x) <*> u
  
  _*>_ : ∀ {α β : Type} → F α → F β → F β
  u *> v = pure (const (id refl)) <*> u <*> v

  _<*_ : ∀ {α β : Type} → F α → F β → F α
  u <* v = pure const <*> u <*> v
