 
module Haskell.Alternative where

open import Function hiding ( id ; _∘_ ) renaming ( _∘′_ to _∘_ )
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Utilities
open import Identity
open import Haskell 
open import Haskell.List
open import Haskell.Functor
open import Haskell.Applicative

record Alternative (F : TyCon) : Set₁ where
  infixl 3 _<|>_
  field
    -- The identity of (<|>).
    empty : ∀ {α : Type} → F α
    -- An assiciative binary operation.
    _<|>_ : ∀ {α : Type} → F α → F α → F α
    
    applicative : Applicative F
    
    lawIdL : ∀ {α : Type} 
           → (v : F α) 
           → (empty {α} <|> v) ≡ v
    lawIdR : ∀ {α : Type}
           → (v : F α)
           → (v <|> empty) ≡ v
    lawAssoc : ∀ {α : Type}
             → (v s t : F α)
             → ((v <|> s) <|> t) ≡ (v <|> (s <|> t))
  
  pure = Applicative.pure applicative
  _<$>_ = Functor.fmap $ Applicative.functor applicative
  _<*>_ = Applicative._<*>_ applicative
