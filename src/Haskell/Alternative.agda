 
module Haskell.Alternative where

open import Relation.Binary.PropositionalEquality

open import Haskell
open import Haskell.Applicative

record Alternative (F : TyCon) : Set₁ where
  infixl 3 _<|>_
  field
    -- The identity of (<|>).
    empty : ∀ {α : Type} → F α
    -- An assiciative binary operation.
    _<|>_ : ∀ {α : Type} → F α → F α → F α
    
    applicative : Applicative F

  open Applicative applicative public
  
  field
    law-left-id : ∀ {α : Type} 
           → (v : F α) 
           → (empty {α} <|> v) ≡ v
    law-right-id : ∀ {α : Type}
           → (v : F α)
           → (v <|> empty) ≡ v
    law-assoc : ∀ {α : Type}
             → (v s t : F α)
             → ((v <|> s) <|> t) ≡ (v <|> (s <|> t))
