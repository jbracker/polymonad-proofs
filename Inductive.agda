 
module Inductive where

open import Level renaming ( suc to lsuc; zero to lzero )
open import Data.Nat hiding ( _⊔_ )
open import Data.Fin
open import Data.Vec
open import Data.Product
open import Data.Empty
open import Relation.Binary.PropositionalEquality

Fin→Level : ∀ {n} → Fin n → Level
Fin→Level Fin.zero = lzero
Fin→Level (Fin.suc k) = lsuc (Fin→Level k)

ℕ→Level : ℕ → Level
ℕ→Level ℕ.zero = lzero
ℕ→Level (ℕ.suc n) = lsuc (ℕ→Level n)

upperBound : {n : ℕ} → Vec Level n → Level
upperBound [] = lzero
upperBound (x ∷ v) = x Level.⊔ upperBound v


{-
mutual
  record IsInductive (C : Set) : Set₁ where
    field
      consNum : ℕ
      
      arities : Vec ℕ consNum
      
      inductiveToCarrier : Inductive arities C → C
      
      carrierToInductive : C → Inductive arities C
      
      --lawInductiveIso1 : ∀ (x : C) → inductiveToCarrier (carrierToInductive x) ≡ x

      --lawInductiveIso2 : ∀ (x : Inductive arities C) → carrierToInductive (inductiveToCarrier x) ≡ x
  
  data Inductive {k : ℕ} (Arities : Vec ℕ k) (C : Set) : Set₁ where
    Cons : (n : Fin k) → Vec (Inductive Arities C) (lookup n Arities) → Inductive Arities C
    Nested : {C' : Set} → (k' : ℕ) → (Arities' : Vec ℕ k') → Inductive Arities' C' → Inductive Arities C
-}
