 
module Haskell.List where

-- Stdlib
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.List
open import Data.Nat
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Local
open import Utilities
open import Haskell
open import Identity

bindList : [ List , List ]▷ List
bindList (x ∷ xs) f = f x ++ (bindList xs f)
bindList Nil f = []

xs++Nil≡xs : ∀ {α : Type} → (xs : List α) → xs ++ [] ≡ xs
xs++Nil≡xs (x ∷ xs) = cong (_∷_ x) (xs++Nil≡xs xs)
xs++Nil≡xs [] = refl

associativeConcat : ∀ {α : Type} 
                  → (xs ys zs : List α) 
                  → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
associativeConcat (x ∷ xs) ys zs = cong (_∷_ x) (associativeConcat xs ys zs)
associativeConcat [] ys zs = refl

distributiveConcat : ∀ {α β : Type} 
                   → (xs ys : List α) → (f : α → List β) 
                   → (bindList xs f) ++ (bindList ys f) ≡ bindList (xs ++ ys) f
distributiveConcat (x ∷ xs) ys f = begin
  bindList (x ∷ xs) f ++ bindList ys f
    ≡⟨ refl ⟩
  (f x ++ bindList xs f) ++ bindList ys f
    ≡⟨ associativeConcat (f x) (bindList xs f) (bindList ys f) ⟩
  f x ++ (bindList xs f ++ bindList ys f)
    ≡⟨ cong (_++_ (f x)) (distributiveConcat xs ys f) ⟩
  f x ++ bindList (xs ++ ys) f
    ≡⟨ refl ⟩
  bindList ((x ∷ xs) ++ ys) f ∎
distributiveConcat [] ys f = refl
