
module Haskell.Monad.List where

-- Stdlib
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Local
open import Utilities
open import Haskell
open import Haskell.Applicative
open import Haskell.Monad
open import Identity 


data List (α : Type) : Type where
  _∷_ : α → List α → List α
  Nil : List α

_++_ : ∀ {α : Type} → List α → List α → List α
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)
Nil ++ ys = ys

bindList : [ List , List ]▷ List
bindList (x ∷ xs) f = f x ++ (bindList xs f)
bindList Nil f = Nil

xs++Nil≡xs : ∀ {α : Type} → (xs : List α) → xs ++ Nil ≡ xs
xs++Nil≡xs (x ∷ xs) = cong (_∷_ x) (xs++Nil≡xs xs)
xs++Nil≡xs Nil = refl

associativeConcat : ∀ {α : Type} 
                  → (xs ys zs : List α) 
                  → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
associativeConcat (x ∷ xs) ys zs = cong (_∷_ x) (associativeConcat xs ys zs)
associativeConcat Nil ys zs = refl

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
distributiveConcat Nil ys f = refl

monadList : Monad List
monadList = record
  { _>>=_ = _>>=_
  ; return = return
  ; applicative = applicativeFromMonad _>>=_ return lawIdL lawIdR lawAssoc
  ; lawIdR = lawIdR
  ; lawIdL = lawIdL
  ; lawAssoc = lawAssoc
  ; lawMonadFmap = λ f a → refl
  } where
    _>>=_ : ∀ {α β : Type} → List α → (α → List β) → List β
    _>>=_ = bindList
    
    return : ∀ {α : Type} → α → List α
    return x = x ∷ Nil
    
    lawIdR : ∀ {α β : Type} 
           → (a : α) → (k : α → List β) 
           → return a >>= k ≡ k a
    lawIdR a k = begin
      return a >>= k
        ≡⟨ refl ⟩
      k a ++ Nil
        ≡⟨ xs++Nil≡xs (k a) ⟩
      k a ∎
    
    lawIdL : ∀ {α : Type} 
           → (m : List α)
           → m >>= return ≡ m
    lawIdL (x ∷ xs) = cong (_∷_ x) (lawIdL xs)
    lawIdL Nil = refl
    
    lawAssoc : ∀ {α β γ : Type} 
             → (m : List α) → (k : α → List β) → (h : β → List γ) 
             → m >>= (λ x → k x >>= h) ≡ (m >>= k) >>= h
    lawAssoc (x ∷ xs) k h = begin
      (x ∷ xs) >>= (λ y → k y >>= h)
        ≡⟨ refl ⟩
      (k x >>= h) ++ (xs >>= (λ y → k y >>= h))
        ≡⟨ cong (_++_ (bindList (k x) h)) (lawAssoc xs k h) ⟩
      (k x >>= h) ++ ((xs >>= k) >>= h)
        ≡⟨ distributiveConcat (k x) (xs >>= k) h ⟩
      (k x ++ (xs >>= k)) >>= h
        ≡⟨ refl ⟩
      ((x ∷ xs) >>= k) >>= h ∎
    lawAssoc Nil k h = refl
    
