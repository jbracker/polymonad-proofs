
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
open import Haskell.List
open import Haskell.Applicative
open import Haskell.Monad
open import Identity 

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
    
