
module Haskell.Monad.List where

-- Stdlib
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Data.List
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
  ; applicative = applicativeFromMonad _>>=_ return law-right-id law-left-id law-assoc
  ; law-right-id = law-right-id
  ; law-left-id = law-left-id
  ; law-assoc = law-assoc
  ; law-monad-fmap = λ f a → refl
  ; law-monad-ap = λ mf ma → refl
  } where
    _>>=_ : ∀ {α β : Type} → List α → (α → List β) → List β
    _>>=_ = bindList
    
    return : ∀ {α : Type} → α → List α
    return x = x ∷ []
    
    law-left-id : ∀ {α β : Type} 
           → (a : α) → (k : α → List β) 
           → return a >>= k ≡ k a
    law-left-id a k = begin
      return a >>= k
        ≡⟨ refl ⟩
      k a ++ []
        ≡⟨ xs++Nil≡xs (k a) ⟩
      k a ∎
    
    law-right-id : ∀ {α : Type} 
           → (m : List α)
           → m >>= return ≡ m
    law-right-id (x ∷ xs) = cong (_∷_ x) (law-right-id xs)
    law-right-id [] = refl
    
    law-assoc : ∀ {α β γ : Type} 
             → (m : List α) → (k : α → List β) → (h : β → List γ) 
             → m >>= (λ x → k x >>= h) ≡ (m >>= k) >>= h
    law-assoc (x ∷ xs) k h = begin
      (x ∷ xs) >>= (λ y → k y >>= h)
        ≡⟨ refl ⟩
      (k x >>= h) ++ (xs >>= (λ y → k y >>= h))
        ≡⟨ cong (_++_ (bindList (k x) h)) (law-assoc xs k h) ⟩
      (k x >>= h) ++ ((xs >>= k) >>= h)
        ≡⟨ distributiveConcat (k x) (xs >>= k) h ⟩
      (k x ++ (xs >>= k)) >>= h
        ≡⟨ refl ⟩
      ((x ∷ xs) >>= k) >>= h ∎
    law-assoc [] k h = refl
    
