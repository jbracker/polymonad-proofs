 
module Monad where

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Utilities
open import Polymonad
open import Haskell

record Monad (M : TyCon) : Set₁ where
  field
    _>>=_ : ∀ {α β : Type} → M α → (α → M β) → M β
    return : ∀ {α : Type} → α → M α
    
    lawIdR : ∀ {α β : Type} 
           → (a : α) → (k : α → M β) 
           → return a >>= k ≡ k a
    lawIdL : ∀ {α : Type} 
           → (m : M α)
           → m >>= return ≡ m
    lawAssoc : ∀ {α β γ : Type} 
             → (m : M α) → (k : α → M β) → (h : β → M γ) 
             → m >>= (λ x → k x >>= h) ≡ (m >>= k) >>= h
  
  _>>_ : ∀ {α β : Type} → M α → M β → M β
  ma >> mb = ma >>= λ a → mb

mBind = Monad._>>=_
mReturn = Monad.return
mSequence = Monad._>>_

mLawIdL = Monad.lawIdL
mLawIdR = Monad.lawIdR
mLawAssoc = Monad.lawAssoc

fmap : ∀ {α β : Type} {M : TyCon} → (monad : Monad M) → (α → β) → (M α → M β)
fmap m f ma = (mBind m) ma (λ a → (mReturn m) (f a))

lawMonadFunctorId : ∀ {α : Type} {M : TyCon} 
                  → (monad : Monad M) → (ma : M α)
                  → fmap monad (λ a → a) ma ≡ ma
lawMonadFunctorId m ma = mLawIdL m ma

lawMonadFunctorComp : ∀ {α β γ : Type} {M : TyCon} 
                    → (monad : Monad M) 
                    → (g : α → β) (f : β → γ) (ma : M α) 
                    → fmap monad (λ a → f (g a)) ma ≡ fmap monad f (fmap monad g ma)
lawMonadFunctorComp m g f ma = begin
  fmap m (λ a → f (g a)) ma 
    ≡⟨ refl ⟩
  (mBind m) ma (λ a → (mReturn m) ((λ a' → f (g a')) a)) 
    ≡⟨ refl ⟩
  (mBind m) ma (λ a → (mReturn m) (f (g a))) 
    ≡⟨ refl ⟩
  (mBind m) ma (λ x → (λ a' → (mReturn m) (f a')) (g x) ) 
    ≡⟨ cong (λ X → (mBind m) ma X) (sym (funExt (λ x → mLawIdR m (g x) (λ a' → (mReturn m) (f a'))))) ⟩
  (mBind m) ma (λ x → (mBind m) ((mReturn m) (g x)) (λ a' → (mReturn m) (f a'))) 
    ≡⟨ refl ⟩
  (mBind m) ma (λ x → (mBind m) ((λ a → (mReturn m) (g a)) x) (λ a' → (mReturn m) (f a'))) 
    ≡⟨ mLawAssoc m ma (λ a → (mReturn m) (g a)) (λ a' → (mReturn m) (f a')) ⟩
  (mBind m) ((mBind m) ma (λ a → (mReturn m) (g a))) (λ a' → (mReturn m) (f a')) 
    ≡⟨ refl ⟩
  fmap m f (fmap m g ma) ∎

