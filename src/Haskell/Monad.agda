 
module Haskell.Monad where

open import Function renaming ( id to idF )
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Extensionality
open import Haskell
open import Haskell.Functor
open import Haskell.Applicative

open Functor
open Applicative

record Monad (M : TyCon) : Set₁ where
  field
    _>>=_ : ∀ {α β : Type} → M α → (α → M β) → M β
    return : ∀ {α : Type} → α → M α
    
    applicative : Applicative M
    
    lawIdR : ∀ {α β : Type} 
           → (a : α) → (k : α → M β) 
           → return a >>= k ≡ k a
    lawIdL : ∀ {α : Type} 
           → (m : M α)
           → m >>= return ≡ m
    lawAssoc : ∀ {α β γ : Type} 
             → (m : M α) → (k : α → M β) → (h : β → M γ)
             → m >>= (λ x → k x >>= h) ≡ (m >>= k) >>= h
    
    lawMonadFmap : ∀ {α β : Type} 
                 → (f : α → β) → (x : M α) 
                 → fmap (functor applicative) f x ≡ x >>= (return ∘ f)
    
  _>>_ : {α β : Type} → M α → M β → M β
  ma >> mb = ma >>= λ a → mb
  
  join : {α : Type} → M (M α) → M α
  join mma = mma >>= idF
  
mBind = Monad._>>=_
mReturn = Monad.return
mSequence = Monad._>>_

mLawIdL = Monad.lawIdL
mLawIdR = Monad.lawIdR
mLawAssoc = Monad.lawAssoc

monadFmap : ∀ {α β : Type} {M : TyCon} → (monad : Monad M) → (α → β) → (M α → M β)
monadFmap m f ma = (mBind m) ma (λ a → (mReturn m) (f a))

lawMonadFunctorId : ∀ {α : Type} {M : TyCon} 
                  → (monad : Monad M) → (ma : M α)
                  → monadFmap monad (λ a → a) ma ≡ ma
lawMonadFunctorId m ma = mLawIdL m ma

lawMonadFunctorComp : ∀ {α β γ : Type} {M : TyCon} 
                    → (monad : Monad M) 
                    → (g : α → β) (f : β → γ) (ma : M α) 
                    → monadFmap monad (λ a → f (g a)) ma ≡ monadFmap monad f (monadFmap monad g ma)
lawMonadFunctorComp m g f ma = begin
  monadFmap m (λ a → f (g a)) ma 
    ≡⟨ refl ⟩
  (mBind m) ma (λ a → (mReturn m) ((λ a' → f (g a')) a)) 
    ≡⟨ refl ⟩
  (mBind m) ma (λ a → (mReturn m) (f (g a))) 
    ≡⟨ refl ⟩
  (mBind m) ma (λ x → (λ a' → (mReturn m) (f a')) (g x) ) 
    ≡⟨ cong (λ X → (mBind m) ma X) (sym (fun-ext (λ x → mLawIdR m (g x) (λ a' → (mReturn m) (f a'))))) ⟩
  (mBind m) ma (λ x → (mBind m) ((mReturn m) (g x)) (λ a' → (mReturn m) (f a'))) 
    ≡⟨ refl ⟩
  (mBind m) ma (λ x → (mBind m) ((λ a → (mReturn m) (g a)) x) (λ a' → (mReturn m) (f a'))) 
    ≡⟨ mLawAssoc m ma (λ a → (mReturn m) (g a)) (λ a' → (mReturn m) (f a')) ⟩
  (mBind m) ((mBind m) ma (λ a → (mReturn m) (g a))) (λ a' → (mReturn m) (f a')) 
    ≡⟨ refl ⟩
  monadFmap m f (monadFmap m g ma) ∎

open Monad {{...}}

commuteFmapBind : {α β γ : Type} {M : TyCon}
                → (monad : Monad M)
                → (m : M α) → (f : α → M β) → (g : β → γ)
                → fmap (functor applicative) g (m >>= f) ≡ m >>= (λ x → fmap (functor applicative) g (f x))
commuteFmapBind monad m f g = begin
  fmap (functor applicative) g (m >>= f)
    ≡⟨ lawMonadFmap g (m >>= f) ⟩
  (m >>= f) >>= (return ∘ g)
    ≡⟨ sym (lawAssoc m f (return ∘ g)) ⟩
  m >>= (λ x → f x >>= (return ∘ g)) 
    ≡⟨ cong (λ X → m >>= X) (fun-ext (λ x → sym (lawMonadFmap g (f x)))) ⟩
  m >>= (λ x → fmap (functor applicative) g (f x)) ∎

decomposeFmapIntro : {α β γ : Type} {M : TyCon}
                   → (monad : Monad M)
                   → (m : M α) → (f : α → β) → (g : β → M γ)
                   → m >>= (g ∘ f) ≡ fmap (functor applicative) f m >>= g
decomposeFmapIntro monad m f g = begin
  m >>= (g ∘ f) 
    ≡⟨ cong (λ X → m >>= X) (fun-ext (λ x → sym (lawIdR (f x) g))) ⟩
  m >>= (λ x → return (f x) >>= g)
    ≡⟨ lawAssoc m (return ∘ f) g ⟩
  (m >>= (return ∘ f)) >>= g
    ≡⟨ cong (λ X → X >>= g) (sym (lawMonadFmap f m)) ⟩
  fmap (functor applicative) f m >>= g ∎
