
module KmettMonad.IxMonad where

-- Stdlib
open import Level
open import Function
open import Agda.Primitive
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Local
open import Utilities
open import Haskell
open import Identity
open import Functor
open import Polymonad
open import Parameterized.IndexedMonad
open import KmettMonad.Definition

-- -----------------------------------------------------------------------------
-- Indexed Monads are Kmett Monads
-- -----------------------------------------------------------------------------

IxMonad→KmettMonad : ∀ {n}
                   → (Ixs : Set n)
                   → (M : Ixs → Ixs → TyCon)
                   → IxMonad Ixs M → KmettMonad (IxMonadTyCons Ixs)
IxMonad→KmettMonad {n = n} Ixs M monad = record
  { ⟨_⟩ = ⟨_⟩
  ; BindCompat = BindCompat
  ; ReturnCompat = ReturnCompat
  ; functor = functor
  ; _◆_ = _◆_
  ; bind⟨_,_,_⟩ = bind⟨_,_,_⟩
  ; return⟨_,_⟩ = return⟨_,_⟩
  ; lawIdR = lawIdR
  ; lawIdL = lawIdL
  ; lawAssoc = lawAssoc
  } where
    TyCons = IxMonadTyCons Ixs
    
    ⟨_⟩ : TyCons → TyCon
    ⟨_⟩ (IxMonadTC i j) = M i j
    
    BindCompat : TyCons → TyCons → Set n
    BindCompat (IxMonadTC i j) (IxMonadTC k l) = j ≡ k
    
    ReturnCompat : TyCons → Set n
    ReturnCompat (IxMonadTC i j) = i ≡ j

    _◆_ : TyCons → TyCons → TyCons
    IxMonadTC i j ◆ IxMonadTC k l = IxMonadTC i l
    
    _>>=_ = IxMonad._>>=_ monad
    return = IxMonad.return monad

    bind⟨_,_,_⟩ : (M N : TyCons) → BindCompat M N → [ ⟨ M ⟩ , ⟨ N ⟩ ]▷ ⟨ M ◆ N ⟩
    bind⟨_,_,_⟩ (IxMonadTC i j) (IxMonadTC .j l) refl ma f = ma >>= f
    
    return⟨_,_⟩ : ∀ {α : Type} → (M : TyCons) → ReturnCompat M → α → ⟨ M ⟩ α
    return⟨_,_⟩ (IxMonadTC i .i) refl = return
    
    fmap⟨_⟩ : (M : TyCons) → ∀ {α β : Type} → (α → β) → ⟨ M ⟩ α → ⟨ M ⟩ β
    fmap⟨_⟩ (IxMonadTC i j) f ma = ma >>= (return ∘ f)
    
    lawIdR : ∀ {α β : Type} 
           → (M N : TyCons)
           → (N◆M≡M : N ◆ M ≡ M )
           → (comp : BindCompat N M) → (compR : ReturnCompat N)
           → (a : α) → (k : α → ⟨ M ⟩ β)
           → subst (λ X → ⟨ X ⟩ β) N◆M≡M (bind⟨ N , M , comp ⟩ (return⟨ N , compR ⟩ a) k) ≡ k a
    lawIdR (IxMonadTC i j) (IxMonadTC .i .i) refl refl refl a f = IxMonad.lawIdR monad a f
    
    lawIdL : ∀ {α : Type} 
           → (M N : TyCons)
           → (M◆N≡M : M ◆ N ≡ M)
           → (comp : BindCompat M N) → (compR : ReturnCompat N)
           → (m : ⟨ M ⟩ α)
           → subst (λ X → ⟨ X ⟩ α) M◆N≡M (bind⟨ M , N , comp ⟩ m return⟨ N , compR ⟩) ≡ m
    lawIdL (IxMonadTC i j) (IxMonadTC .j .j) refl refl refl m = IxMonad.lawIdL monad m
    
    lawAssoc : ∀ {α β γ : Type} 
             → (M N P : TyCons)
             → (assoc : M ◆ (N ◆ P) ≡ (M ◆ N) ◆ P) 
             → (comp1 : BindCompat M (N ◆ P)) → (comp2 : BindCompat N P)
             → (comp3 : BindCompat (M ◆ N) P) → (comp4 : BindCompat M N)
             → (m : ⟨ M ⟩ α) → (f : α → ⟨ N ⟩ β) → (g : β → ⟨ P ⟩ γ)
             → subst (λ X → ⟨ X ⟩ γ) assoc (bind⟨ M , N ◆ P , comp1 ⟩ m (λ x → bind⟨ N , P , comp2 ⟩ (f x) g)) 
               ≡ bind⟨ M ◆ N , P , comp3 ⟩ (bind⟨ M , N , comp4 ⟩ m f) g
    lawAssoc (IxMonadTC i j) (IxMonadTC .j k) (IxMonadTC .k l) refl refl refl refl refl m f g = IxMonad.lawAssoc monad m f g
    
    functor : (F : TyCons) → Functor ⟨ F ⟩
    functor (IxMonadTC i j) = record 
      { fmap = fmap 
      ; lawId = lawId 
      ; lawDist = lawDist
      } where
        F = IxMonadTC i j
        fmap = fmap⟨ F ⟩
        
        lawId : ∀ {α : Type} → fmap {α = α} identity ≡ identity
        lawId = funExt lawId'
          where
            lawId' : {α : Type} → (ma : ⟨ F ⟩ α) → fmap {α = α} identity ma ≡ identity ma 
            lawId' ma = begin
              fmap identity ma 
                ≡⟨ refl ⟩
              ma >>= return
                ≡⟨ IxMonad.lawIdL monad ma ⟩
              identity ma ∎
        
        lawDist : ∀ {α β γ : Type} 
                → (f : β → γ) → (g : α → β) 
                → fmap (f ∘ g) ≡ fmap f ∘ fmap g
        lawDist {α = α} f g = funExt lawDist'
          where
            lawDist' : (ma : ⟨ F ⟩ α)
                     → fmap (f ∘ g) ma ≡ (fmap f ∘ fmap g) ma
            lawDist' ma = begin 
              fmap (f ∘ g) ma
                ≡⟨ refl ⟩
              ma >>= (λ x → return (f (g x)))
                ≡⟨ cong (λ X → ma >>= X) (funExt (λ x → sym (IxMonad.lawIdR monad (g x) (return ∘ f)))) ⟩
              ma >>= (λ x → return (g x) >>= (return ∘ f))
                ≡⟨ IxMonad.lawAssoc monad ma (return ∘ g) (return ∘ f) ⟩
              (ma >>= (return ∘ g)) >>= (return ∘ f)
                ≡⟨ refl ⟩
              (fmap f ∘ fmap g) ma ∎
