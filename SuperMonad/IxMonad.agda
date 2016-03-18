
module SuperMonad.IxMonad where

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
open import SuperMonad.Definition

-- -----------------------------------------------------------------------------
-- Indexed Monads are Super Monads
-- -----------------------------------------------------------------------------

IxMonad→SuperMonad : ∀ {n}
                   → (Ixs : Set n)
                   → (M : Ixs → Ixs → TyCon)
                   → IxMonad Ixs M → SuperMonad (IxMonadTyCons Ixs)
IxMonad→SuperMonad {n = n} Ixs M monad = record
  { ⟨_⟩ = ⟨_⟩
  ; Binds = Binds
  ; Returns = Returns
  ; functor = functor
  ; _◆_ = _◆_
  ; bind = bind
  ; return = return
  ; lawIdR = lawIdR
  ; lawIdL = lawIdL
  ; lawAssoc = lawAssoc
  ; lawMonadFmap = lawMonadFmap
  } where
    TyCons = IxMonadTyCons Ixs
    
    ⟨_⟩ : TyCons → TyCon
    ⟨_⟩ (IxMonadTC i j) = M i j
    
    Binds : TyCons → TyCons → Set n
    Binds (IxMonadTC i j) (IxMonadTC k l) = j ≡ k
    
    Returns : TyCons → Set n
    Returns (IxMonadTC i j) = i ≡ j

    _◆_ : TyCons → TyCons → TyCons
    IxMonadTC i j ◆ IxMonadTC k l = IxMonadTC i l
    
    _>>=_ = IxMonad._>>=_ monad
    return' = IxMonad.return monad

    bind : {M N : TyCons} → Binds M N → [ ⟨ M ⟩ , ⟨ N ⟩ ]▷ ⟨ M ◆ N ⟩
    bind {M = IxMonadTC i j} {N = IxMonadTC .j l} refl ma f = ma >>= f
    
    return : ∀ {α : Type} → {M : TyCons} → Returns M → α → ⟨ M ⟩ α
    return {M = IxMonadTC i .i} refl = return'
    
    fmap⟨_⟩ : (M : TyCons) → ∀ {α β : Type} → (α → β) → ⟨ M ⟩ α → ⟨ M ⟩ β
    fmap⟨_⟩ (IxMonadTC i j) f ma = ma >>= (return' ∘ f)
    
    lawIdR : ∀ {α β : Type} 
           → (M N : TyCons)
           → (N◆M≡M : N ◆ M ≡ M )
           → (b : Binds N M) → (r : Returns N)
           → (a : α) → (k : α → ⟨ M ⟩ β)
           → subst (λ X → ⟨ X ⟩ β) N◆M≡M (bind b (return r a) k) ≡ k a
    lawIdR (IxMonadTC i j) (IxMonadTC .i .i) refl refl refl a f = IxMonad.lawIdR monad a f
    
    lawIdL : ∀ {α : Type} 
           → (M N : TyCons)
           → (M◆N≡M : M ◆ N ≡ M)
           → (b : Binds M N) → (r : Returns N)
           → (m : ⟨ M ⟩ α)
           → subst (λ X → ⟨ X ⟩ α) M◆N≡M (bind b m (return r)) ≡ m
    lawIdL (IxMonadTC i j) (IxMonadTC .j .j) refl refl refl m = IxMonad.lawIdL monad m
    
    lawAssoc : ∀ {α β γ : Type} 
             → (M N P : TyCons)
             → (assoc : M ◆ (N ◆ P) ≡ (M ◆ N) ◆ P) 
             → (b₁ : Binds M (N ◆ P)) → (b₂ : Binds N P)
             → (b₃ : Binds (M ◆ N) P) → (b₄ : Binds M N)
             → (m : ⟨ M ⟩ α) → (f : α → ⟨ N ⟩ β) → (g : β → ⟨ P ⟩ γ)
             → subst (λ X → ⟨ X ⟩ γ) assoc (bind b₁ m (λ x → bind b₂ (f x) g)) 
               ≡ bind b₃ (bind b₄ m f) g
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
              ma >>= return'
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
              ma >>= (λ x → return' (f (g x)))
                ≡⟨ cong (λ X → ma >>= X) (funExt (λ x → sym (IxMonad.lawIdR monad (g x) (return' ∘ f)))) ⟩
              ma >>= (λ x → return' (g x) >>= (return' ∘ f))
                ≡⟨ IxMonad.lawAssoc monad ma (return' ∘ g) (return' ∘ f) ⟩
              (ma >>= (return' ∘ g)) >>= (return' ∘ f)
                ≡⟨ refl ⟩
              (fmap f ∘ fmap g) ma ∎
    
    lawMonadFmap : ∀ {α β : Type}
                 → (M N : TyCons)
                 → (M◆N≡M : M ◆ N ≡ M)
                 → (b : Binds M N) → (r : Returns N)
                 → (f : α → β) → (m : ⟨ M ⟩ α)
                 → subst (λ X → ⟨ X ⟩ β) M◆N≡M (bind b m (return r ∘ f)) 
                   ≡ Functor.fmap (functor M) f m
    lawMonadFmap (IxMonadTC i j) (IxMonadTC .j .j) refl refl refl f m = refl
