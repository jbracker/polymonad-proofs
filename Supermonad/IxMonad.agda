
module Supermonad.IxMonad where

-- Stdlib
open import Level
open import Function
open import Agda.Primitive
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Data.Nat
open import Data.Vec hiding ( _>>=_ )
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Local
open import Utilities
open import Haskell
open import Identity
open import Functor
open import Polymonad
open import Constrained.ConstrainedFunctor
open import Parameterized.IndexedMonad
open import Parameterized.PhantomIndices
open import Supermonad.Definition

-- -----------------------------------------------------------------------------
-- Indexed Monads are Super Monads
-- -----------------------------------------------------------------------------

IxMonad→Supermonad : ∀ {n}
                   → (Ixs : Set n)
                   → (M : Ixs → Ixs → TyCon)
                   → IxMonad Ixs M → Supermonad (IxMonadTyCons Ixs)
IxMonad→Supermonad {n = n} Ixs M monad = record
  { ⟨_⟩ = ⟨_⟩
  ; Binds = Binds
  ; Returns = Returns
  ; functor = cfunctor
  ; tyConArity = tyConArity
  ; tyConArgTys = tyConArgTys
  ; tyCon = tyCon
  ; bind = bind
  ; return = return
  ; lawSingleTyCon = lawSingleTyCon
  ; lawUniqueBind = lawUniqueBind
  ; lawUniqueReturn = lawUniqueReturn
  ; lawIdR = lawIdR
  ; lawIdL = lawIdL
  ; lawAssoc = lawAssoc
  ; lawMonadFmap = lawMonadFmap
  } where
    TyCons = IxMonadTyCons Ixs
    
    ⟨_⟩ : TyCons → TyCon
    ⟨_⟩ (IxMonadTC i j) = M i j
    
    Binds : TyCons → TyCons → TyCons → Type → Type → Set n
    Binds (IxMonadTC i j) (IxMonadTC j' k) (IxMonadTC i' k') _ _ = j ≡ j' × i ≡ i' × k ≡ k'
    
    Returns : TyCons → Type → Set n
    Returns (IxMonadTC i j) _ = i ≡ j
    
    _>>=_ = IxMonad._>>=_ monad
    return' = IxMonad.return monad
    
    tyConArity : ℕ
    tyConArity = 2

    tyConArgTys : Vec (Set n) tyConArity
    tyConArgTys = Ixs ∷ Ixs ∷ []
    
    tyCon : ParamTyCon tyConArgTys
    tyCon i j = lift $ M i j
    
    bind : {α β : Type} {M N P : TyCons} → Binds M N P α β → ( ⟨ M ⟩ α → (α → ⟨ N ⟩ β) → ⟨ P ⟩ β )
    bind {M = IxMonadTC i j} {N = IxMonadTC .j l} {P = IxMonadTC .i .l} (refl , refl , refl) ma f = ma >>= f
    
    return : ∀ {α : Type} → {M : TyCons} → Returns M α → α → ⟨ M ⟩ α
    return {M = IxMonadTC i .i} refl = return'
    
    fmap⟨_⟩ : (M : TyCons) → ∀ {α β : Type} → (α → β) → ⟨ M ⟩ α → ⟨ M ⟩ β
    fmap⟨_⟩ (IxMonadTC i j) f ma = ma >>= (return' ∘ f)
    
    lawSingleTyCon : ∀ (M : TyCons) 
                   → ∃Indices tyConArgTys tyCon (λ X → Lift {ℓ = lsuc n} (⟨ M ⟩ ≡ X))
    lawSingleTyCon (IxMonadTC i j) = i , j , lift refl
    
    lawUniqueBind : {α β : Type} {M N P : TyCons} 
                  → (b₁ b₂ : Binds M N P α β) 
                  → b₁ ≡ b₂
    lawUniqueBind {M = IxMonadTC i j} {N = IxMonadTC .j k} {P = IxMonadTC .i .k} (refl , refl , refl) (refl , refl , refl) = refl
    
    lawUniqueReturn : {α : Type} {M : TyCons} 
                    → (r₁ r₂ : Returns M α) 
                    → r₁ ≡ r₂
    lawUniqueReturn {M = IxMonadTC i .i} refl refl = refl
    
    lawIdR : ∀ {α β : Type} 
           → (M N : TyCons)
           → (b : Binds M N N α β) → (r : Returns M α)
           → (a : α) → (k : α → ⟨ N ⟩ β)
           → bind b (return r a) k ≡ k a
    lawIdR (IxMonadTC i .i) (IxMonadTC .i k) (refl , refl , refl) refl a f = IxMonad.lawIdR monad a f
    
    lawIdL : ∀ {α : Type} 
           → (M N : TyCons)
           → (b : Binds M N M α α) → (r : Returns N α)
           → (m : ⟨ M ⟩ α)
           → bind b m (return r) ≡ m
    lawIdL (IxMonadTC i j) (IxMonadTC .j .j) (refl , refl , refl) refl m = IxMonad.lawIdL monad m
    
    lawAssoc : ∀ {α β γ : Type} 
             → (M N P S T : TyCons)
             → (b₁ : Binds M N P α γ) → (b₂ : Binds S T N β γ)
             → (b₃ : Binds N T P β γ) → (b₄ : Binds M S N α β)
             → (m : ⟨ M ⟩ α) → (f : α → ⟨ S ⟩ β) → (g : β → ⟨ T ⟩ γ)
             → bind b₁ m (λ x → bind b₂ (f x) g) ≡ bind b₃ (bind b₄ m f) g
    lawAssoc (IxMonadTC j .j) (IxMonadTC .j l) (IxMonadTC .j .l) (IxMonadTC .j .l) (IxMonadTC .l .l) 
             (refl , refl , refl) (refl , refl , refl) (refl , refl , refl) (refl , refl , refl) m f g = IxMonad.lawAssoc monad m f g
    
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
    
    cfunctor : (F : TyCons) → ConstrainedFunctor ⟨ F ⟩
    cfunctor (IxMonadTC i j) = Functor→ConstrainedFunctor (M i j) (functor (IxMonadTC i j))
    
    lawMonadFmap : ∀ {α β : Type}
                 → (M N : TyCons)
                 → (fcts : ConstrainedFunctor.FunctorCts (cfunctor M) α β)
                 → (b : Binds M N M α β) → (r : Returns N β)
                 → (f : α → β) → (m : ⟨ M ⟩ α)
                 → bind b m (return r ∘ f) ≡ ConstrainedFunctor.fmap (cfunctor M) fcts f m
    lawMonadFmap (IxMonadTC i j) (IxMonadTC .j .j) fcts (refl , refl , refl) refl f m = refl


IxMonad→UnconstrainedSupermonad 
  : ∀ {n}
  → (Ixs : Set n)
  → (M : Ixs → Ixs → TyCon)
  → IxMonad Ixs M → UnconstrainedSupermonad (IxMonadTyCons Ixs)
IxMonad→UnconstrainedSupermonad {n} Ixs M monad = record
  { supermonad = supermonad
  ; lawBindUnconstrained = Binds , lawBindUnconstrained
  ; lawReturnUnconstrained = Returns , lawReturnUnconstrained
  ; lawFunctorUnconstrained = (λ M → Lift ⊤) , lawFunctorUnconstrained
  } where
    supermonad = IxMonad→Supermonad Ixs M monad
    TyCons = Supermonad.tyConSet supermonad
    
    Binds : TyCons → TyCons → TyCons → Set n
    Binds (IxMonadTC i j) (IxMonadTC j' k) (IxMonadTC i' k') = j ≡ j' × i ≡ i' × k ≡ k'
    
    Returns : TyCons → Set n
    Returns (IxMonadTC i j) = i ≡ j
    
    lawBindUnconstrained : (α β : Type) → (M N P : TyCons) 
                         → Binds M N P ≡ Supermonad.Binds supermonad M N P α β
    lawBindUnconstrained α β (IxMonadTC i j) (IxMonadTC j' k) (IxMonadTC i' k') = refl
    
    lawReturnUnconstrained : (α : Type) → (M : TyCons)
                           → Returns M ≡ Supermonad.Returns supermonad M α
    lawReturnUnconstrained α (IxMonadTC i j) = refl

    lawFunctorUnconstrained : (α β : Type) → (M : TyCons)
                            → Lift {ℓ = n} ⊤ ≡ ConstrainedFunctor.FunctorCts (Supermonad.functor supermonad M) α β
    lawFunctorUnconstrained α β (IxMonadTC i j) = refl

