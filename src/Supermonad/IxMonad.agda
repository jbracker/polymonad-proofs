
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
open import Haskell.Functor hiding ( functor )
open import Haskell.Constrained.ConstrainedFunctor
open import Haskell.Parameterized.Indexed.Monad
open import Haskell.Parameterized.Indexed.Functor
open import Haskell.Parameterized.PhantomIndices
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
  ; law-right-id = law-right-id
  ; law-left-id = law-left-id
  ; law-assoc = law-assoc
  ; law-monad-fmap = law-monad-fmap
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
    
    law-right-id : ∀ {α β : Type} 
           → (M N : TyCons)
           → (b : Binds M N N α β) → (r : Returns M α)
           → (a : α) → (k : α → ⟨ N ⟩ β)
           → bind b (return r a) k ≡ k a
    law-right-id (IxMonadTC i .i) (IxMonadTC .i k) (refl , refl , refl) refl a f = IxMonad.law-right-id monad a f
    
    law-left-id : ∀ {α : Type} 
           → (M N : TyCons)
           → (b : Binds M N M α α) → (r : Returns N α)
           → (m : ⟨ M ⟩ α)
           → bind b m (return r) ≡ m
    law-left-id (IxMonadTC i j) (IxMonadTC .j .j) (refl , refl , refl) refl m = IxMonad.law-left-id monad m
    
    law-assoc : ∀ {α β γ : Type} 
             → (M N P S T : TyCons)
             → (b₁ : Binds M N P α γ) → (b₂ : Binds S T N β γ)
             → (b₃ : Binds N T P β γ) → (b₄ : Binds M S N α β)
             → (m : ⟨ M ⟩ α) → (f : α → ⟨ S ⟩ β) → (g : β → ⟨ T ⟩ γ)
             → bind b₁ m (λ x → bind b₂ (f x) g) ≡ bind b₃ (bind b₄ m f) g
    law-assoc (IxMonadTC j .j) (IxMonadTC .j l) (IxMonadTC .j .l) (IxMonadTC .j .l) (IxMonadTC .l .l) 
             (refl , refl , refl) (refl , refl , refl) (refl , refl , refl) (refl , refl , refl) m f g = IxMonad.law-assoc monad m f g
    
    functor : (F : TyCons) → Functor ⟨ F ⟩
    functor (IxMonadTC i j) = IxMonad→Functor Ixs M monad i j
    
    cfunctor : (F : TyCons) → ConstrainedFunctor ⟨ F ⟩
    cfunctor (IxMonadTC i j) = Functor→ConstrainedFunctor (M i j) (functor (IxMonadTC i j))
    
    law-monad-fmap : ∀ {α β : Type}
                 → (M N : TyCons)
                 → (fcts : ConstrainedFunctor.FunctorCts (cfunctor M) α β)
                 → (b : Binds M N M α β) → (r : Returns N β)
                 → (f : α → β) → (m : ⟨ M ⟩ α)
                 → bind b m (return r ∘ f) ≡ ConstrainedFunctor.fmap (cfunctor M) fcts f m
    law-monad-fmap (IxMonadTC i j) (IxMonadTC .j .j) fcts (refl , refl , refl) refl f m = refl


IxMonad→UnconstrainedSupermonad 
  : ∀ {n}
  → (Ixs : Set n)
  → (M : Ixs → Ixs → TyCon)
  → IxMonad Ixs M → UnconstrainedSupermonad (IxMonadTyCons Ixs)
IxMonad→UnconstrainedSupermonad {n} Ixs M monad = record
  { supermonad = supermonad
  ; lawBindUnconstrained = Binds , lawBindUnconstrained
  ; lawReturnUnconstrained = Returns , lawReturnUnconstrained
  ; lawFunctorUnconstrained = lawFunctorUnconstrained
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

    lawFunctorUnconstrained : (M : TyCons) → Functor K⟨ supermonad ▷ M ⟩
    lawFunctorUnconstrained (IxMonadTC i j) = IxMonad→Functor Ixs M monad i j
    {-
    lawFunctorUnconstrained : (α β : Type) → (M : TyCons)
                            → Lift {ℓ = n} ⊤ ≡ ConstrainedFunctor.FunctorCts (Supermonad.functor supermonad M) α β
    lawFunctorUnconstrained α β (IxMonadTC i j) = refl
    -}
