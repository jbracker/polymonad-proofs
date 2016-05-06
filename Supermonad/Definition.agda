
module Supermonad.Definition where

-- Stdlib
open import Level
open import Function
open import Agda.Primitive
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Data.Nat hiding ( _⊔_ )
open import Data.Vec
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Local
open import Utilities
open import Haskell
open import Identity
open import Polymonad
open import Functor

open import Parameterized.PhantomIndices

-- -----------------------------------------------------------------------------
-- Definition of SuperMonads
-- -----------------------------------------------------------------------------

record Supermonad {ℓ} (TyCons : Set ℓ) : Set (lsuc ℓ) where
  field
    ⟨_⟩ : TyCons → TyCon
    
    -- The constraints/condition that needs to hold for the bind operation.
    Binds : TyCons → TyCons → TyCons → Type → Type → Set ℓ
    
    -- The constraints/condition that needs to hold for the return operation.
    Returns : TyCons → Type → Set ℓ

    -- The functor associated with the supermonad.
    functor : (M : TyCons) → Functor ⟨ M ⟩
    
    -- A supermonad only uses a single type constructor.
    
    -- Arity of the supermonad type constructor.
    tyConArity : ℕ
    -- Argument types of the supermonad type constructor indices.
    tyConArgTys : Vec (Set ℓ) tyConArity
    -- The supermonad type constructor.
    tyCon : ParamTyCon tyConArgTys
    
    -- The bind operation of the supermonad.
    bind : {α β : Type} → {M N P : TyCons} → Binds M N P α β → ( ⟨ M ⟩ α → (α → ⟨ N ⟩ β) → ⟨ P ⟩ β )
    -- The return operation of the supermonad.
    return : {α : Type} {M : TyCons} → Returns M α → (α → ⟨ M ⟩ α)
    
    -- The supermonad only uses one type constructor.
    lawSingleTyCon : ∀ (M : TyCons) 
                   → ∃Indices tyConArgTys tyCon (λ X → Lift {ℓ = lsuc ℓ} (⟨ M ⟩ ≡ X))
    
    -- The supermonad only has a single bind operation.
    lawUniqueBind : {α β : Type} {M N P : TyCons} 
                  → (b₁ b₂ : Binds M N P α β) 
                  → b₁ ≡ b₂
    
    -- The supermonad only has a single return operation.
    lawUniqueReturn : {α : Type} {M : TyCons} 
                    → (r₁ r₂ : Returns M α) 
                    → r₁ ≡ r₂
    
    -- The supermonad version of the right identity law.
    lawIdR : {α β : Type} 
           → (M N : TyCons)
           → (b : Binds M N N α β) → (r : Returns M α)
           → (a : α) → (k : α → ⟨ N ⟩ β)
           → bind b (return r a) k ≡ k a
    
    -- The supermonad version of the left identity law.
    lawIdL : {α : Type} 
           → (M N : TyCons)
           → (b : Binds M N M α α) → (r : Returns N α)
           → (m : ⟨ M ⟩ α)
           → bind b m (return r) ≡ m
    
    -- The supermonad version of the associativity law.
    lawAssoc : {α β γ : Type} 
             → (M N P S T : TyCons)
             → (b₁ : Binds M N P α γ) → (b₂ : Binds S T N β γ)
             → (b₃ : Binds N T P β γ) → (b₄ : Binds M S N α β)
             → (m : ⟨ M ⟩ α) → (f : α → ⟨ S ⟩ β) → (g : β → ⟨ T ⟩ γ)
             → bind b₁ m (λ x → bind b₂ (f x) g) ≡ bind b₃ (bind b₄ m f) g
    
    -- The supermonad version of the monad-functor relationship.
    lawMonadFmap : {α β : Type}
                 → (M N : TyCons)
                 → (b : Binds M N M α β) → (r : Returns N β)
                 → (f : α → β) → (m : ⟨ M ⟩ α)
                 → bind b m (return r ∘ f) ≡ Functor.fmap (functor M) f m
    
  sequence : {α β : Type} {M N P : TyCons} → Binds M N P α β → ⟨ M ⟩ α → ⟨ N ⟩ β → ⟨ P ⟩ β
  sequence b ma mb = bind b ma (λ _ → mb)
  
  tyConSet : Set ℓ
  tyConSet = TyCons

record UnconstrainedSupermonad {ℓ} (TyCons : Set ℓ) : Set (lsuc ℓ) where
  field
    supermonad : Supermonad TyCons
    lawBindUnconstrained : ∃ λ (B : TyCons → TyCons → TyCons → Set ℓ) 
                           → (α β : Type) → (M N P : TyCons) 
                           → B M N P ≡ Supermonad.Binds supermonad M N P α β
    lawReturnUnconstrained : ∃ λ (R : TyCons → Set ℓ)
                             → (α : Type) → (M : TyCons)
                             → R M ≡ Supermonad.Returns supermonad M α

UnconstrainedSupermonad→Supermonad : ∀ {ℓ} {TyCons : Set ℓ} → UnconstrainedSupermonad {ℓ = ℓ} TyCons → Supermonad {ℓ = ℓ} TyCons
UnconstrainedSupermonad→Supermonad = UnconstrainedSupermonad.supermonad

K⟨_▷_⟩ : ∀ {n} {TyCons : Set n} → Supermonad TyCons → TyCons → TyCon
K⟨ monad ▷ M ⟩ = Supermonad.⟨ monad ⟩ M


