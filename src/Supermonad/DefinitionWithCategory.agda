
module Supermonad.DefinitionWithCategory where

-- Stdlib
open import Level
open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Agda.Primitive
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Data.Nat hiding ( _⊔_ )
open import Data.Vec hiding ( _>>=_ ; functor )
open import Data.List hiding ( sequence )
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning


open import Utilities
open import Haskell
open import Haskell.Constrained.ConstrainedFunctor
open import Theory.Category.Definition


open Category renaming ( left-id to catIdL ; right-id to catIdR ; assoc to catAssoc ; _∘_ to comp )


UniqueIdHomomorphisms : ∀ {ℓ₀ ℓ₁} → (C : Category {ℓ₀} {ℓ₁}) → Set (ℓ₁ ⊔ ℓ₀)
UniqueIdHomomorphisms C = ∀ {a} → (f : Hom C a a) → f ≡ id C {a}


-- -----------------------------------------------------------------------------
-- Definition of a monad extended with a category to repredent an alternative 
-- formalization of supermonads.
-- -----------------------------------------------------------------------------

record SupermonadC {ℓ₀ ℓ₁ ℓF : Level} (C : Category {ℓ₀} {ℓ₁}) (M : ∀ {a b} → Hom C a b → TyCon) : Set (lsuc ℓF ⊔ ℓ₀ ⊔ ℓ₁) where
  _∘_ = comp C
  field
    _>>=_ : ∀ {α β : Type} {a b c : Obj C} {i : Hom C a b} {j : Hom C b c} → (M i α → (α → M j β) → M (j ∘ i) β) 
    
    return : ∀ {α : Type} {a : Obj C} → (α → M (id C {a}) α)
    
    functor : {a b : Obj C} (f : Hom C a b) → ConstrainedFunctor {ℓ = ℓF} (M f)
    
    -- The supermonad version of the right identity law.
    right-id : {α β : Type} {a b : Obj C} {j : Hom C a b}
        → (a : α) → (k : α → M j β)
        → subst (λ X → M X β) (catIdL C) (return a >>= k) ≡ k a
    
    -- The supermonad version of the left identity law.
    left-id : {α : Type} {a b : Obj C} {i : Hom C a b}
        → (m : M i α)
        → subst (λ X → M X α) (catIdR C) (m >>= return) ≡ m
    
    -- The supermonad version of the associativity law.
    assoc : {α β γ : Type} {a b c d : Obj C}
          → {i : Hom C a b} {j : Hom C b c} {k : Hom C c d}
          → (m : M i α) → (f : α → M j β) → (g : β → M k γ)
          → subst (λ X → M X γ) (catAssoc C) ((m >>= f) >>= g) ≡ (m >>= (λ x → f x >>= g))
    
    monadFmap : {α β : Type} {a b : Obj C}
              → {i : Hom C a b}
              → (fcts : ConstrainedFunctor.FunctorCts (functor i) α β)
              → (m : M i α) → (k : α → β)
              → subst (λ X → M X β) (catIdR C {f = i}) (m >>= (return ∘F k)) ≡ ConstrainedFunctor.fmap (functor i) fcts k m
    
  _>>_ : {α β : Type} {a b c : Obj C}
           → {i : Hom C a b} {j : Hom C b c}
           → M i α → M j β → M (j ∘ i) β
  _>>_ ma mb = ma >>= (λ _ → mb)

  sequence = _>>_
  bind = _>>=_

