 
module Theory.Haskell.Constrained.Functor where

open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Level renaming ( suc to lsuc ; zero to lzero)
open import Data.Unit
open import Data.Product hiding ( map )
open import Relation.Binary.PropositionalEquality

open import Haskell
open import Utilities
open import ProofIrrelevance
open import Theory.Category
open import Theory.Category.Subcategory
open import Theory.Category.Subcategory.Examples
open import Theory.Category.Concrete
open import Theory.Category.Dependent
open import Theory.Functor
open import Theory.Haskell.Constrained

record ConstrainedFunctor {ℓ ℓCt₀ ℓCt₁ : Level} (CC : ConstraintCategory {ℓ} {ℓCt₀} {ℓCt₁}) : Set (lsuc (ℓ ⊔ ℓCt₀ ⊔ ℓCt₁)) where
  open DependentCategory CC
  open Category DepCat
  
  Cts = CC
  
  field
    F : Obj → Set ℓ
    
    map : {α β : Obj} → Hom α β → F α → F β
    
    functor-id : {α : Obj} → map {α} {α} id ≡ idF
    
    functor-compose : {α β γ : Obj} {f : Hom α β} {g : Hom β γ} 
                    → map (g ∘ f) ≡ map g ∘F map f
    
    -- We do not force the instance for each type to be unique,
    -- because Haskell (or at least GHC) does not enforce the 
    -- uniqueness of an instance and reasonable extensions such
    -- as OverlappingInstances violate this condition anyway.
    --unique-instances : UniqueInstances Cts
  
  -- The actual constrained functor.
  CtFunctor : Functor (ConstrainedHask Cts) (Hask {ℓ})
  CtFunctor = functor F map functor-id functor-compose

