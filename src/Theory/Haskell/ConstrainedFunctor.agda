 
module Theory.Haskell.ConstrainedFunctor where

open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Level renaming ( suc to lsuc ; zero to lzero)
open import Data.Unit
open import Data.Product hiding ( map )
open import Relation.Binary.PropositionalEquality

open import Haskell hiding ( Hask )
open import Utilities
open import ProofIrrelevance
open import Theory.Category
open import Theory.Category.Subcategory
open import Theory.Category.Subcategory.Examples
open import Theory.Category.Dependent
open import Theory.Functor
open import Theory.Haskell.Constrained

record ConstrainedFunctor {ℓ ℓ₀ ℓ₁ : Level} : Set (lsuc (ℓ ⊔ ℓ₀ ⊔ ℓ₁)) where
  field
    Cts : ConstraintCategory {ℓ} {ℓ₀} {ℓ₁}
  
  open DependentCategory Cts
  open Category dep-category
  
  F : Obj → Set ℓ
  F x = proj₁ x

  field
    map : {α β : Obj} → Hom α β → F α → F β
    
    functor-id : {α : Obj} → map {α} {α} id ≡ idF
    
    functor-compose : {α β γ : Obj} {f : Hom α β} {g : Hom β γ} 
                    → map (g ∘ f) ≡ map g ∘F map f
    
    unique-insts : UniqueInstances Cts
  
  -- The actual constrained functor.
  CtFunctor : Functor (ConstrainedHask Cts) (Hask {ℓ})
  CtFunctor = functor F map functor-id functor-compose

