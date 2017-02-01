 
module Theory.ConstrainedFunctor where

open import Function
open import Level renaming ( suc to lsuc ; zero to lzero)
open import Data.Unit
open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Utilities
open import Theory.Category
open import Theory.Subcategory
open import Theory.Functor
open import Theory.InclusionFunctor

-- A constrained functor consists of a category of constraints 'Cts', the category 'C' it works on and 
-- an injective inclusion functor 'IncF' that maps the constraints in 'Cts' to elements in 'C'.
-- In other words: 
--   If (IncF : Cts ⇒ S) is the injective inclusion functor then S ⊑ C is a subcategory of C.
--   Thus the resulting constrained functor has type S ⇒ C.
ConstrainedFunctor : {ℓCt₀ ℓCt₁ ℓC₀ ℓC₁ : Level} 
                   → (Cts : Category {ℓCt₀} {ℓCt₁}) 
                   → (C : Category {ℓC₀} {ℓC₁}) 
                   → (IncF : Functor Cts C) 
                   → IsInjectiveFunctor IncF 
                   → Set (ℓC₁ ⊔ ℓC₀ ⊔ ℓCt₁ ⊔ ℓCt₀)
ConstrainedFunctor CtCat C IncF (injF₀ , injF₁) = Functor (Subcategory→Category (InclusionFunctor→LiftSubcategory IncF injF₀ injF₁)) C

-- Construct the constrained functor induced by the given arguments.
mkConstrainedFunctor : {ℓCt₀ ℓCt₁ ℓC₀ ℓC₁ : Level} 
                     → (Cts : Category {ℓCt₀} {ℓCt₁}) 
                     → (C : Category {ℓC₀} {ℓC₁}) 
                     → (IncF : Functor Cts C) 
                     → (injF : IsInjectiveFunctor IncF)
                     → ConstrainedFunctor Cts C IncF injF
mkConstrainedFunctor Cts C IncF (injF₀ , injF₁) = functor (lower ∘ proj₁) (lower ∘ proj₁) refl refl
