
open import Level renaming ( zero to lzero ; suc to lsuc )

open import Data.Product renaming ( _,_ to _,'_ )

open import Relation.Binary.PropositionalEquality

open import Theory.Category hiding ( category )
open import Theory.Functor
import Theory.Functor.Examples
open import Theory.Natural.Isomorphism
open import Theory.Natural.Transformation

module Theory.Category.Closed where

record ClosedCategory {ℓ₀ ℓ₁ : Level} (C : Category {ℓ₀} {ℓ₁}) : Set (lsuc (ℓ₀ ⊔ ℓ₁)) where
  constructor closedCategory

  category = C
  open Category
  
  field
    InternalHom : Functor (C op ×C C) C
    
    I : Obj C
  
  open Theory.Functor.Examples.BiFunctorApplication
  
  field
    i : NaturalIsomorphism Id[ C ] ([ I ,-] InternalHom)
    -- TODO
