
open import Level
open import Function renaming ( id to idF ; _∘_ to _∘F_ )

open import Relation.Binary.PropositionalEquality

open import Theory.Category.Definition

module Theory.Category.Examples.SetCat where 

-- Category of sets and functions.
setCategory : {ℓ : Level} → Category {ℓ₀ = suc ℓ} {ℓ}
setCategory {ℓ} = record
  { Obj = Set ℓ
  ; Hom = λ a b → (a → b)
  ; _∘_ = λ f g → f ∘F g
  ; id = idF
  ; assoc = refl
  ; left-id = refl
  ; right-id = refl
  } 
