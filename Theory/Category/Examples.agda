
module Theory.Category.Examples where 

-- Stdlib
open import Level renaming ( suc to lsuc ; zero to lzero )
open import Function renaming ( id to idF ; _∘_ to _∘F_ )
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Utilities
open import Theory.Category
open import Theory.Functor

-- The unit category with exactly one element and one morphism.
unitCategory : {ℓ₀ ℓ₁ : Level} → Category {ℓ₀ = ℓ₀} {ℓ₁ = ℓ₁}
unitCategory = record
  { Obj = Lift ⊤
  ; Hom = λ _ _ → Lift ⊤
  ; _∘_ = λ _ _ → lift tt
  ; id = lift tt
  ; assoc = refl
  ; idL = refl
  ; idR = refl
  }

-- Category of sets and functions.
setCategory : {ℓ₀ : Level} → Category {ℓ₀ = lsuc ℓ₀}
setCategory {ℓ₀ = ℓ₀} = record
  { Obj = Set ℓ₀
  ; Hom = λ a b → (a → b)
  ; _∘_ = λ f g → f ∘F g
  ; id = idF
  ; assoc = refl
  ; idL = refl
  ; idR = refl
  }

-- Category of categories and functors.
catCategory : {ℓ₀ ℓ₁ : Level} → Category {ℓ₀ = lsuc (ℓ₀ ⊔ ℓ₁)} {ℓ₁ = ℓ₀ ⊔ ℓ₁}
catCategory {ℓ₀} {ℓ₁} = record
  { Obj = Category {ℓ₀} {ℓ₁}
  ; Hom = λ C D → Functor C D
  ; _∘_ = [_]∘[_]
  ; id = λ {C} → Id[ C ]
  ; assoc = λ {a b c d} {f} {g} {h} → assoc {a} {b} {c} {d} {f} {g} {h}
  ; idL = idL
  ; idR = idR
  } where
    assoc : {a b c d : Category} {f : Functor a b} {g : Functor b c} {h : Functor c d} 
          → [ h ]∘[ [ g ]∘[ f ] ] ≡ [ [ h ]∘[ g ] ]∘[ f ]
    assoc = propEqFunctor refl refl
    
    idL : {a b : Category} {f : Functor a b} → [ Id[ b ] ]∘[ f ] ≡ f
    idL = propEqFunctor refl refl

    idR : {a b : Category} {f : Functor a b} → [ f ]∘[ Id[ a ] ] ≡ f
    idR = refl
