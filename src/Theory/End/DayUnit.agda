 
open import Level


open import Theory.Category.Definition
open import Theory.Category.Examples
open import Theory.Category.Monoidal
open import Theory.Functor.Definition
open import Theory.Functor.Examples.HomFunctor

module Theory.End.DayUnit where

open Category

dayUnit : {ℓC₀ ℓC₁ ℓSet : Level} {C : Category {ℓC₀} {ℓC₁}} 
        → (CMon : MonoidalCategory C) 
        → Obj [ C , setCategory {ℓSet ⊔ ℓC₁ ⊔ ℓC₀} ]
dayUnit {ℓC₀} {ℓC₁} {ℓSet} {C} CMon = homFunctor ℓSet (MonoidalCategory.unit CMon)
