
open import Level

open import Relation.Binary.PropositionalEquality

open import Theory.Category.Definition
open import Theory.Functor.Definition
open import Theory.Functor.Composition
open import Theory.Natural.Transformation

module Theory.Haskell.Parameterized.Indexed.Monad where

record IndexedMonad {ℓIxs ℓC₀ ℓC₁ : Level} {C : Category {ℓC₀} {ℓC₁}} (Ixs : Set ℓIxs) (M : Ixs → Ixs → Functor C C) : Set (ℓIxs ⊔ ℓC₀ ⊔ ℓC₁) where
  constructor indexed-monad
 
  open Category C
  open NaturalTransformation renaming ( η to nat-η )

  field
    -- return ∷ α → M i i α
    η : {i : Ixs} → NaturalTransformation (Id[ C ]) (M i i)
    
    -- join ∷ M i j (M j k α) → M i k α
    μ : {i j k : Ixs} → NaturalTransformation ([ M j k ]∘[ M i j ]) (M i k)
  
  field
    -- μ ∘ T₁μ ≡ μ ∘ μT₀
    μ-coher : {i j k l : Ixs} {x : Obj}
            → nat-η (μ {i} {k} {l}) x ∘ [ M k l ]₁ (nat-η (μ {i} {j} {k}) x) ≡ nat-η (μ {i} {j} {l}) x ∘ nat-η (μ {j} {k} {l}) ([ M i j ]₀ x)
  
  field
    -- μ ∘ Tη ≡ 1ₜ
    η-left-coher : {i j : Ixs} {x : Obj}
                 → nat-η (μ {i} {i} {j}) x ∘ [ M i j ]₁ (nat-η η x) ≡ nat-η (Id⟨ M i j ⟩) x
    
  field
    -- μ ∘ ηT ≡ 1ₜ
    η-right-coher : {i j : Ixs} {x : Obj}
                  → nat-η (μ {i} {j} {j}) x ∘ nat-η (η {j}) ([ M i j ]₀ x) ≡ nat-η (Id⟨ M i j ⟩) x

