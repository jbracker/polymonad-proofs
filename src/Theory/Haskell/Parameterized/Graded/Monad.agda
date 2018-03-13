
open import Level

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality

open import Theory.Monoid
open import Theory.Category.Definition
open import Theory.Functor.Definition
open import Theory.Functor.Composition
open import Theory.Natural.Transformation
 
module Theory.Haskell.Parameterized.Graded.Monad where

record GradedMonad {ℓMon ℓC₀ ℓC₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {Mon : Set ℓMon} (monoid : Monoid Mon) (M : Mon → Functor C C) : Set (ℓMon ⊔ ℓC₀ ⊔ ℓC₁) where
  constructor graded-monad
 
  open Monoid monoid
  open Category C
  open NaturalTransformation renaming ( η to nat-η )

  field
    -- return ∷ α → M ε α
    η : NaturalTransformation (Id[ C ]) (M ε)
    
    -- join ∷ M i (M j α) → M (i ∙ j) α
    μ : {i j : Mon} → NaturalTransformation ([ M i ]∘[ M j ]) (M (i ∙ j))
  
  field
    -- μ ∘ T₁μ ≡ μ ∘ μT₀
    μ-coher : {i j k : Mon} {x : Obj}
            → nat-η (μ {i} {j ∙ k}) x ∘ [ M i ]₁ (nat-η (μ {j} {k}) x) ≅ nat-η (μ {i ∙ j} {k}) x ∘ nat-η (μ {i} {j}) ([ M k ]₀ x)
  
  field
    -- μ ∘ Tη ≡ 1ₜ
    η-left-coher : {i : Mon} {x : Obj}
                 → nat-η (μ {i} {ε}) x ∘ [ M i ]₁ (nat-η η x) ≅ nat-η (Id⟨ M i ⟩) x
    
  field
    -- μ ∘ ηT ≡ 1ₜ
    η-right-coher : {i : Mon} {x : Obj}
                  → nat-η (μ {ε} {i}) x ∘ nat-η η ([ M i ]₀ x) ≅ nat-η (Id⟨ M i ⟩) x

