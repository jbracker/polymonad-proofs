
open import Level

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality

open import Theory.Category.Definition
open import Theory.Functor.Definition
open import Theory.Functor.Composition
open import Theory.Natural.Transformation

module Theory.Haskell.Parameterized.Indexed.Monad where

open Category

record IndexedMonad {ℓI₀ ℓI₁ ℓC₀ ℓC₁ : Level} {C : Category {ℓC₀} {ℓC₁}} (I : Category {ℓI₀} {ℓI₁}) (M : {i j : Obj I} → Hom I i j → Functor C C) : Set (ℓC₀ ⊔ ℓC₁ ⊔ ℓI₀ ⊔ ℓI₁) where
  constructor indexedMonad
  
  open NaturalTransformation renaming ( η to nat-η )
  
  private
    _∘I_ = _∘_ I
    _∘C_ = _∘_ C

  field
    -- return ∷ α → M i i α
    η : (i : Obj I) → NaturalTransformation (Id[ C ]) (M (id I {i}))
    
    -- join ∷ M i j (M j k α) → M i k α
    μ : {i j k : Obj I} (f : Hom I i j) (g : Hom I j k) → NaturalTransformation ([ M f ]∘[ M g ]) (M (g ∘I f))
  
  field
    -- μ ∘ T₁μ ≡ μ ∘ μT₀
    μ-coher : {i j k l : Obj I} {f : Hom I i j} {g : Hom I j k} {h : Hom I k l} {x : Obj C}
            → nat-η (μ f (h ∘I g)) x ∘C [ M f ]₁ (nat-η (μ g h) x) ≅ nat-η (μ (g ∘I f) h) x ∘C nat-η (μ f g) ([ M h ]₀ x)
  
  field
    -- μ ∘ Tη ≡ 1ₜ
    η-left-coher : {i j : Obj I} {f : Hom I i j} {x : Obj C}
                 → nat-η (μ f (id I)) x ∘C [ M f ]₁ (nat-η (η j) x) ≅ nat-η (Id⟨ M f ⟩) x
    
  field
    -- μ ∘ ηT ≡ 1ₜ
    η-right-coher : {i j : Obj I} {f : Hom I i j} {x : Obj C}
                  → nat-η (μ (id I) f) x ∘C nat-η (η i) ([ M f ]₀ x) ≅ nat-η (Id⟨ M f ⟩) x

