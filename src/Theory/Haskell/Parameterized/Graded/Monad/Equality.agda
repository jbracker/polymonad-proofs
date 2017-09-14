
open import Level
open import Function hiding ( id ; _∘_ )

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( refl to hrefl ; proof-irrelevance to het-proof-irrelevance )

open import Congruence
open import Extensionality
open import Theory.Monoid
open import Theory.Category.Definition
open import Theory.Functor.Definition
open import Theory.Functor.Composition
open import Theory.Natural.Transformation

open import Theory.Haskell.Parameterized.Graded.Monad

module Theory.Haskell.Parameterized.Graded.Monad.Equality where 

open Monoid
open Category
open NaturalTransformation renaming ( η to nat-η )

graded-monad-eq : {ℓMon ℓC₀ ℓC₁ : Level} 
                → {C : Category {ℓC₀} {ℓC₁}} 
                → {Mon : Set ℓMon}
                → {monoid : Monoid Mon}
                → {M : Mon → Functor C C}
                → {η₀ : NaturalTransformation (Id[ C ]) (M (ε monoid))}
                → {η₁ : NaturalTransformation (Id[ C ]) (M (ε monoid))}
                → {μ₀ : {i j : Mon} → NaturalTransformation ([ M i ]∘[ M j ]) (M (_∙_ monoid i j))}
                → {μ₁ : {i j : Mon} → NaturalTransformation ([ M i ]∘[ M j ]) (M (_∙_ monoid i j))}
                → {μ-coher₀ : {i j k : Mon} {x : Obj C}
                            → _∘_ C (nat-η (μ₀ {i} {_∙_ monoid j k}) x) ([ M i ]₁ (nat-η (μ₀ {j} {k}) x)) ≅ _∘_ C (nat-η (μ₀ {_∙_ monoid i j} {k}) x) (nat-η (μ₀ {i} {j}) ([ M k ]₀ x))}
                → {μ-coher₁ : {i j k : Mon} {x : Obj C}
                            → _∘_ C (nat-η (μ₁ {i} {_∙_ monoid j k}) x) ([ M i ]₁ (nat-η (μ₁ {j} {k}) x)) ≅ _∘_ C (nat-η (μ₁ {_∙_ monoid i j} {k}) x) (nat-η (μ₁ {i} {j}) ([ M k ]₀ x))}
                → {η-lcoher₀ : {i : Mon} {x : Obj C}
                             → _∘_ C (nat-η (μ₀ {i} {ε monoid}) x) ([ M i ]₁ (nat-η η₀ x)) ≅ nat-η (Id⟨ M i ⟩) x}
                → {η-lcoher₁ : {i : Mon} {x : Obj C}
                             → _∘_ C (nat-η (μ₁ {i} {ε monoid}) x) ([ M i ]₁ (nat-η η₁ x)) ≅ nat-η (Id⟨ M i ⟩) x}
                → {η-rcoher₀ : {i : Mon} {x : Obj C}
                             → _∘_ C (nat-η (μ₀ {ε monoid} {i}) x) (nat-η η₀ ([ M i ]₀ x)) ≅ nat-η (Id⟨ M i ⟩) x}
                → {η-rcoher₁ : {i : Mon} {x : Obj C}
                             → _∘_ C (nat-η (μ₁ {ε monoid} {i}) x) (nat-η η₁ ([ M i ]₀ x)) ≅ nat-η (Id⟨ M i ⟩) x}
                → (η₀ ≡ η₁)
                → ((λ {i j : Mon} → μ₀ {i} {j}) ≡ μ₁)
                → graded-monad {C = C} {Mon} {monoid} {M} η₀ μ₀ μ-coher₀ η-lcoher₀ η-rcoher₀ ≡ graded-monad {C = C} {Mon} {monoid} {M} η₁ μ₁ μ-coher₁ η-lcoher₁ η-rcoher₁
graded-monad-eq {ℓMon} {ℓC₀} {ℓC₁} {C} {Mon} {monoid} {M} {η} {.η} {μ} {.μ} {μ-coher₀} {μ-coher₁} {η-lcoher₀} {η-lcoher₁} {η-rcoher₀} {η-rcoher₁} refl refl
  = cong₃ (graded-monad {C = C} {Mon} {monoid} {M} η μ) eq1 eq2 eq3
  where
    eq1 : (λ {i j k} {x} → μ-coher₀ {i} {j} {k} {x}) ≡ μ-coher₁
    eq1 = implicit-fun-ext 
        $ λ i → implicit-fun-ext 
        $ λ j → implicit-fun-ext 
        $ λ k → implicit-fun-ext 
        $ λ x → het-proof-irrelevance μ-coher₀ μ-coher₁
    
    eq2 : (λ {i} {x} → η-lcoher₀ {i} {x}) ≡ η-lcoher₁
    eq2 = implicit-fun-ext 
        $ λ i → implicit-fun-ext 
        $ λ x → het-proof-irrelevance η-lcoher₀ η-lcoher₁
    
    eq3 : (λ {i : Mon} {x : Obj C} → η-rcoher₀ {i} {x}) ≡ η-rcoher₁
    eq3 = implicit-fun-ext 
        $ λ (i : Mon) → implicit-fun-ext
        $ λ (x : Obj C) → het-proof-irrelevance (η-rcoher₀ {i} {x}) (η-rcoher₁ {i} {x})

