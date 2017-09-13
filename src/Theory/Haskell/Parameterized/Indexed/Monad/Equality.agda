
open import Level
open import Function hiding ( id ; _∘_ )

open import Relation.Binary.PropositionalEquality

open import Congruence
open import Extensionality
open import Theory.Category.Definition
open import Theory.Functor.Definition
open import Theory.Functor.Composition
open import Theory.Natural.Transformation

open import Theory.Haskell.Parameterized.Indexed.Monad

module Theory.Haskell.Parameterized.Indexed.Monad.Equality where 

open Category
open NaturalTransformation renaming ( η to nat-η )

indexed-monad-eq : {ℓIxs ℓC₀ ℓC₁ : Level} 
                 → {C : Category {ℓC₀} {ℓC₁}} 
                 → {Ixs : Set ℓIxs} 
                 → {M : Ixs → Ixs → Functor C C}
                 → {η₀ : {i : Ixs} → NaturalTransformation (Id[ C ]) (M i i)}
                 → {η₁ : {i : Ixs} → NaturalTransformation (Id[ C ]) (M i i)}
                 → {μ₀ : {i j k : Ixs} → NaturalTransformation ([ M j k ]∘[ M i j ]) (M i k)}
                 → {μ₁ : {i j k : Ixs} → NaturalTransformation ([ M j k ]∘[ M i j ]) (M i k)}
                 → {μ-coher₀ : {i j k l : Ixs} {x : Obj C}
                             → _∘_ C (nat-η (μ₀ {i} {k} {l}) x) ([ M k l ]₁ (nat-η (μ₀ {i} {j} {k}) x)) ≡ _∘_ C (nat-η (μ₀ {i} {j} {l}) x) (nat-η (μ₀ {j} {k} {l}) ([ M i j ]₀ x))}
                 → {μ-coher₁ : {i j k l : Ixs} {x : Obj C}
                             → _∘_ C (nat-η (μ₁ {i} {k} {l}) x) ([ M k l ]₁ (nat-η (μ₁ {i} {j} {k}) x)) ≡ _∘_ C (nat-η (μ₁ {i} {j} {l}) x) (nat-η (μ₁ {j} {k} {l}) ([ M i j ]₀ x))}
                 → {η-lcoher₀ : {i j : Ixs} {x : Obj C}
                              → _∘_ C (nat-η (μ₀ {i} {i} {j}) x) ([ M i j ]₁ (nat-η η₀ x)) ≡ nat-η (Id⟨ M i j ⟩) x}
                 → {η-lcoher₁ : {i j : Ixs} {x : Obj C}
                              → _∘_ C (nat-η (μ₁ {i} {i} {j}) x) ([ M i j ]₁ (nat-η η₁ x)) ≡ nat-η (Id⟨ M i j ⟩) x}
                 → {η-rcoher₀ : {i j : Ixs} {x : Obj C}
                              → _∘_ C (nat-η (μ₀ {i} {j} {j}) x) (nat-η (η₀ {j}) ([ M i j ]₀ x)) ≡ nat-η (Id⟨ M i j ⟩) x}
                 → {η-rcoher₁ : {i j : Ixs} {x : Obj C}
                              → _∘_ C (nat-η (μ₁ {i} {j} {j}) x) (nat-η (η₁ {j}) ([ M i j ]₀ x)) ≡ nat-η (Id⟨ M i j ⟩) x}
                 → ((λ {i} → η₀ {i}) ≡ η₁)
                 → ((λ {i j k} → μ₀ {i} {j} {k}) ≡ μ₁)
                 → indexed-monad {C = C} {Ixs} {M} η₀ μ₀ μ-coher₀ η-lcoher₀ η-rcoher₀ ≡ indexed-monad {C = C} {Ixs} {M} η₁ μ₁ μ-coher₁ η-lcoher₁ η-rcoher₁
indexed-monad-eq {ℓIxs} {ℓC₀} {ℓC₁} {C} {Ixs} {M} {η} {.η} {μ} {.μ} {μ-coher₀} {μ-coher₁} {η-lcoher₀} {η-lcoher₁} {η-rcoher₀} {η-rcoher₁} refl refl
  = cong₃ (indexed-monad {C = C} {Ixs} {M} η μ) eq1 eq2 eq3
  where
    eq1 : (λ {i j k l} {x} → μ-coher₀ {i} {j} {k} {l} {x}) ≡ μ-coher₁
    eq1 = implicit-fun-ext 
        $ λ i → implicit-fun-ext 
        $ λ j → implicit-fun-ext 
        $ λ k → implicit-fun-ext 
        $ λ l → implicit-fun-ext 
        $ λ x → proof-irrelevance μ-coher₀ μ-coher₁
    
    eq2 : (λ {i j} {x} → η-lcoher₀ {i} {j} {x}) ≡ η-lcoher₁
    eq2 = implicit-fun-ext 
        $ λ i → implicit-fun-ext 
        $ λ j → implicit-fun-ext 
        $ λ x → proof-irrelevance η-lcoher₀ η-lcoher₁
    
    eq3 : (λ {i j} {x} → η-rcoher₀ {i} {j} {x}) ≡ η-rcoher₁
    eq3 = implicit-fun-ext 
        $ λ i → implicit-fun-ext 
        $ λ j → implicit-fun-ext 
        $ λ x → proof-irrelevance η-rcoher₀ η-rcoher₁
