
open import Level
open import Function hiding ( id ; _∘_ )

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( refl to hrefl ; proof-irrelevance to het-proof-irrelevance )

open import Congruence
open import Extensionality
open import Theory.Category.Definition
open import Theory.Functor.Definition
open import Theory.Functor.Composition
open import Theory.Natural.Transformation

open import Theory.Haskell.Parameterized.Indexed.Monad

module Theory.Haskell.Parameterized.Indexed.Monad.Equality
  {ℓI₀ ℓI₁ ℓC₀ ℓC₁ : Level} 
  {C : Category {ℓC₀} {ℓC₁}} {I : Category {ℓI₀} {ℓI₁}} where 

open Category renaming ( id to cat-id )
open NaturalTransformation renaming ( η to nat-η )

private
  _∘I_ = _∘_ I
  _∘C_ = _∘_ C

{-
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
-}

abstract
  indexed-monad-eq : {M : {i j : Obj I} → Hom I i j → Functor C C}
                   → {η₀ : (i : Obj I) → NaturalTransformation (Id[ C ]) (M (cat-id I {i}))}
                   → {η₁ : (i : Obj I) → NaturalTransformation (Id[ C ]) (M (cat-id I {i}))}
                   → {μ₀ : {i j k : Obj I} → (f : Hom I i j) (g : Hom I j k) → NaturalTransformation ([ M f ]∘[ M g ]) (M (g ∘I f))}
                   → {μ₁ : {i j k : Obj I} → (f : Hom I i j) (g : Hom I j k) → NaturalTransformation ([ M f ]∘[ M g ]) (M (g ∘I f))}
                   → {μ-coher₀ : {i j k l : Obj I} {f : Hom I i j} {g : Hom I j k} {h : Hom I k l} {x : Obj C}
                               → (nat-η (μ₀ f (h ∘I g)) x) ∘C ([ M f ]₁ (nat-η (μ₀ g h) x)) ≅ (nat-η (μ₀ (g ∘I f) h) x) ∘C (nat-η (μ₀ f g) ([ M h ]₀ x))}
                   → {μ-coher₁ : {i j k l : Obj I} {f : Hom I i j} {g : Hom I j k} {h : Hom I k l} {x : Obj C}
                               → (nat-η (μ₁ f (h ∘I g)) x) ∘C ([ M f ]₁ (nat-η (μ₁ g h) x)) ≅ (nat-η (μ₁ (g ∘I f) h) x) ∘C (nat-η (μ₁ f g) ([ M h ]₀ x))}
                   → {η-lcoher₀ : {i j : Obj I} {f : Hom I i j} {x : Obj C}
                                → _∘_ C (nat-η (μ₀ f (cat-id I {j})) x) ([ M f ]₁ (nat-η (η₀ j) x)) ≅ nat-η (Id⟨ M f ⟩) x}
                   → {η-lcoher₁ : {i j : Obj I} {f : Hom I i j} {x : Obj C}
                                → _∘_ C (nat-η (μ₁ f (cat-id I {j})) x) ([ M f ]₁ (nat-η (η₁ j) x)) ≅ nat-η (Id⟨ M f ⟩) x}
                   → {η-rcoher₀ : {i j : Obj I} {f : Hom I i j} {x : Obj C}
                                → _∘_ C (nat-η (μ₀ (cat-id I {i}) f) x) (nat-η (η₀ i) ([ M f ]₀ x)) ≅ nat-η (Id⟨ M f ⟩) x}
                   → {η-rcoher₁ : {i j : Obj I} {f : Hom I i j} {x : Obj C}
                                → _∘_ C (nat-η (μ₁ (cat-id I {i}) f) x) (nat-η (η₁ i) ([ M f ]₀ x)) ≅ nat-η (Id⟨ M f ⟩) x}
                   → (η₀ ≡ η₁)
                   → ((λ {i j k} → μ₀ {i} {j} {k}) ≡ μ₁)
                   → indexedMonad {C = C} {I = I} {M} η₀ μ₀ μ-coher₀ η-lcoher₀ η-rcoher₀ ≡ indexedMonad {C = C} {I = I} {M} η₁ μ₁ μ-coher₁ η-lcoher₁ η-rcoher₁
  indexed-monad-eq {M} {η} {.η} {μ} {.μ} {μ-coher₀} {μ-coher₁} {η-lcoher₀} {η-lcoher₁} {η-rcoher₀} {η-rcoher₁} refl refl
    = cong₃ (indexedMonad {C = C} {I = I} {M} η μ) eq1 eq2 eq3
    where
      abstract
        eq1 : (λ {i j k l} {f} {g} {h} {x} → μ-coher₀ {i} {j} {k} {l} {f} {g} {h} {x}) ≡ μ-coher₁
        eq1 = implicit-fun-ext 
            $ λ i → implicit-fun-ext 
            $ λ j → implicit-fun-ext 
            $ λ k → implicit-fun-ext 
            $ λ l → implicit-fun-ext 
            $ λ f → implicit-fun-ext 
            $ λ g → implicit-fun-ext 
            $ λ h → implicit-fun-ext 
            $ λ x → het-proof-irrelevance μ-coher₀ μ-coher₁
      
      abstract
        eq2 : (λ {i j} {f} {x} → η-lcoher₀ {i} {j} {f} {x}) ≡ η-lcoher₁
        eq2 = implicit-fun-ext 
            $ λ i → implicit-fun-ext 
            $ λ j → implicit-fun-ext 
            $ λ f → implicit-fun-ext 
            $ λ x → het-proof-irrelevance η-lcoher₀ η-lcoher₁
      
      abstract
        eq3 : (λ {i j} {f} {x} → η-rcoher₀ {i} {j} {f} {x}) ≡ η-rcoher₁
        eq3 = implicit-fun-ext 
            $ λ i → implicit-fun-ext 
            $ λ j → implicit-fun-ext 
            $ λ f → implicit-fun-ext 
            $ λ x → het-proof-irrelevance η-rcoher₀ η-rcoher₁
        
abstract
  het-indexed-monad-eq : {M₀ : {i j : Obj I} → Hom I i j → Functor C C}
                       → {M₁ : {i j : Obj I} → Hom I i j → Functor C C}
                       → {η₀ : (i : Obj I) → NaturalTransformation (Id[ C ]) (M₀ (cat-id I {i}))}
                       → {η₁ : (i : Obj I) → NaturalTransformation (Id[ C ]) (M₁ (cat-id I {i}))}
                       → {μ₀ : {i j k : Obj I} → (f : Hom I i j) (g : Hom I j k) → NaturalTransformation ([ M₀ f ]∘[ M₀ g ]) (M₀ (g ∘I f))}
                       → {μ₁ : {i j k : Obj I} → (f : Hom I i j) (g : Hom I j k) → NaturalTransformation ([ M₁ f ]∘[ M₁ g ]) (M₁ (g ∘I f))}
                       → {μ-coher₀ : {i j k l : Obj I} {f : Hom I i j} {g : Hom I j k} {h : Hom I k l} {x : Obj C}
                                   → (nat-η (μ₀ f (h ∘I g)) x) ∘C ([ M₀ f ]₁ (nat-η (μ₀ g h) x)) ≅ (nat-η (μ₀ (g ∘I f) h) x) ∘C (nat-η (μ₀ f g) ([ M₀ h ]₀ x))}
                       → {μ-coher₁ : {i j k l : Obj I} {f : Hom I i j} {g : Hom I j k} {h : Hom I k l} {x : Obj C}
                                   → (nat-η (μ₁ f (h ∘I g)) x) ∘C ([ M₁ f ]₁ (nat-η (μ₁ g h) x)) ≅ (nat-η (μ₁ (g ∘I f) h) x) ∘C (nat-η (μ₁ f g) ([ M₁ h ]₀ x))}
                       → {η-lcoher₀ : {i j : Obj I} {f : Hom I i j} {x : Obj C}
                                    → _∘_ C (nat-η (μ₀ f (cat-id I {j})) x) ([ M₀ f ]₁ (nat-η (η₀ j) x)) ≅ nat-η (Id⟨ M₀ f ⟩) x}
                       → {η-lcoher₁ : {i j : Obj I} {f : Hom I i j} {x : Obj C}
                                    → _∘_ C (nat-η (μ₁ f (cat-id I {j})) x) ([ M₁ f ]₁ (nat-η (η₁ j) x)) ≅ nat-η (Id⟨ M₁ f ⟩) x}
                       → {η-rcoher₀ : {i j : Obj I} {f : Hom I i j} {x : Obj C}
                                    → _∘_ C (nat-η (μ₀ (cat-id I {i}) f) x) (nat-η (η₀ i) ([ M₀ f ]₀ x)) ≅ nat-η (Id⟨ M₀ f ⟩) x}
                       → {η-rcoher₁ : {i j : Obj I} {f : Hom I i j} {x : Obj C}
                                    → _∘_ C (nat-η (μ₁ (cat-id I {i}) f) x) (nat-η (η₁ i) ([ M₁ f ]₀ x)) ≅ nat-η (Id⟨ M₁ f ⟩) x}
                       → ((λ {i j} → M₀ {i} {j}) ≡ M₁)
                       → (η₀ ≅ η₁)
                       → ((λ {i j k} → μ₀ {i} {j} {k}) ≅ (λ {i j k} → μ₁ {i} {j} {k}))
                       → indexedMonad {C = C} {I = I} {M₀} η₀ μ₀ μ-coher₀ η-lcoher₀ η-rcoher₀ ≅ indexedMonad {C = C} {I = I} {M₁} η₁ μ₁ μ-coher₁ η-lcoher₁ η-rcoher₁
  het-indexed-monad-eq {M} {.M} {η} {.η} {μ} {.μ} {μ-coher₀} {μ-coher₁} {η-lcoher₀} {η-lcoher₁} {η-rcoher₀} {η-rcoher₁} refl hrefl hrefl
    = ≡-to-≅ $ cong₃ (indexedMonad {C = C} {I = I} {M} η μ) eq1 eq2 eq3
    where
      abstract
        eq1 : (λ {i j k l} {f} {g} {h} {x} → μ-coher₀ {i} {j} {k} {l} {f} {g} {h} {x}) ≡ μ-coher₁
        eq1 = implicit-fun-ext 
            $ λ i → implicit-fun-ext 
            $ λ j → implicit-fun-ext 
            $ λ k → implicit-fun-ext 
            $ λ l → implicit-fun-ext 
            $ λ f → implicit-fun-ext 
            $ λ g → implicit-fun-ext 
            $ λ h → implicit-fun-ext 
            $ λ x → het-proof-irrelevance μ-coher₀ μ-coher₁
      
      abstract
        eq2 : (λ {i j} {f} {x} → η-lcoher₀ {i} {j} {f} {x}) ≡ η-lcoher₁
        eq2 = implicit-fun-ext 
            $ λ i → implicit-fun-ext 
            $ λ j → implicit-fun-ext 
            $ λ f → implicit-fun-ext 
            $ λ x → het-proof-irrelevance η-lcoher₀ η-lcoher₁
      
      abstract
        eq3 : (λ {i j} {f} {x} → η-rcoher₀ {i} {j} {f} {x}) ≡ η-rcoher₁
        eq3 = implicit-fun-ext 
            $ λ i → implicit-fun-ext 
            $ λ j → implicit-fun-ext 
            $ λ f → implicit-fun-ext 
            $ λ x → het-proof-irrelevance η-rcoher₀ η-rcoher₁
        
