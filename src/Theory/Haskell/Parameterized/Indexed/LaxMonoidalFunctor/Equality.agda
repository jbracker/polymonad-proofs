
open import Level
open import Function hiding ( id ; _∘_ )

open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( refl to hrefl ; proof-irrelevance to het-proof-irrelevance )

open import Congruence
open import Extensionality
open import Theory.Category.Definition
open import Theory.Category.Monoidal
open import Theory.Functor.Definition
open import Theory.Functor.Composition
open import Theory.Natural.Transformation

open import Theory.Haskell.Parameterized.Indexed.LaxMonoidalFunctor

module Theory.Haskell.Parameterized.Indexed.LaxMonoidalFunctor.Equality 
  {ℓC₀ ℓC₁ ℓD₀ ℓD₁ ℓI₀ ℓI₁ : Level}
  {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}} {I : Category {ℓI₀} {ℓI₁}}
  {CM : MonoidalCategory C} {DM : MonoidalCategory D} where 

open Category renaming ( id to cat-id )
open MonoidalCategory hiding ( Obj ; Hom ; id )
open NaturalTransformation renaming ( η to nat-η )

private
  _⊗C₀_ = _⊗₀_ CM
  _⊗D₀_ = _⊗₀_ DM
  _⊗C₁_ = _⊗₁_ CM
  _⊗D₁_ = _⊗₁_ DM
  _∘D_ = Category._∘_ D
  _∘I_ = Category._∘_ I

abstract
  indexed-lax-monoidal-functor-eq : {F₀ : {i j : Obj I} → Hom I i j → Functor C D}
                                  → {F₁ : {i j : Obj I} → Hom I i j → Functor C D}
                                  → {ε₀ : (i : Obj I) → Hom D (unit DM) (Functor.F₀ (F₀ (cat-id I {i})) (unit CM))}
                                  → {ε₁ : (i : Obj I) → Hom D (unit DM) (Functor.F₀ (F₁ (cat-id I {i})) (unit CM))}
                                  → {μ₀ : {i j k : Obj I} → (f : Hom I i j) (g : Hom I j k) 
                                        → NaturalTransformation ([ tensor DM ]∘[ [ F₀ f ]×[ F₀ g ] ]) ([ F₀ (g ∘I f) ]∘[ tensor CM ])}
                                  → {μ₁ : {i j k : Obj I} → (f : Hom I i j) (g : Hom I j k) 
                                        → NaturalTransformation ([ tensor DM ]∘[ [ F₁ f ]×[ F₁ g ] ]) ([ F₁ (g ∘I f) ]∘[ tensor CM ])}
                                  → {assoc₀ : {i j k l : Obj I} → {f : Hom I i j} {g : Hom I j k} {h : Hom I k l} → (x y z : Obj C) 
                                            → Functor.F₁ (F₀ (h ∘I (g ∘I f))) (α CM x y z) ∘D ((nat-η (μ₀ (g ∘I f) h) ((x ⊗C₀ y) , z)) ∘D (nat-η (μ₀ f g) (x , y) ⊗D₁ cat-id D {Functor.F₀ (F₀ h) z})) 
                                            ≅ nat-η (μ₀ f (h ∘I g)) (x , y ⊗C₀ z) ∘D ((cat-id D {Functor.F₀ (F₀ f) x} ⊗D₁ nat-η (μ₀ g h) (y , z)) ∘D (α DM (Functor.F₀ (F₀ f) x) (Functor.F₀ (F₀ g) y) (Functor.F₀ (F₀ h) z)))}
                                  → {assoc₁ : {i j k l : Obj I} → {f : Hom I i j} {g : Hom I j k} {h : Hom I k l} → (x y z : Obj C) 
                                            → Functor.F₁ (F₁ (h ∘I (g ∘I f))) (α CM x y z) ∘D ((nat-η (μ₁ (g ∘I f) h) ((x ⊗C₀ y) , z)) ∘D (nat-η (μ₁ f g) (x , y) ⊗D₁ cat-id D {Functor.F₀ (F₁ h) z})) 
                                            ≅ nat-η (μ₁ f (h ∘I g)) (x , y ⊗C₀ z) ∘D ((cat-id D {Functor.F₀ (F₁ f) x} ⊗D₁ nat-η (μ₁ g h) (y , z)) ∘D (α DM (Functor.F₀ (F₁ f) x) (Functor.F₀ (F₁ g) y) (Functor.F₀ (F₁ h) z)))}
                                  → {left-u₀ : {i j : Obj I} {f : Hom I i j} → (x : Obj C)
                                             → λ' DM (Functor.F₀ (F₀ f) x)
                                             ≅ Functor.F₁ (F₀ (f ∘I cat-id I {i})) (λ' CM x) ∘D (nat-η (μ₀ (cat-id I {i}) f) (unit CM , x) ∘D (ε₀ i ⊗D₁ cat-id D {Functor.F₀ (F₀ f) x}))}
                                  → {left-u₁ : {i j : Obj I} {f : Hom I i j} → (x : Obj C)
                                             → λ' DM (Functor.F₀ (F₁ f) x)
                                             ≅ Functor.F₁ (F₁ (f ∘I cat-id I {i})) (λ' CM x) ∘D (nat-η (μ₁ (cat-id I {i}) f) (unit CM , x) ∘D (ε₁ i ⊗D₁ cat-id D {Functor.F₀ (F₁ f) x}))}
                                  → {right-u₀ : {i j : Obj I} {f : Hom I i j} (x : Obj C)
                                              → ρ DM (Functor.F₀ (F₀ f) x) 
                                              ≅ Functor.F₁ (F₀ (cat-id I {j} ∘I f)) (ρ CM x) ∘D (nat-η (μ₀ f (cat-id I {j})) (x , unit CM) ∘D (cat-id D {Functor.F₀ (F₀ f) x} ⊗D₁ ε₀ j))}
                                  → {right-u₁ : {i j : Obj I} {f : Hom I i j} (x : Obj C)
                                              → ρ DM (Functor.F₀ (F₁ f) x) 
                                              ≅ Functor.F₁ (F₁ (cat-id I {j} ∘I f)) (ρ CM x) ∘D (nat-η (μ₁ f (cat-id I {j})) (x , unit CM) ∘D (cat-id D {Functor.F₀ (F₁ f) x} ⊗D₁ ε₁ j))}
                                  → ((λ {i j} → F₀ {i} {j}) ≡ F₁)
                                  → (ε₀ ≅ ε₁)
                                  → ((λ {i j k} → μ₀ {i} {j} {k}) ≅ (λ {i j k} → μ₁ {i} {j} {k}))
                                  → indexedLaxMonoidalFunctor {I = I} {CM} {DM} F₀ ε₀ μ₀ assoc₀ left-u₀ right-u₀
                                  ≡ indexedLaxMonoidalFunctor {I = I} {CM} {DM} F₁ ε₁ μ₁ assoc₁ left-u₁ right-u₁
  indexed-lax-monoidal-functor-eq {F} {.F} {ε} {.ε} {μ} {.μ} {assoc₀} {assoc₁} {lu₀} {lu₁} {ru₀} {ru₁} refl hrefl hrefl
    = cong₃ (indexedLaxMonoidalFunctor {I = I} {CM} {DM} F ε μ) eq1 eq2 eq3
    where
      abstract
        eq1 : (λ {i j k l} {f} {g} {h} → assoc₀ {i} {j} {k} {l} {f} {g} {h}) ≡ assoc₁
        eq1 = implicit-fun-ext 
            $ λ i → implicit-fun-ext 
            $ λ j → implicit-fun-ext 
            $ λ k → implicit-fun-ext 
            $ λ l → implicit-fun-ext 
            $ λ f → implicit-fun-ext 
            $ λ g → implicit-fun-ext 
            $ λ h → fun-ext 
            $ λ x → fun-ext 
            $ λ y → fun-ext 
            $ λ z → het-proof-irrelevance (assoc₀ x y z) (assoc₁ x y z)
      
      abstract
        eq2 : (λ {i j} {f} → lu₀ {i} {j} {f}) ≡ lu₁
        eq2 = implicit-fun-ext 
            $ λ i → implicit-fun-ext 
            $ λ j → implicit-fun-ext 
            $ λ f → fun-ext 
            $ λ x → het-proof-irrelevance (lu₀ x) (lu₁ x)
      
      abstract
        eq3 : (λ {i j} {f} → ru₀ {i} {j} {f}) ≡ ru₁
        eq3 = implicit-fun-ext 
            $ λ i → implicit-fun-ext 
            $ λ j → implicit-fun-ext 
            $ λ f → fun-ext 
            $ λ x → het-proof-irrelevance (ru₀ x) (ru₁ x)
