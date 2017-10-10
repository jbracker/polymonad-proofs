
open import Level
open import Function hiding ( id ; _∘_ )

open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( proof-irrelevance to het-proof-irrelevance )

open import Congruence
open import Extensionality
open import Theory.Monoid
open import Theory.Category.Definition
open import Theory.Category.Monoidal
open import Theory.Functor.Definition
open import Theory.Functor.Composition
open import Theory.Natural.Transformation

open import Theory.Haskell.Parameterized.Graded.LaxMonoidalFunctor

module Theory.Haskell.Parameterized.Graded.LaxMonoidalFunctor.Equality 
  {ℓMon ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} 
  {M : Set ℓMon} {Mon : Monoid M}
  {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}}
  {CM : MonoidalCategory C} {DM : MonoidalCategory D} where 

open MonoidalCategory renaming ( id to cat-id )
open NaturalTransformation renaming ( η to nat-η )
open Monoid Mon renaming ( ε to mon-ε )

private
  _⊗C₀_ = _⊗₀_ CM
  _⊗D₀_ = _⊗₀_ DM
  _⊗C₁_ = _⊗₁_ CM
  _⊗D₁_ = _⊗₁_ DM
  _∘D_ = _∘_ DM

abstract
  indexed-lax-monoidal-functor-eq : {F₀ : (i : M) → Functor C D}
                                  → {F₁ : (i : M) → Functor C D}
                                  → {ε₀ : Hom DM (unit DM) (Functor.F₀ (F₀ mon-ε) (unit CM))}
                                  → {ε₁ : Hom DM (unit DM) (Functor.F₀ (F₁ mon-ε) (unit CM))}
                                  → {μ₀ : (i j : M) → NaturalTransformation ([ tensor DM ]∘[ [ F₀ i ]×[ F₀ j ] ]) ([ F₀ (i ∙ j) ]∘[ tensor CM ])}
                                  → {μ₁ : (i j : M) → NaturalTransformation ([ tensor DM ]∘[ [ F₁ i ]×[ F₁ j ] ]) ([ F₁ (i ∙ j) ]∘[ tensor CM ])}
                                  → {assoc₀ : {i j k : M} → (x y z : Obj CM) 
                                            → Functor.F₁ (F₀ ((i ∙ j) ∙ k)) (α CM x y z) ∘D ((nat-η (μ₀ (i ∙ j) k) ((x ⊗C₀ y) , z)) ∘D (nat-η (μ₀ i j) (x , y) ⊗D₁ cat-id DM {Functor.F₀ (F₀ k) z})) 
                                            ≅ (nat-η (μ₀ i (j ∙ k)) (x , y ⊗C₀ z)) ∘D ((cat-id DM {Functor.F₀ (F₀ i) x} ⊗D₁ nat-η (μ₀ j k) (y , z)) ∘D (α DM (Functor.F₀ (F₀ i) x) (Functor.F₀ (F₀ j) y) (Functor.F₀ (F₀ k) z)))}
                                  → {assoc₁ : {i j k : M} → (x y z : Obj CM) 
                                            → Functor.F₁ (F₁ ((i ∙ j) ∙ k)) (α CM x y z) ∘D ((nat-η (μ₁ (i ∙ j) k) ((x ⊗C₀ y) , z)) ∘D (nat-η (μ₁ i j) (x , y) ⊗D₁ cat-id DM {Functor.F₀ (F₁ k) z})) 
                                            ≅ (nat-η (μ₁ i (j ∙ k)) (x , y ⊗C₀ z)) ∘D ((cat-id DM {Functor.F₀ (F₁ i) x} ⊗D₁ nat-η (μ₁ j k) (y , z)) ∘D (α DM (Functor.F₀ (F₁ i) x) (Functor.F₀ (F₁ j) y) (Functor.F₀ (F₁ k) z)))}
                                  → {left-u₀ : {i : M} → (x : Obj CM)
                                             → λ' DM (Functor.F₀ (F₀ i) x)
                                             ≅ Functor.F₁ (F₀ (mon-ε ∙ i)) (λ' CM x) ∘D (nat-η (μ₀ mon-ε i) (unit CM , x) ∘D (ε₀ ⊗D₁ cat-id DM {Functor.F₀ (F₀ i) x}))}
                                  → {left-u₁ : {i : M} → (x : Obj CM)
                                             → λ' DM (Functor.F₀ (F₁ i) x)
                                             ≅ Functor.F₁ (F₁ (mon-ε ∙ i)) (λ' CM x) ∘D (nat-η (μ₁ mon-ε i) (unit CM , x) ∘D (ε₁ ⊗D₁ cat-id DM {Functor.F₀ (F₁ i) x}))}
                                  → {right-u₀ : {i : M} (x : Obj CM)
                                              → ρ DM (Functor.F₀ (F₀ i) x) 
                                              ≅ Functor.F₁ (F₀ (i ∙ mon-ε)) (ρ CM x) ∘D (nat-η (μ₀ i mon-ε) (x , unit CM) ∘D (cat-id DM {Functor.F₀ (F₀ i) x} ⊗D₁ ε₀))}
                                  → {right-u₁ : {i : M} (x : Obj CM)
                                              → ρ DM (Functor.F₀ (F₁ i) x) 
                                              ≅ Functor.F₁ (F₁ (i ∙ mon-ε)) (ρ CM x) ∘D (nat-η (μ₁ i mon-ε) (x , unit CM) ∘D (cat-id DM {Functor.F₀ (F₁ i) x} ⊗D₁ ε₁))}
                                  → (F₀ ≡ F₁)
                                  → (ε₀ ≅ ε₁)
                                  → (μ₀ ≅ μ₁)
                                  → gradedLaxMonoidalFunctor {Mon = Mon} {CM} {DM} F₀ ε₀ μ₀ assoc₀ left-u₀ right-u₀
                                  ≡ gradedLaxMonoidalFunctor {Mon = Mon} {CM} {DM} F₁ ε₁ μ₁ assoc₁ left-u₁ right-u₁
  indexed-lax-monoidal-functor-eq {F} {.F} {ε} {.ε} {μ} {.μ} {assoc₀} {assoc₁} {lu₀} {lu₁} {ru₀} {ru₁} refl refl refl
    = cong₃ (gradedLaxMonoidalFunctor {Mon = Mon} {CM} {DM} F ε μ) eq1 eq2 eq3
    where
      abstract
        eq1 : (λ {i j k} → assoc₀ {i} {j} {k}) ≡ assoc₁
        eq1 = implicit-fun-ext 
            $ λ i → implicit-fun-ext 
            $ λ j → implicit-fun-ext 
            $ λ k → fun-ext 
            $ λ x → fun-ext 
            $ λ y → fun-ext 
            $ λ z → het-proof-irrelevance (assoc₀ x y z) (assoc₁ x y z)
      
      abstract
        eq2 : (λ {i} → lu₀ {i}) ≡ lu₁
        eq2 = implicit-fun-ext 
            $ λ i → fun-ext 
            $ λ x → het-proof-irrelevance (lu₀ x) (lu₁ x)
      
      abstract
        eq3 : (λ {i} → ru₀ {i}) ≡ ru₁
        eq3 = implicit-fun-ext 
            $ λ i → fun-ext 
            $ λ x → het-proof-irrelevance (ru₀ x) (ru₁ x)
