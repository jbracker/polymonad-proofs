
open import Level
open import Function hiding ( id ; _∘_ )

open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( proof-irrelevance to het-proof-irrelevance )

open import Congruence
open import Extensionality
open import Theory.Category.Definition
open import Theory.Category.Monoidal
open import Theory.Functor.Definition
open import Theory.Functor.Composition
open import Theory.Natural.Transformation

open import Theory.Haskell.Parameterized.Indexed.Applicative

module Theory.Haskell.Parameterized.Indexed.Applicative.Equality 
  {ℓIxs ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} 
  {Ixs : Set ℓIxs} 
  {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}}
  {CM : MonoidalCategory C} {DM : MonoidalCategory D} where 

open MonoidalCategory renaming ( id to cat-id )
open NaturalTransformation renaming ( η to nat-η )

private
  _⊗C₀_ = _⊗₀_ CM
  _⊗D₀_ = _⊗₀_ DM
  _⊗C₁_ = _⊗₁_ CM
  _⊗D₁_ = _⊗₁_ DM
  _∘D_ = _∘_ DM

abstract
  indexed-lax-monoidal-functor-eq : {F₀ : (i j : Ixs) → Functor C D}
                                  → {F₁ : (i j : Ixs) → Functor C D}
                                  → {ε₀ : (i : Ixs) → Hom DM (unit DM) (Functor.F₀ (F₀ i i) (unit CM))}
                                  → {ε₁ : (i : Ixs) → Hom DM (unit DM) (Functor.F₀ (F₁ i i) (unit CM))}
                                  → {μ₀ : (i j k : Ixs) → NaturalTransformation ([ tensor DM ]∘[ [ F₀ i j ]×[ F₀ j k ] ]) ([ F₀ i k ]∘[ tensor CM ])}
                                  → {μ₁ : (i j k : Ixs) → NaturalTransformation ([ tensor DM ]∘[ [ F₁ i j ]×[ F₁ j k ] ]) ([ F₁ i k ]∘[ tensor CM ])}
                                  → {assoc₀ : {i j k l : Ixs} → (x y z : Obj CM) 
                                            → Functor.F₁ (F₀ i l) (α CM x y z) ∘D ((nat-η (μ₀ i k l) ((x ⊗C₀ y) , z)) ∘D (nat-η (μ₀ i j k) (x , y) ⊗D₁ cat-id DM {Functor.F₀ (F₀ k l) z})) 
                                            ≡ (nat-η (μ₀ i j l) (x , y ⊗C₀ z)) ∘D ((cat-id DM {Functor.F₀ (F₀ i j) x} ⊗D₁ nat-η (μ₀ j k l) (y , z)) ∘D (α DM (Functor.F₀ (F₀ i j) x) (Functor.F₀ (F₀ j k) y) (Functor.F₀ (F₀ k l) z)))}
                                  → {assoc₁ : {i j k l : Ixs} → (x y z : Obj CM) 
                                            → Functor.F₁ (F₁ i l) (α CM x y z) ∘D ((nat-η (μ₁ i k l) ((x ⊗C₀ y) , z)) ∘D (nat-η (μ₁ i j k) (x , y) ⊗D₁ cat-id DM {Functor.F₀ (F₁ k l) z})) 
                                            ≡ (nat-η (μ₁ i j l) (x , y ⊗C₀ z)) ∘D ((cat-id DM {Functor.F₀ (F₁ i j) x} ⊗D₁ nat-η (μ₁ j k l) (y , z)) ∘D (α DM (Functor.F₀ (F₁ i j) x) (Functor.F₀ (F₁ j k) y) (Functor.F₀ (F₁ k l) z)))}
                                  → {left-u₀ : {i j : Ixs} → (x : Obj CM)
                                             → λ' DM (Functor.F₀ (F₀ i j) x)
                                             ≡ Functor.F₁ (F₀ i j) (λ' CM x) ∘D (nat-η (μ₀ i i j) (unit CM , x) ∘D (ε₀ i ⊗D₁ cat-id DM {Functor.F₀ (F₀ i j) x}))}
                                  → {left-u₁ : {i j : Ixs} → (x : Obj CM)
                                             → λ' DM (Functor.F₀ (F₁ i j) x)
                                             ≡ Functor.F₁ (F₁ i j) (λ' CM x) ∘D (nat-η (μ₁ i i j) (unit CM , x) ∘D (ε₁ i ⊗D₁ cat-id DM {Functor.F₀ (F₁ i j) x}))}
                                  → {right-u₀ : {i j : Ixs} (x : Obj CM)
                                              → ρ DM (Functor.F₀ (F₀ i j) x) 
                                              ≡ Functor.F₁ (F₀ i j) (ρ CM x) ∘D (nat-η (μ₀ i j j) (x , unit CM) ∘D (cat-id DM {Functor.F₀ (F₀ i j) x} ⊗D₁ ε₀ j))}
                                  → {right-u₁ : {i j : Ixs} (x : Obj CM)
                                              → ρ DM (Functor.F₀ (F₁ i j) x) 
                                              ≡ Functor.F₁ (F₁ i j) (ρ CM x) ∘D (nat-η (μ₁ i j j) (x , unit CM) ∘D (cat-id DM {Functor.F₀ (F₁ i j) x} ⊗D₁ ε₁ j))}
                                  → (F₀ ≡ F₁)
                                  → (ε₀ ≅ ε₁)
                                  → (μ₀ ≅ μ₁)
                                  → indexdedLaxMonoidalFunctor {Ixs = Ixs} {CM} {DM} F₀ ε₀ μ₀ assoc₀ left-u₀ right-u₀
                                  ≡ indexdedLaxMonoidalFunctor {Ixs = Ixs} {CM} {DM} F₁ ε₁ μ₁ assoc₁ left-u₁ right-u₁
  indexed-lax-monoidal-functor-eq {F} {.F} {ε} {.ε} {μ} {.μ} {assoc₀} {assoc₁} {lu₀} {lu₁} {ru₀} {ru₁} refl refl refl
    = cong₃ (indexdedLaxMonoidalFunctor {Ixs = Ixs} {CM} {DM} F ε μ) eq1 eq2 eq3
    where
      abstract
        eq1 : (λ {i j k l} → assoc₀ {i} {j} {k} {l}) ≡ assoc₁
        eq1 = implicit-fun-ext 
            $ λ i → implicit-fun-ext 
            $ λ j → implicit-fun-ext 
            $ λ k → implicit-fun-ext 
            $ λ l → fun-ext 
            $ λ x → fun-ext 
            $ λ y → fun-ext 
            $ λ z → proof-irrelevance (assoc₀ x y z) (assoc₁ x y z)
      
      abstract
        eq2 : (λ {i j} → lu₀ {i} {j}) ≡ lu₁
        eq2 = implicit-fun-ext 
            $ λ i → implicit-fun-ext 
            $ λ j → fun-ext 
            $ λ x → proof-irrelevance (lu₀ x) (lu₁ x)
      
      abstract
        eq3 : (λ {i j} → ru₀ {i} {j}) ≡ ru₁
        eq3 = implicit-fun-ext 
            $ λ i → implicit-fun-ext 
            $ λ j → fun-ext 
            $ λ x → proof-irrelevance (ru₀ x) (ru₁ x)
