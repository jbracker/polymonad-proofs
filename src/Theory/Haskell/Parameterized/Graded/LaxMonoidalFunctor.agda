
open import Level
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality using ( _≅_ ; refl )

open import Extensionality
open import Congruence
open import Theory.Monoid
open import Theory.Category.Definition
open import Theory.Category.Monoidal
open import Theory.Category.Isomorphism
open import Theory.Functor.Definition
open import Theory.Functor.Composition
open import Theory.Natural.Isomorphism
open import Theory.Natural.Transformation

module Theory.Haskell.Parameterized.Graded.LaxMonoidalFunctor 
  {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} 
  {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}} where

-------------------------------------------------------------------------------
-- Definition of a lax/weak monoidal functor: 
-- https://ncatlab.org/nlab/show/monoidal+functor
-------------------------------------------------------------------------------
record GradedLaxMonoidalFunctor {ℓMon : Level} {M : Set ℓMon} (Mon : Monoid M) (CM : MonoidalCategory C) (DM : MonoidalCategory D) : Set (ℓC₀ ⊔ ℓC₁ ⊔ ℓD₀ ⊔ ℓD₁ ⊔ ℓMon) where
  constructor gradedLaxMonoidalFunctor
  
  open MonoidalCategory renaming ( id to cat-id )
  open Functor

  open Monoid Mon renaming ( ε to mon-ε )
  
  field
    F : (i : M) → Functor C D
  
  field
    ε : Hom DM (unit DM) (F₀ (F mon-ε) (unit CM))
  
  field
    μ-natural-transformation : (i j : M) → NaturalTransformation ([ tensor DM ]∘[ [ F i ]×[ F j ] ]) ([ F (i ∙ j) ]∘[ tensor CM ])
  
  private
    _⊗C₀_ = _⊗₀_ CM
    _⊗D₀_ = _⊗₀_ DM
    _⊗C₁_ = _⊗₁_ CM
    _⊗D₁_ = _⊗₁_ DM
    _∘D_ = _∘_ DM
  
  open NaturalTransformation renaming ( η to nat-η )
  
  μ : (i j : M) → (x y : Obj CM) → Hom DM (F₀ (F i) x ⊗D₀ F₀ (F j) y) (F₀ (F (i ∙ j)) (x ⊗C₀ y))
  μ i j x y = nat-η (μ-natural-transformation i j) (x , y)
  
  field
    assoc : {i j k : M} → (x y z : Obj CM) 
          → F₁ (F ((i ∙ j) ∙ k)) (α CM x y z) ∘D ((μ (i ∙ j) k (x ⊗C₀ y) z) ∘D (μ i j x y ⊗D₁ cat-id DM {F₀ (F k) z})) 
          ≅ (μ i (j ∙ k) x (y ⊗C₀ z)) ∘D ((cat-id DM {F₀ (F i) x} ⊗D₁ μ j k y z) ∘D (α DM (F₀ (F i) x) (F₀ (F j) y) (F₀ (F k) z)))
    
    left-unitality : {i : M} → (x : Obj CM)
                   → λ' DM (F₀ (F i) x)
                   ≅ F₁ (F (mon-ε ∙ i)) (λ' CM x) ∘D (μ mon-ε i (unit CM) x ∘D (ε ⊗D₁ cat-id DM {F₀ (F i) x}))
    
    right-unitality : {i : M} (x : Obj CM)
                    → ρ DM (F₀ (F i) x) 
                    ≅ F₁ (F (i ∙ mon-ε)) (ρ CM x) ∘D (μ i mon-ε x (unit CM) ∘D (cat-id DM {F₀ (F i) x} ⊗D₁ ε))

