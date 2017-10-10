
open import Level
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality using ( _≅_ ; refl )

open import Extensionality
open import Congruence
open import Theory.Category.Definition
open import Theory.Category.Monoidal
open import Theory.Category.Isomorphism
open import Theory.Functor.Definition
open import Theory.Functor.Composition
open import Theory.Natural.Isomorphism
open import Theory.Natural.Transformation

module Theory.Haskell.Parameterized.Indexed.Applicative 
  {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} 
  {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}} where

-------------------------------------------------------------------------------
-- Definition of a lax/weak monoidal functor: 
-- https://ncatlab.org/nlab/show/monoidal+functor
-------------------------------------------------------------------------------
record IndexedLaxMonoidalFunctor {ℓIxs : Level} (Ixs : Set ℓIxs) (CM : MonoidalCategory C) (DM : MonoidalCategory D) : Set (ℓC₀ ⊔ ℓC₁ ⊔ ℓD₀ ⊔ ℓD₁ ⊔ ℓIxs) where
  constructor indexdedLaxMonoidalFunctor
  
  open MonoidalCategory renaming ( id to cat-id )
  open Functor
  
  field
    F : (i j : Ixs) → Functor C D
  
  field
    ε : (i : Ixs) → Hom DM (unit DM) (F₀ (F i i) (unit CM))

  field
    μ-natural-transformation : (i j k : Ixs) → NaturalTransformation ([ tensor DM ]∘[ [ F i j ]×[ F j k ] ]) ([ F i k ]∘[ tensor CM ])
  
  private
    _⊗C₀_ = _⊗₀_ CM
    _⊗D₀_ = _⊗₀_ DM
    _⊗C₁_ = _⊗₁_ CM
    _⊗D₁_ = _⊗₁_ DM
    _∘D_ = _∘_ DM
  
  open NaturalTransformation renaming ( η to nat-η )
  
  μ : (i j k : Ixs) → (x y : Obj CM) → Hom DM (F₀ (F i j) x ⊗D₀ F₀ (F j k) y) (F₀ (F i k) (x ⊗C₀ y))
  μ i j k x y = nat-η (μ-natural-transformation i j k) (x , y)
  
  field
    assoc : {i j k l : Ixs} → (x y z : Obj CM) 
          → F₁ (F i l) (α CM x y z) ∘D ((μ i k l (x ⊗C₀ y) z) ∘D (μ i j k x y ⊗D₁ cat-id DM {F₀ (F k l) z})) 
          ≡ (μ i j l x (y ⊗C₀ z)) ∘D ((cat-id DM {F₀ (F i j) x} ⊗D₁ μ j k l y z) ∘D (α DM (F₀ (F i j) x) (F₀ (F j k) y) (F₀ (F k l) z)))
    
    left-unitality : {i j : Ixs} → (x : Obj CM)
                   → λ' DM (F₀ (F i j) x)
                   ≡ F₁ (F i j) (λ' CM x) ∘D (μ i i j (unit CM) x ∘D (ε i ⊗D₁ cat-id DM {F₀ (F i j) x}))
    
    right-unitality : {i j : Ixs} (x : Obj CM)
                    → ρ DM (F₀ (F i j) x) 
                    ≡ F₁ (F i j) (ρ CM x) ∘D (μ i j j x (unit CM) ∘D (cat-id DM {F₀ (F i j) x} ⊗D₁ ε j))
