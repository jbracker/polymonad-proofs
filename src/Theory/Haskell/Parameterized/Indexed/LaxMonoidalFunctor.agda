
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

module Theory.Haskell.Parameterized.Indexed.LaxMonoidalFunctor 
  {ℓC₀ ℓC₁ ℓD₀ ℓD₁ ℓI₀ ℓI₁ : Level} 
  {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}}  where

-------------------------------------------------------------------------------
-- Definition of a lax/weak monoidal functor adjusted to support indices
-- as in indexed applicatives do.
-------------------------------------------------------------------------------
record IndexedLaxMonoidalFunctor (I : Category {ℓI₀} {ℓI₁}) (CM : MonoidalCategory C) (DM : MonoidalCategory D) : Set (ℓC₀ ⊔ ℓC₁ ⊔ ℓD₀ ⊔ ℓD₁ ⊔ ℓI₀ ⊔ ℓI₁) where
  constructor indexedLaxMonoidalFunctor
  
  open Category renaming ( id to cat-id )
  open MonoidalCategory hiding ( Obj ; Hom ; id )
  open Functor

  private
    _∘I_ = Category._∘_ I
  
  field
    F : {i j : Obj I} → Hom I i j → Functor C D
  
  field
    ε : (i : Obj I) → Hom D (unit DM) (F₀ (F (cat-id I {i})) (unit CM))

  field
    μ-natural-transformation : {i j k : Obj I} → (f : Hom I i j) → (g : Hom I j k) 
                             → NaturalTransformation ([ tensor DM ]∘[ [ F f ]×[ F g ] ]) ([ F (g ∘I f) ]∘[ tensor CM ])
  
  private
    _⊗C₀_ = _⊗₀_ CM
    _⊗D₀_ = _⊗₀_ DM
    _⊗C₁_ = _⊗₁_ CM
    _⊗D₁_ = _⊗₁_ DM
    _∘D_ = Category._∘_ D
  
  open NaturalTransformation renaming ( η to nat-η )
  
  μ : {i j k : Obj I} → (f : Hom I i j) → (g : Hom I j k) → (x y : Obj C) 
    → Hom D (F₀ (F f) x ⊗D₀ F₀ (F g) y) (F₀ (F (g ∘I f)) (x ⊗C₀ y))
  μ f g x y = nat-η (μ-natural-transformation f g) (x , y)
  
  field
    assoc : {i j k l : Obj I}
          → {f : Hom I i j} {g : Hom I j k} {h : Hom I k l} 
          → (a b c : Obj C) 
          → F₁ (F (h ∘I (g ∘I f))) (α CM a b c) ∘D ((μ (g ∘I f) h (a ⊗C₀ b) c) ∘D (μ f g a b ⊗D₁ cat-id D {F₀ (F h) c})) 
          ≅ (μ f (h ∘I g) a (b ⊗C₀ c)) ∘D ((cat-id D {F₀ (F f) a} ⊗D₁ μ g h b c) ∘D (α DM (F₀ (F f) a) (F₀ (F g) b) (F₀ (F h) c)))
    
    left-unitality : {i j : Obj I} {f : Hom I i j} → (x : Obj C)
                   → λ' DM (F₀ (F f) x)
                   ≅ F₁ (F (f ∘I cat-id I {i})) (λ' CM x) ∘D (μ (cat-id I {i}) f (unit CM) x ∘D (ε i ⊗D₁ cat-id D {F₀ (F f) x}))
    
    right-unitality : {i j : Obj I} {f : Hom I i j} → (x : Obj C)
                    → ρ DM (F₀ (F f) x) 
                    ≅ F₁ (F (cat-id I {j} ∘I f)) (ρ CM x) ∘D (μ f (cat-id I {j}) x (unit CM) ∘D (cat-id D {F₀ (F f) x} ⊗D₁ ε j))

