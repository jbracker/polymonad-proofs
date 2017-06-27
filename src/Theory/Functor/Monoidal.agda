
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

module Theory.Functor.Monoidal {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} 
                               {C' : Category {ℓC₀} {ℓC₁}} {D' : Category {ℓD₀} {ℓD₁}} where

-------------------------------------------------------------------------------
-- Definition of a lax/weak monoidal functor: 
-- https://ncatlab.org/nlab/show/monoidal+functor
-------------------------------------------------------------------------------
record LaxMonoidalFunctor (C : MonoidalCategory C') (D : MonoidalCategory D') : Set (ℓC₀ ⊔ ℓC₁ ⊔ ℓD₀ ⊔ ℓD₁) where
  constructor laxMonoidalFunctor
    
  field
    F : Functor C' D'
    
  open Functor F public
  open MonoidalCategory renaming ( assoc to cat-assoc ; id to cat-id )
  
  field
    ε : Hom D (unit D) (F₀ (unit C))
  --  iso-ε : Isomorphism D' ε
  
  -- open Isomorphism iso-ε renaming ( inv to ε⁻¹ ; left-id to ε-left-id ; right-id to ε-right-id ) hiding ( f⁻¹ ) public 
  
  private
    _⊗C₀_ = _⊗₀_ C
    _⊗D₀_ = _⊗₀_ D
    _⊗C₁_ = _⊗₁_ C
    _⊗D₁_ = _⊗₁_ D
    _∘D_ = _∘_ D
  
  field
    μ-natural-transformation : NaturalTransformation ([ tensor D ]∘[ [ F ]×[ F ] ]) ([ F ]∘[ tensor C ])
  
  open NaturalTransformation μ-natural-transformation
  
  μ : (x y : Obj C) → Hom D (F₀ x ⊗D₀ F₀ y) (F₀ (x ⊗C₀ y))
  μ x y = η (x , y)
  
  field
    assoc : (x y z : Obj C) 
          → F₁ (α C x y z) ∘D ((μ (x ⊗C₀ y) z) ∘D (μ x y ⊗D₁ cat-id D {F₀ z})) 
          ≡ (μ x (y ⊗C₀ z)) ∘D ((cat-id D {F₀ x} ⊗D₁ μ y z) ∘D (α D (F₀ x) (F₀ y) (F₀ z)))
    
    left-unitality : (x : Obj C)
                   → λ' D (F₀ x)
                   ≡ F₁ (λ' C x) ∘D (μ (unit C) x ∘D (ε ⊗D₁ cat-id D {F₀ x}))
    
    right-unitality : (x : Obj C)
                    → ρ D (F₀ x) 
                    ≡ F₁ (ρ C x) ∘D (μ x (unit C) ∘D (cat-id D {F₀ x} ⊗D₁ ε))

WeakMonoidalFunctor = LaxMonoidalFunctor

-------------------------------------------------------------------------------
-- Definition of a (strong) monoidal functor: 
-- https://ncatlab.org/nlab/show/monoidal+functor
-------------------------------------------------------------------------------
record MonoidalFunctor (C : MonoidalCategory C') (D : MonoidalCategory D') : Set (ℓC₀ ⊔ ℓC₁ ⊔ ℓD₀ ⊔ ℓD₁) where
  constructor monoidalFunctor
    
  field
    lax-monoidal-functor : LaxMonoidalFunctor C D
    
  open LaxMonoidalFunctor lax-monoidal-functor public
  open MonoidalCategory renaming ( assoc to cat-assoc ; id to cat-id )
  
  field
    iso-ε : Isomorphism D' ε
  
  open Isomorphism iso-ε renaming ( inv to ε⁻¹ ; left-id to ε-left-id ; right-id to ε-right-id ) hiding ( f⁻¹ ) public 
  
  field
    μ-natural-isomorphism : NaturalIsomorphism ([ tensor D ]∘[ [ F ]×[ F ] ]) ([ F ]∘[ tensor C ])
  
  open NaturalIsomorphism μ-natural-isomorphism hiding ( natural-transformation ) public

  field
    natural-transformation-coherence : NaturalIsomorphism.natural-transformation μ-natural-isomorphism ≡ μ-natural-transformation

StrongMonoidalFunctor = MonoidalFunctor

-------------------------------------------------------------------------------
-- Equality of monoidal functors
-------------------------------------------------------------------------------
private
  module Equality {C : MonoidalCategory C'} {D : MonoidalCategory D'} where 
    open MonoidalCategory renaming ( id to cat-id )
    open NaturalTransformation
    open Functor
    
    abstract
      lax-monoidal-functor-eq : {F G : Functor C' D'}
                              → {ε₀ : Hom D (unit D) (F₀ F (unit C))}
                              → {ε₁ : Hom D (unit D) (F₀ G (unit C))}
                              → {μ-NatTrans₀ : NaturalTransformation ([ tensor D ]∘[ [ F ]×[ F ] ]) ([ F ]∘[ tensor C ])}
                              → {μ-NatTrans₁ : NaturalTransformation ([ tensor D ]∘[ [ G ]×[ G ] ]) ([ G ]∘[ tensor C ])}
                              → {assoc₀ : (x y z : Obj C) → _∘_ D (F₁ F (α C x y z)) (_∘_ D (η μ-NatTrans₀ (_⊗₀_ C x y , z)) (_⊗₁_ D (η μ-NatTrans₀ (x , y)) (cat-id D {F₀ F z}))) 
                                                       ≡ _∘_ D (η μ-NatTrans₀ (x , _⊗₀_ C y z)) (_∘_ D (_⊗₁_ D (cat-id D {F₀ F x}) (η μ-NatTrans₀ (y , z))) (α D (F₀ F x) (F₀ F y) (F₀ F z)))}
                              → {assoc₁ : (x y z : Obj C) → _∘_ D (F₁ G (α C x y z)) (_∘_ D (η μ-NatTrans₁ (_⊗₀_ C x y , z)) (_⊗₁_ D (η μ-NatTrans₁ (x , y)) (cat-id D {F₀ G z}))) 
                                                       ≡ _∘_ D (η μ-NatTrans₁ (x , _⊗₀_ C y z)) (_∘_ D (_⊗₁_ D (cat-id D {F₀ G x}) (η μ-NatTrans₁ (y , z))) (α D (F₀ G x) (F₀ G y) (F₀ G z)))}
                              → {left-unitality₀ : (x : Obj C) → λ' D (F₀ F x) ≡ _∘_ D (F₁ F (λ' C x)) (_∘_ D (η μ-NatTrans₀ (unit C , x)) (_⊗₁_ D ε₀ (cat-id D {F₀ F x})))}
                              → {left-unitality₁ : (x : Obj C) → λ' D (F₀ G x) ≡ _∘_ D (F₁ G (λ' C x)) (_∘_ D (η μ-NatTrans₁ (unit C , x)) (_⊗₁_ D ε₁ (cat-id D {F₀ G x})))}
                              → {right-unitality₀ : (x : Obj C) → ρ D (F₀ F x) ≡ _∘_ D (F₁ F (ρ C x)) (_∘_ D (η μ-NatTrans₀ (x , unit C)) (_⊗₁_ D (cat-id D {F₀ F x}) ε₀ ))}
                              → {right-unitality₁ : (x : Obj C) → ρ D (F₀ G x) ≡ _∘_ D (F₁ G (ρ C x)) (_∘_ D (η μ-NatTrans₁ (x , unit C)) (_⊗₁_ D (cat-id D {F₀ G x}) ε₁))}
                              → F ≡ G → ε₀ ≅ ε₁ → μ-NatTrans₀ ≅ μ-NatTrans₁
                              → laxMonoidalFunctor {C = C} {D} F ε₀ μ-NatTrans₀ assoc₀ left-unitality₀ right-unitality₀
                              ≡ laxMonoidalFunctor {C = C} {D} G ε₁ μ-NatTrans₁ assoc₁ left-unitality₁ right-unitality₁
      lax-monoidal-functor-eq {F = F} {.F} {ε} {.ε} {μ-NatIso} {.μ-NatIso} {assoc₀} {assoc₁} {left-u₀} {left-u₁} {right-u₀} {right-u₁} refl refl refl 
        = cong₃ (laxMonoidalFunctor F ε μ-NatIso) 
                (fun-ext (λ x → fun-ext (λ y → fun-ext (λ z → proof-irrelevance (assoc₀ x y z) (assoc₁ x y z))))) 
                (fun-ext (λ x → proof-irrelevance (left-u₀  x) (left-u₁  x))) 
                (fun-ext (λ x → proof-irrelevance (right-u₀ x) (right-u₁ x)))
    
    weak-monoidal-functor-eq = lax-monoidal-functor-eq
    
    open LaxMonoidalFunctor
    open NaturalIsomorphism
    
    abstract
      monoidal-functor-eq : {LMF₀ : LaxMonoidalFunctor C D}
                          → {LMF₁ : LaxMonoidalFunctor C D}
                          → {iso-ε₀ : Isomorphism D' (ε LMF₀)}
                          → {iso-ε₁ : Isomorphism D' (ε LMF₁)}
                          → {μ-NatIso₀ : NaturalIsomorphism ([ tensor D ]∘[ [ F LMF₀ ]×[ F LMF₀ ] ]) ([ F LMF₀ ]∘[ tensor C ])}
                          → {μ-NatIso₁ : NaturalIsomorphism ([ tensor D ]∘[ [ F LMF₁ ]×[ F LMF₁ ] ]) ([ F LMF₁ ]∘[ tensor C ])}
                          → {nat-trans-coher₀ : natural-transformation μ-NatIso₀ ≡ μ-natural-transformation LMF₀}
                          → {nat-trans-coher₁ : natural-transformation μ-NatIso₁ ≡ μ-natural-transformation LMF₁}
                          → LMF₀ ≡ LMF₁ → iso-ε₀ ≅ iso-ε₁ → μ-NatIso₀ ≅ μ-NatIso₁
                          → monoidalFunctor LMF₀ iso-ε₀ μ-NatIso₀ nat-trans-coher₀
                          ≡ monoidalFunctor LMF₁ iso-ε₁ μ-NatIso₁ nat-trans-coher₁
      monoidal-functor-eq {LMF} {.LMF} {iso-ε} {.iso-ε} {μ-NatIso} {.μ-NatIso} {nat-trans-coher₀} {nat-trans-coher₁} refl refl refl 
        = cong (monoidalFunctor LMF iso-ε μ-NatIso) (proof-irrelevance nat-trans-coher₀ nat-trans-coher₁)
    
    strong-monoidal-functor-eq = monoidal-functor-eq
    
open Equality public
