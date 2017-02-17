
open import Level
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality using ( _≅_ ; refl )

open import Extensionality
open import Congruence
open import Theory.Category
open import Theory.Isomorphism
open import Theory.MonoidalCategory
open import Theory.Functor
open import Theory.NaturalIsomorphism

module Theory.MonoidalFunctor where

-------------------------------------------------------------------------------
-- Definition of a monoidal functor: 
-- https://ncatlab.org/nlab/show/monoidal+functor
-------------------------------------------------------------------------------
record MonoidalFunctor {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} 
                       {C' : Category {ℓC₀} {ℓC₁}} {D' : Category {ℓD₀} {ℓD₁}} 
                       (C : MonoidalCategory C') (D : MonoidalCategory D') : Set (ℓC₀ ⊔ ℓC₁ ⊔ ℓD₀ ⊔ ℓD₁) where
  constructor monoidalFunctor
    
  field
    F : Functor C' D'
    
  open Functor F public
  open MonoidalCategory renaming ( assoc to cat-assoc ; id to cat-id )
  
  field
    ε : Hom D (unit D) (F₀ (unit C))
    iso-ε : Isomorphism D' ε
  
  open Isomorphism iso-ε renaming ( inv to ε⁻¹ ; left-id to ε-left-id ; right-id to ε-right-id ) hiding ( f⁻¹ ) public 
  
  private
    _⊗C₀_ = _⊗₀_ C
    _⊗D₀_ = _⊗₀_ D
    _⊗C₁_ = _⊗₁_ C
    _⊗D₁_ = _⊗₁_ D
    _∘D_ = _∘_ D
  
  field
    μ-NatIso : NaturalIsomorphism ([ tensor D ]∘[ [ F ]×[ F ] ]) ([ F ]∘[ tensor C ])
  
  open NaturalIsomorphism μ-NatIso
  
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

open MonoidalCategory renaming ( id to cat-id )
open NaturalIsomorphism
open Functor

-------------------------------------------------------------------------------
-- Equality of monoidal functors
-------------------------------------------------------------------------------
monoidal-functor-eq : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} 
                    → {C' : Category {ℓC₀} {ℓC₁}} {D' : Category {ℓD₀} {ℓD₁}} 
                    → {C : MonoidalCategory C'} {D : MonoidalCategory D'}
                    → {F G : Functor C' D'}
                    → {ε  : Hom D (unit D) (F₀ F (unit C))}
                    → {ε' : Hom D (unit D) (F₀ G (unit C))}
                    → {iso-ε  : Isomorphism D' ε}
                    → {iso-ε' : Isomorphism D' ε'}
                    → {μ-NatIso  : NaturalIsomorphism ([ tensor D ]∘[ [ F ]×[ F ] ]) ([ F ]∘[ tensor C ])}
                    → {μ-NatIso' : NaturalIsomorphism ([ tensor D ]∘[ [ G ]×[ G ] ]) ([ G ]∘[ tensor C ])}
                    → {assoc  : (x y z : Obj C) → _∘_ D (F₁ F (α C x y z)) (_∘_ D (η μ-NatIso  (_⊗₀_ C x y , z)) (_⊗₁_ D (η μ-NatIso  (x , y)) (cat-id D {F₀ F z}))) 
                                                ≡ _∘_ D (η μ-NatIso  (x , _⊗₀_ C y z)) (_∘_ D (_⊗₁_ D (cat-id D {F₀ F x}) (η μ-NatIso  (y , z))) (α D (F₀ F x) (F₀ F y) (F₀ F z)))}
                    → {assoc' : (x y z : Obj C) → _∘_ D (F₁ G (α C x y z)) (_∘_ D (η μ-NatIso' (_⊗₀_ C x y , z)) (_⊗₁_ D (η μ-NatIso' (x , y)) (cat-id D {F₀ G z}))) 
                                                ≡ _∘_ D (η μ-NatIso' (x , _⊗₀_ C y z)) (_∘_ D (_⊗₁_ D (cat-id D {F₀ G x}) (η μ-NatIso' (y , z))) (α D (F₀ G x) (F₀ G y) (F₀ G z)))}
                    → {left-unitality  : (x : Obj C) → λ' D (F₀ F x) ≡ _∘_ D (F₁ F (λ' C x)) (_∘_ D (η μ-NatIso  (unit C , x)) (_⊗₁_ D ε  (cat-id D {F₀ F x})))}
                    → {left-unitality' : (x : Obj C) → λ' D (F₀ G x) ≡ _∘_ D (F₁ G (λ' C x)) (_∘_ D (η μ-NatIso' (unit C , x)) (_⊗₁_ D ε' (cat-id D {F₀ G x})))}
                    → {right-unitality  : (x : Obj C) → ρ D (F₀ F x) ≡ _∘_ D (F₁ F (ρ C x)) (_∘_ D (η μ-NatIso  (x , unit C)) (_⊗₁_ D (cat-id D {F₀ F x}) ε ))}
                    → {right-unitality' : (x : Obj C) → ρ D (F₀ G x) ≡ _∘_ D (F₁ G (ρ C x)) (_∘_ D (η μ-NatIso' (x , unit C)) (_⊗₁_ D (cat-id D {F₀ G x}) ε'))}
                    → F ≡ G → ε ≅ ε' → iso-ε ≅ iso-ε' → μ-NatIso ≅ μ-NatIso'
                    → monoidalFunctor {C = C} {D} F ε iso-ε μ-NatIso assoc left-unitality right-unitality ≡ monoidalFunctor G ε' iso-ε' μ-NatIso' assoc' left-unitality' right-unitality'
monoidal-functor-eq {F = F} {.F} {ε} {.ε} {iso-ε} {.iso-ε} {μ-NatIso} {.μ-NatIso} {assoc} {assoc'} {left-u} {left-u'} {right-u} {right-u'} refl refl refl refl 
  = cong₃ (monoidalFunctor F ε iso-ε μ-NatIso) 
          (fun-ext (λ x → fun-ext (λ y → fun-ext (λ z → proof-irrelevance (assoc x y z) (assoc' x y z))))) 
          (fun-ext (λ x → proof-irrelevance (left-u x) (left-u' x))) 
          (fun-ext (λ x → proof-irrelevance (right-u x) (right-u' x)))
