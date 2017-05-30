
-- StdLib
open import Level renaming ( zero to lzero ; suc to lsuc )
open import Function using ( _$_ )

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality hiding ( cong ; sym )

-- Local
open import Extensionality
open import Theory.Category.Definition
open import Theory.Category.Isomorphism
open import Theory.Functor.Definition
open import Theory.Natural.Transformation

module Theory.Natural.Isomorphism where
  
open Category

-------------------------------------------------------------------------------
-- Definition of a natural isomorphism: 
-- https://ncatlab.org/nlab/show/natural+isomorphism
-- A natural isomorphism is a natural transformation where every
-- arrow mapped by the natural transformation has an inverse arrow
-- that is its left and right identity.
-------------------------------------------------------------------------------
record NaturalIsomorphism {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} 
                          {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}}
                          (F : Functor C D) (G : Functor C D) : Set (ℓC₀ ⊔ ℓC₁ ⊔ ℓD₀ ⊔ ℓD₁) where
  constructor naturalIsomorphism
  field
    natural-transformation : NaturalTransformation F G

  open NaturalTransformation natural-transformation renaming ( natural to η-natural ) public
  open Functor hiding ( id )
  private
    _∘D_ = _∘_ D
  
  field
    isomorphic : (x : Obj C) → Isomorphism D (η x)
  
  private
    module Isomorphic (x : Obj C) where
      private iso = isomorphic x
      open Isomorphism iso hiding ( f⁻¹ ) public
  open Isomorphic renaming ( left-id to inv-left-id ; right-id to inv-right-id ) public
  
  open ≡-Reasoning
  
  inv-natural : {a b : Obj C} {f : Hom C a b} → [ F ]₁ f ∘D inv a ≡ inv b ∘D [ G ]₁ f
  inv-natural {a} {b} {f} = begin
    [ F ]₁ f ∘D inv a
      ≡⟨ sym $ right-id D ⟩
    id D ∘D ([ F ]₁ f ∘D inv a)
      ≡⟨ cong (λ X → X ∘D ([ F ]₁ f ∘D inv a)) (sym $ inv-right-id b) ⟩
    (inv b ∘D η b) ∘D ([ F ]₁ f ∘D inv a)
      ≡⟨ sym $ assoc D ⟩
    inv b ∘D (η b ∘D ([ F ]₁ f ∘D inv a))
      ≡⟨ cong (λ X → inv b ∘D X) (assoc D) ⟩
    inv b ∘D ((η b ∘D [ F ]₁ f) ∘D inv a)
      ≡⟨ cong (λ X → inv b ∘D (X ∘D inv a)) (sym $ η-natural) ⟩
    inv b ∘D (([ G ]₁ f ∘D η a) ∘D inv a)
      ≡⟨ cong (λ X → inv b ∘D X) (sym $ assoc D) ⟩
    inv b ∘D ([ G ]₁ f ∘D (η a ∘D inv a))
      ≡⟨ cong (λ X → inv b ∘D ([ G ]₁ f ∘D X)) (inv-left-id a) ⟩
    inv b ∘D ([ G ]₁ f ∘D id D)
      ≡⟨ cong (λ X → inv b ∘D X) (left-id D) ⟩
    inv b ∘D [ G ]₁ f ∎
  
  inv-natural-transformation : NaturalTransformation G F
  inv-natural-transformation = naturalTransformation inv inv-natural

-------------------------------------------------------------------------------
-- Equality of natural isomorphisms
-------------------------------------------------------------------------------
natural-isomorphism-eq : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} 
                       → {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}}
                       → {F : Functor C D} {G : Functor C D}
                       → {nat₀ nat₁ : NaturalTransformation F G}
                       → {iso₀ : (x : Obj C) → Isomorphism D (NaturalTransformation.η nat₀ x)}
                       → {iso₁ : (x : Obj C) → Isomorphism D (NaturalTransformation.η nat₁ x)}
                       → nat₀ ≡ nat₁ → iso₀ ≅ iso₁
                       → naturalIsomorphism nat₀ iso₀ ≡ naturalIsomorphism nat₁ iso₁
natural-isomorphism-eq {nat₀ = nat} {.nat} {iso} {.iso} refl refl = refl
