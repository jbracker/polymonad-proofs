
module Theory.Natural.Transformation where

-- Stdlib
open import Level
open import Function hiding ( _∘_ )
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality
  renaming ( sym to hsym ; trans to htrans ; cong to hcong ; subst₂ to hsubst₂ ; proof-irrelevance to hproof-irrelevance )
open ≡-Reasoning 

-- Local
open import Extensionality
open import Theory.Category.Definition
open import Theory.Functor.Definition
open import Theory.Functor.Composition

open Category
open Functor

-------------------------------------------------------------------------------
-- Definition of Natural Transformations
-------------------------------------------------------------------------------
record NaturalTransformation {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} 
                             {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}}
                             (F : Functor C D) (G : Functor C D) 
                             : Set (ℓC₀ ⊔ ℓC₁ ⊔ ℓD₀ ⊔ ℓD₁) where
  constructor naturalTransformation
  private _∘D_ = Category._∘_ D
  field
    η : (x : Obj C) → Hom D ([ F ]₀ x) ([ G ]₀ x)
    
    natural : {a b : Obj C} {f : Hom C a b} 
            → ([ G ]₁ f) ∘D (η a) ≡ (η b) ∘D ([ F ]₁ f)
            -- G₁ f ∘ η ≡ η ∘ F₁ f

η⟨_⟩_ = NaturalTransformation.η

-------------------------------------------------------------------------------
-- The Identity Natural Transformation
-------------------------------------------------------------------------------
idNaturalTransformation : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} 
                        → {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}}
                        → (F : Functor C D) → NaturalTransformation F F
idNaturalTransformation {C = C} {D = D} F = record 
  { η = λ x → Category.id D {[ F ]₀ x}
  ; natural = trans (left-id D) (sym (right-id D))
  }

Id⟨_⟩ = idNaturalTransformation

-------------------------------------------------------------------------------
-- Vertical Composition of Natural Transformations
-------------------------------------------------------------------------------
compNaturalTransformationVert : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} 
                              → {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}}
                              → {F G H : Functor C D}
                              → NaturalTransformation G H → NaturalTransformation F G
                              → NaturalTransformation F H
compNaturalTransformationVert {C = C} {D} {F} {G} {H} α β =  record 
  { η = η 
  ; natural = natural
  } where
    _∘D_ = Category._∘_ D
    ηα = NaturalTransformation.η α
    ηβ = NaturalTransformation.η β
    
    η :  (a : Category.Obj C) → Category.Hom D ([ F ]₀ a) ([ H ]₀ a)
    η a = ηα a ∘D ηβ a
    
    natural : {a b : Category.Obj C} {f : Category.Hom C a b} 
            → ([ H ]₁ f) ∘D (η a) ≡ (η b) ∘D ([ F ]₁ f)
    natural {a} {b} {f} = begin
      ([ H ]₁ f) ∘D (η a) 
        ≡⟨ refl ⟩
      ([ H ]₁ f) ∘D (ηα a ∘D ηβ a) 
        ≡⟨ Category.assoc D ⟩
      (([ H ]₁ f) ∘D ηα a) ∘D ηβ a 
        ≡⟨ cong (λ X → X ∘D ηβ a) (NaturalTransformation.natural α) ⟩
      (ηα b ∘D ([ G ]₁ f)) ∘D ηβ a 
        ≡⟨ sym (Category.assoc D) ⟩
      ηα b ∘D (([ G ]₁ f) ∘D ηβ a)
        ≡⟨ cong (λ X → ηα b ∘D X) (NaturalTransformation.natural β) ⟩
      ηα b ∘D (ηβ b ∘D ([ F ]₁ f))
        ≡⟨ Category.assoc D ⟩
      (ηα b ∘D ηβ b) ∘D ([ F ]₁ f)
        ≡⟨ refl ⟩
      (η b) ∘D ([ F ]₁ f) ∎

⟨_⟩∘ᵥ⟨_⟩ = compNaturalTransformationVert

-------------------------------------------------------------------------------
-- Horizontal Composition of Natural Transformations
-------------------------------------------------------------------------------

compNaturalTransformationHorz 
  : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ ℓE₀ ℓE₁ : Level} 
  → {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}} {E : Category {ℓE₀} {ℓE₁}}
  → {G G' : Functor D E} {F F' : Functor C D}
  → NaturalTransformation G G' → NaturalTransformation F F'
  → NaturalTransformation [ G ]∘[ F ] [ G' ]∘[ F' ]
compNaturalTransformationHorz {C = C} {D} {E} {G} {G'} {F} {F'} α β =  record 
  { η = η 
  ; natural = natural
  } where
    _∘E_ = Category._∘_ E
    _∘D_ = Category._∘_ D
    ηα = NaturalTransformation.η α
    ηβ = NaturalTransformation.η β

    η : (c : Obj C) → Hom E ([ [ G ]∘[ F ] ]₀ c) ([ [ G' ]∘[ F' ] ]₀ c)
    η c = ηα ([ F' ]₀ c) ∘E [ G ]₁ (ηβ c)
    
    natural : {a b : Obj C} {f : Hom C a b} 
            → ([ [ G' ]∘[ F' ] ]₁ f) ∘E (η a) ≡ (η b) ∘E ([ [ G ]∘[ F ] ]₁ f)
    natural {a} {b} {f} = begin
      ([ [ G' ]∘[ F' ] ]₁ f) ∘E (η a) 
        ≡⟨ refl ⟩ 
      [ G' ]₁ ([ F' ]₁ f) ∘E (ηα ([ F' ]₀ a) ∘E [ G ]₁ (ηβ a)) 
        ≡⟨ Category.assoc E ⟩ 
      ([ G' ]₁ ([ F' ]₁ f) ∘E ηα ([ F' ]₀ a)) ∘E [ G ]₁ (ηβ a)
        ≡⟨ cong (λ X → X ∘E [ G ]₁ (ηβ a)) (NaturalTransformation.natural α) ⟩ 
      (ηα ([ F' ]₀ b) ∘E [ G ]₁ ([ F' ]₁ f)) ∘E [ G ]₁ (ηβ a)
        ≡⟨ sym (Category.assoc E) ⟩ 
      ηα ([ F' ]₀ b) ∘E ([ G ]₁ ([ F' ]₁ f) ∘E [ G ]₁ (ηβ a))
        ≡⟨ cong (λ X → ηα ([ F' ]₀ b) ∘E X) (sym (Functor.compose G)) ⟩ 
      ηα ([ F' ]₀ b) ∘E [ G ]₁ ([ F' ]₁ f ∘D ηβ a)
        ≡⟨ cong (λ X → ηα ([ F' ]₀ b) ∘E [ G ]₁ X) (NaturalTransformation.natural β) ⟩ 
      ηα ([ F' ]₀ b) ∘E [ G ]₁ (ηβ b ∘D [ F ]₁ f)
        ≡⟨ cong (λ X → ηα ([ F' ]₀ b) ∘E X) (Functor.compose G) ⟩
      ηα ([ F' ]₀ b) ∘E ([ G ]₁ (ηβ b) ∘E [ G ]₁ ([ F ]₁ f))
        ≡⟨ Category.assoc E ⟩ 
      (ηα ([ F' ]₀ b) ∘E [ G ]₁ (ηβ b)) ∘E [ G ]₁ ([ F ]₁ f)
        ≡⟨ refl ⟩ 
      (η b) ∘E ([ [ G ]∘[ F ] ]₁ f) ∎

⟨_⟩∘ₕ⟨_⟩ = compNaturalTransformationHorz

-------------------------------------------------------------------------------
-- Heterogeneous substitution elimination
-------------------------------------------------------------------------------

open NaturalTransformation

-- We can only do this heterogeneously.
subst₂-insert : ∀ {ℓA₀ ℓA₁ ℓB₀ ℓB₁}
              → {A : Category {ℓA₀} {ℓA₁}} {B : Category {ℓB₀} {ℓB₁}} 
              → {F F' G G' : Functor A B}
              → (eqA : F ≡ F')
              → (eqB : G ≡ G')
              → (α : NaturalTransformation F G)
              → (x : Obj A) 
              → η α x ≅ η (subst₂ NaturalTransformation eqA eqB α) x
subst₂-insert refl refl α x = refl

subst₂-replace : ∀ {ℓA₀ ℓA₁ ℓB₀ ℓB₁}
              → {A : Category {ℓA₀} {ℓA₁}} {B : Category {ℓB₀} {ℓB₁}} 
              → {F G : Functor A B}
              → (α β : NaturalTransformation F G)
              → (α ≅ β)
              → (x : Obj A) 
              → η α x ≅ η β x
subst₂-replace α .α refl x = refl

-------------------------------------------------------------------------------
-- Equality of Natural Transformations
-------------------------------------------------------------------------------

natural-transformation-eq : {Cℓ₀ Cℓ₁ Dℓ₀ Dℓ₁ : Level} 
                          → {C : Category {Cℓ₀} {Cℓ₁}} {D : Category {Dℓ₀} {Dℓ₁}} 
                          → {F G : Functor C D}
                          → {η₀ : (x : Obj C) → Hom D ([ F ]₀ x) ([ G ]₀ x)}
                          → {η₁ : (x : Obj C) → Hom D ([ F ]₀ x) ([ G ]₀ x)}
                          → {nat₀ : {a b : Obj C} {f : Hom C a b} → ( _∘_ D ([ G ]₁ f) (η₀ a) ) ≡ ( _∘_ D (η₀ b) ([ F ]₁ f) )}
                          → {nat₁ : {a b : Obj C} {f : Hom C a b} → ( _∘_ D ([ G ]₁ f) (η₁ a) ) ≡ ( _∘_ D (η₁ b) ([ F ]₁ f) )}
                          → η₀ ≡ η₁
                          → naturalTransformation {F = F} {G = G} η₀ nat₀ ≡ naturalTransformation {F = F} {G = G} η₁ nat₁
natural-transformation-eq {η₀ = η₀} {.η₀} {nat₀} {nat₁} refl 
  = cong (naturalTransformation η₀) 
  $ implicit-fun-ext (λ a → implicit-fun-ext (λ b → implicit-fun-ext (λ f → proof-irrelevance (nat₀ {a} {b} {f}) (nat₁ {a} {b} {f}) ) ) )

het-natural-transformation-eq : {Cℓ₀ Cℓ₁ Dℓ₀ Dℓ₁ : Level} 
                               → {C : Category {Cℓ₀} {Cℓ₁}} {D : Category {Dℓ₀} {Dℓ₁}} 
                               → {F G : Functor C D}
                               → {η₀ : (x : Obj C) → Hom D ([ F ]₀ x) ([ G ]₀ x)}
                               → {η₁ : (x : Obj C) → Hom D ([ F ]₀ x) ([ G ]₀ x)}
                               → {nat₀ : {a b : Obj C} {f : Hom C a b} → ( _∘_ D ([ G ]₁ f) (η₀ a) ) ≅ ( _∘_ D (η₀ b) ([ F ]₁ f) )}
                               → {nat₁ : {a b : Obj C} {f : Hom C a b} → ( _∘_ D ([ G ]₁ f) (η₁ a) ) ≅ ( _∘_ D (η₁ b) ([ F ]₁ f) )}
                               → η₀ ≅ η₁
                               → naturalTransformation {F = F} {G = G} η₀ (≅-to-≡ nat₀) ≅ naturalTransformation {F = F} {G = G} η₁ (≅-to-≡ nat₁)
het-natural-transformation-eq {η₀ = η₀} {.η₀} {nat₀} {nat₁} refl 
  with het-implicit-fun-ext refl (λ a → het-implicit-fun-ext refl (λ b → het-implicit-fun-ext refl (λ f → ≡-to-≅ (hproof-irrelevance (nat₀ {a} {b} {f}) (nat₁ {a} {b} {f})) ) ) )
het-natural-transformation-eq {η₀ = η₀} {.η₀} {nat₀} {.nat₀} refl | refl = refl
