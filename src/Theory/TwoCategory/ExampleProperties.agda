
open import Level
open import Function hiding ( _∘_ ; id )

open import Data.Unit
open import Relation.Binary.HeterogeneousEquality 
  renaming ( refl to hrefl; sym to hsym ; trans to htrans ; cong to hcong ; cong₂ to hcong₂ ; subst to hsubst ; subst₂ to hsubst₂ ; proof-irrelevance to hproof-irrelevance )
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning hiding ( _≅⟨_⟩_ )
open ≅-Reasoning hiding ( _≡⟨_⟩_ ; _≡⟨⟩_ ) renaming ( begin_ to hbegin_ ; _∎ to _∎h)

open import Extensionality

open import Theory.Category.Definition
open import Theory.Category.Examples renaming ( setCategory to SetCat )
open import Theory.Functor.Definition
open import Theory.Functor.Composition
open import Theory.Natural.Transformation
open import Theory.Natural.Transformation.Examples
open import Theory.TwoCategory.Definition
open import Theory.TwoCategory.Examples

module Theory.TwoCategory.ExampleProperties where

open Category
open NaturalTransformation
open StrictTwoCategory

private
  abstract
    helper : {ℓA₀ ℓA₁ ℓB₀ ℓB₁ : Level}
           → {A : Category {ℓA₀} {ℓA₁}} {B : Category {ℓB₀} {ℓB₁}}
           → {F G H : Functor A B}
           → (α : NaturalTransformation F G)
           → (p : G ≡ H)
           → (x : Obj A)
           → (q : [ G ]₀ x ≡ [ H ]₀ x)
           → η (subst₂ NaturalTransformation refl p α) x
           ≡ subst₂ (Hom B) refl q (η α x)
    helper α refl x refl = refl

abstract
  associator-eq : {ℓObj ℓHom : Level}
                → {A : Category {ℓObj} {ℓHom}} {B : Category {ℓObj} {ℓHom}}
                → {C : Category {ℓObj} {ℓHom}} {D : Category {ℓObj} {ℓHom}}
                → (F : Functor A B)
                → (G : Functor B C)
                → (H : Functor C D)
                → StrictTwoCategory.α (functorTwoCategory {ℓObj} {ℓHom}) F G H ≡ functorAssociator H G F
  associator-eq {ℓObj} {ℓHom} {A} {B} {C} {D} F G H = natural-transformation-eq $ fun-ext $ λ (x : Obj A) → begin
    η (subst₂ NaturalTransformation refl (hAssoc₁ (functorTwoCategory {ℓObj} {ℓHom})) (Id⟨ [ H ]∘[ [ G ]∘[ F ] ] ⟩)) x
      ≡⟨ helper Id⟨ [ H ]∘[ [ G ]∘[ F ] ] ⟩ (hAssoc₁ (functorTwoCategory {ℓObj} {ℓHom})) x refl ⟩
    subst₂ (Hom D) refl refl (η (Id⟨ [ H ]∘[ [ G ]∘[ F ] ] ⟩) x)
      ≡⟨ refl ⟩
    Category.id D {[ H ]₀ ([ G ]₀ ([ F ]₀ x))} ∎


open NaturalTransformation renaming ( η to nat-η )

private
  abstract
    nat-helper : {ℓ : Level} {F G : Functor (SetCat {ℓ}) (SetCat {ℓ})} → (p : F ≡ G) → (α : Obj (SetCat {ℓ})) → (x : [ G ]₀ α) → nat-η (subst₂ NaturalTransformation p refl Id⟨ F ⟩) α x ≅ x
    nat-helper {ℓ} {F} {.F} refl α x = hrefl

  abstract
    nat-helper2 : {ℓ : Level} {F G : Functor (SetCat {ℓ}) (SetCat {ℓ})} → (p : F ≡ G) → (α : Obj (SetCat {ℓ})) → (x : [ F ]₀ α) → nat-η (subst₂ NaturalTransformation refl p Id⟨ F ⟩) α x ≅ x
    nat-helper2 {ℓ} {F} {.F} refl α x = hrefl

abstract
  het-cat-λ-id : {ℓ : Level} {F : Functor (SetCat {ℓ}) (SetCat {ℓ})} → (a : Obj (SetCat {ℓ})) → (x : [ F ]₀ a) → nat-η (λ' Cat F) a x ≅ x
  het-cat-λ-id {ℓ} {F} a x = hbegin
    nat-η (λ' Cat F) a x
      ≅⟨ hrefl ⟩
    nat-η (subst₂ NaturalTransformation (sym $ hIdL₁ Cat {SetCat {ℓ}} {SetCat {ℓ}} {F}) refl (Id⟨ F ⟩)) a x
      ≅⟨ nat-helper (sym $ hIdL₁ Cat {SetCat {ℓ}} {SetCat {ℓ}} {F}) a x ⟩
    x ∎h

abstract
  het-cat-ρ-id : {ℓ : Level} {F : Functor (SetCat {ℓ}) (SetCat {ℓ})} → (a : Obj (SetCat {ℓ})) → (x : [ F ]₀ a) → nat-η (ρ Cat F) a x ≅ x
  het-cat-ρ-id {ℓ} {F} a x = hbegin
    nat-η (ρ Cat F) a x 
      ≅⟨ hrefl ⟩
    nat-η (subst₂ NaturalTransformation (sym $ hIdR₁ Cat {SetCat {ℓ}} {SetCat {ℓ}} {F}) refl (Id⟨ F ⟩)) a x
      ≅⟨ nat-helper (sym $ hIdR₁ Cat {SetCat {ℓ}} {SetCat {ℓ}} {F}) a x ⟩
    x ∎h

private
  abstract
    nat-subst-elim : {ℓC₀ ℓC₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {F F' G : Functor C C} 
                   → (α : NaturalTransformation F G) → (p : F ≡ F') → (c : Obj C) 
                   → nat-η α c ≅ nat-η (subst₂ (Cell₂ Cat) p refl α) c
    nat-subst-elim α refl c = hrefl

abstract
  cat-λ-id : {ℓC₀ ℓC₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {F : Functor C C} 
                → (c : Obj C) → id C ≡ nat-η (λ' Cat F) c
  cat-λ-id {C = C} {F} c = begin
    id C {[ F ]₀ c}
      ≡⟨ ≅-to-≡ $ nat-subst-elim (id₂ Cat {C} {C}) (sym $ hIdL₁ Cat {a = C} {C} {F}) c ⟩
    nat-η (subst₂ (Cell₂ Cat) (sym $ hIdL₁ Cat {a = C} {C} {F}) refl (id₂ Cat {C} {C})) c
      ≡⟨⟩
    nat-η (λ' Cat F) c ∎
  
  cat-ρ-id : {ℓC₀ ℓC₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {F : Functor C C} 
                → (c : Obj C) → id C ≡ nat-η (ρ Cat F) c
  cat-ρ-id {C = C} {F} c = begin
    id C {[ F ]₀ c}
      ≡⟨ ≅-to-≡ $ nat-subst-elim (id₂ Cat {C} {C}) (sym $ hIdR₁ Cat {a = C} {C} {F}) c ⟩
    nat-η (subst₂ (Cell₂ Cat) (sym $ hIdR₁ Cat {a = C} {C} {F}) refl (id₂ Cat {C} {C})) c
      ≡⟨⟩
    nat-η (ρ Cat F) c ∎

abstract
  het-cat-α-id : {ℓ : Level} {F G H : Functor (SetCat {ℓ}) (SetCat {ℓ})} 
               → (x : Obj (SetCat {ℓ})) → (y : [ H ]₀ ([ G ]₀ ([ F ]₀ x)))
               → nat-η (α Cat F G H) x y ≅ y
  het-cat-α-id {ℓ} {F} {G} {H} x y = hbegin
    nat-η (α Cat F G H) x y
      ≅⟨ hrefl ⟩
    nat-η (subst₂ NaturalTransformation refl (hAssoc₁ Cat {f = F} {G} {H}) (Id⟨ [ H ]∘[ [ G ]∘[ F ] ] ⟩) ) x y
      ≅⟨ nat-helper2 (hAssoc₁ Cat {f = F} {G} {H}) x y ⟩
    y ∎h

