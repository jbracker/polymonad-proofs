
open import Level
open import Function hiding ( _∘_ ; id )

open import Data.Unit
open import Relation.Binary.HeterogeneousEquality 
  renaming ( refl to hrefl; sym to hsym ; trans to htrans ; cong to hcong ; cong₂ to hcong₂ ; subst to hsubst ; subst₂ to hsubst₂ ; proof-irrelevance to hproof-irrelevance )
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning hiding ( _≅⟨_⟩_ )
open ≅-Reasoning hiding ( _≡⟨_⟩_ ; _≡⟨⟩_ ) renaming ( begin_ to hbegin_ ; _∎ to _∎h)

open import Extensionality

open import Theory.Category
open import Theory.Category.Examples renaming ( setCategory to SetCat )
open import Theory.Functor
open import Theory.Functor.Composition
open import Theory.Natural.Transformation
open import Theory.Natural.Transformation.Examples
open import Theory.TwoCategory
open import Theory.TwoCategory.Examples

module Theory.TwoCategory.ExampleProperties where

open Category
open NaturalTransformation

private
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


associator-eq : {ℓObj ℓHom : Level}
              → {A : Category {ℓObj} {ℓHom}} {B : Category {ℓObj} {ℓHom}}
              → {C : Category {ℓObj} {ℓHom}} {D : Category {ℓObj} {ℓHom}}
              → (F : Functor A B)
              → (G : Functor B C)
              → (H : Functor C D)
              → StrictTwoCategory.α (functorTwoCategory {ℓObj} {ℓHom}) F G H ≡ functorAssociator H G F
associator-eq {ℓObj} {ℓHom} {A} {B} {C} {D} F G H = natural-transformation-eq $ fun-ext $ λ (x : Obj A) → begin
  η (subst₂ NaturalTransformation refl (functor-eq refl hrefl) (Id⟨ [ H ]∘[ [ G ]∘[ F ] ] ⟩)) x
    ≡⟨ helper Id⟨ [ H ]∘[ [ G ]∘[ F ] ] ⟩ (functor-eq refl hrefl) x refl ⟩
  subst₂ (Hom D) refl refl (η (Id⟨ [ H ]∘[ [ G ]∘[ F ] ] ⟩) x)
    ≡⟨ refl ⟩
  Category.id D {[ H ]₀ ([ G ]₀ ([ F ]₀ x))} ∎


open StrictTwoCategory
open NaturalTransformation renaming ( η to nat-η )

private
  nat-helper : {ℓ : Level} {F G : Functor (SetCat {ℓ}) (SetCat {ℓ})} → (p : F ≡ G) → (α : Obj (SetCat {ℓ})) → (x : [ G ]₀ α) → nat-η (subst₂ NaturalTransformation p refl Id⟨ F ⟩) α x ≅ x
  nat-helper {ℓ} {F} {.F} refl α x = hrefl

  nat-helper2 : {ℓ : Level} {F G : Functor (SetCat {ℓ}) (SetCat {ℓ})} → (p : F ≡ G) → (α : Obj (SetCat {ℓ})) → (x : [ F ]₀ α) → nat-η (subst₂ NaturalTransformation refl p Id⟨ F ⟩) α x ≅ x
  nat-helper2 {ℓ} {F} {.F} refl α x = hrefl

het-cat-λ-id : {ℓ : Level} {F : Functor (SetCat {ℓ}) (SetCat {ℓ})} → (a : Obj (SetCat {ℓ})) → (x : [ F ]₀ a) → nat-η (λ' Cat F) a x ≅ x
het-cat-λ-id {ℓ} {F} a x = hrefl

het-cat-ρ-id : {ℓ : Level} {F : Functor (SetCat {ℓ}) (SetCat {ℓ})} → (a : Obj (SetCat {ℓ})) → (x : [ F ]₀ a) → nat-η (ρ Cat F) a x ≅ x
het-cat-ρ-id {ℓ} {F} a x = hbegin
  nat-η (ρ Cat F) a x 
    ≅⟨ hrefl ⟩
  nat-η (subst₂ NaturalTransformation (sym $ hIdR₁ Cat {SetCat {ℓ}} {SetCat {ℓ}} {F}) refl (Id⟨ F ⟩)) a x
    ≅⟨ nat-helper (sym $ hIdR₁ Cat {SetCat {ℓ}} {SetCat {ℓ}} {F}) a x ⟩
  x ∎h


het-cat-α-id : {ℓ : Level} {F G H : Functor (SetCat {ℓ}) (SetCat {ℓ})} 
             → (x : Obj (SetCat {ℓ})) → (y : [ H ]₀ ([ G ]₀ ([ F ]₀ x)))
             → nat-η (α Cat F G H) x y ≅ y
het-cat-α-id {ℓ} {F} {G} {H} x y = hbegin
  nat-η (α Cat F G H) x y
    ≅⟨ hrefl ⟩
  nat-η (subst₂ NaturalTransformation refl (hAssoc₁ Cat {f = F} {G} {H}) (Id⟨ [ H ]∘[ [ G ]∘[ F ] ] ⟩) ) x y
    ≅⟨ nat-helper2 (hAssoc₁ Cat {f = F} {G} {H}) x y ⟩
  y ∎h

