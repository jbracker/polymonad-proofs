
open import Level
open import Function hiding ( _∘_ ; id )

open import Data.Unit
open import Relation.Binary.HeterogeneousEquality renaming ( refl to hrefl ; cong to hcong ; subst₂ to hsubst₂ )
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Extensionality

open import Theory.Category
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
    
