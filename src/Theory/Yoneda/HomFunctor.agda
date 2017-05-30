
open import Level
open import Function renaming ( _∘_ to _∘F_ ; id to idF )

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Extensionality

open import Theory.Category.Definition
open import Theory.Category.Examples
open import Theory.Functor.Definition

module Theory.Yoneda.HomFunctor {ℓC₀ ℓC₁ : Level} {C : Category {ℓC₀} {ℓC₁}} where

open Category

private
  SetCat = setCategory {ℓC₁}
  _∘C_ = _∘_ C
  _∘Set_ = _∘_ SetCat

-- Definition of the Hom-Functor Hom[A,-] from C to Set.
Hom[_,-] : (a : Obj C) → Functor C SetCat
Hom[_,-] a = functor HomF₀ HomF₁ id-HomF compose-HomF
  where
    HomF₀ : Obj C → Obj SetCat
    HomF₀ x = Hom C a x
    
    HomF₁ : {x y : Obj C} → Hom C x y → Hom SetCat (HomF₀ x) (HomF₀ y)
    HomF₁ f = λ g → f ∘C g
    
    id-HomF : {a : Obj C} → HomF₁ (id C {a}) ≡ id SetCat
    id-HomF {a} = begin
      HomF₁ (id C) 
        ≡⟨⟩
      ( λ g → id C ∘C g )
        ≡⟨ fun-ext (λ g → right-id C {f = g}) ⟩
      ( λ g → g )
        ≡⟨⟩
      id SetCat ∎
    
    compose-HomF : {a b c : Obj C} {f : Hom C a b} {g : Hom C b c} 
                 → HomF₁ (g ∘C f) ≡ (HomF₁ g) ∘Set (HomF₁ f)
    compose-HomF {f = f} {g} = begin
      HomF₁ (g ∘C f) 
        ≡⟨ refl ⟩
      ( λ h → (g ∘C f) ∘C h )
        ≡⟨ fun-ext (λ h → sym (assoc C {f = h} {f} {g})) ⟩ 
      ( λ h → g ∘C (f ∘C h) )
        ≡⟨ refl ⟩ 
      (HomF₁ g) ∘Set (HomF₁ f) ∎
