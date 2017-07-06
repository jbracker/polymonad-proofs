
open import Level
open import Function renaming ( _∘_ to _∘F_ ; id to idF )

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Extensionality

open import Theory.Category.Definition
open import Theory.Category.Examples.SetCat
open import Theory.Functor.Definition

module Theory.Functor.Examples.HomFunctor where

open Category

-- Definition of the Hom-Functor Hom[A,-] from C to Set.
homFunctor : {ℓC₀ ℓC₁ : Level} → (ℓSet : Level) → {C : Category {ℓC₀} {ℓC₁}} 
         → (a : Obj C) → Functor C (setCategory {ℓSet ⊔ ℓC₁ ⊔ ℓC₀})
homFunctor {ℓC₀} {ℓC₁} ℓSet {C} a = functor HomF₀ HomF₁ id-HomF compose-HomF
  where
    SetCat = setCategory {ℓSet ⊔ ℓC₁ ⊔ ℓC₀}
    _∘C_ = _∘_ C
    _∘Set_ = _∘_ SetCat
    
    HomF₀ : Obj C → Obj SetCat
    HomF₀ x = Lift {ℓ = ℓSet ⊔ ℓC₀} (Hom C a x)
    
    HomF₁ : {x y : Obj C} → Hom C x y → Hom SetCat (HomF₀ x) (HomF₀ y)
    HomF₁ f = λ g → lift (f ∘C lower g)

    abstract
      id-HomF : {a : Obj C} → HomF₁ (id C {a}) ≡ id SetCat
      id-HomF {a} = begin
        HomF₁ (id C)
          ≡⟨⟩
        ( λ g → lift (id C ∘C lower g) )
          ≡⟨ fun-ext (λ g → cong lift (right-id C)) ⟩
        ( λ g → g )
          ≡⟨⟩
        id SetCat ∎

    abstract
      compose-HomF : {a b c : Obj C} {f : Hom C a b} {g : Hom C b c} 
                   → HomF₁ (g ∘C f) ≡ (HomF₁ g) ∘Set (HomF₁ f)
      compose-HomF {f = f} {g} = begin
        HomF₁ (g ∘C f)
          ≡⟨⟩
        ( λ h → lift ((g ∘C f) ∘C lower h) )
          ≡⟨ fun-ext (λ h → cong lift (sym $ assoc C)) ⟩ 
        ( λ h → lift (g ∘C (f ∘C lower h)) )
          ≡⟨⟩ 
        (HomF₁ g) ∘Set (HomF₁ f) ∎

