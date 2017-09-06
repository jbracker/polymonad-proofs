
open import Level
open import Function renaming ( _∘_ to _∘F_ ; id to idF )

open import Data.Product

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Extensionality

open import Theory.Category.Definition
open import Theory.Category.Examples.SetCat
open import Theory.Functor.Definition

module Theory.Functor.Examples.HomFunctor where

open Category

-- Definition of the Hom-Functor Hom[-,-] from C to Set.
homFunctor : {ℓC₀ ℓC₁ : Level} → (ℓSet : Level) → (C : Category {ℓC₀} {ℓC₁})
           → Functor (C op ×C C) (setCategory {ℓSet ⊔ ℓC₁ ⊔ ℓC₀})
homFunctor {ℓC₀} {ℓC₁} ℓSet C = functor HomF₀ HomF₁ id-HomF compose-HomF
  where
    SetCat = setCategory {ℓSet ⊔ ℓC₁ ⊔ ℓC₀}
    _∘C_ = _∘_ C
    _∘C×C_ = _∘_ (C op ×C C)
    _∘Set_ = _∘_ SetCat
    
    HomF₀ : Obj (C op ×C C) → Obj SetCat
    HomF₀ (a , b) = Lift {ℓ = ℓSet ⊔ ℓC₀} (Hom C a b)
    
    HomF₁ : {a b : Obj (C op ×C C)} → Hom (C op ×C C) a b → Hom SetCat (HomF₀ a) (HomF₀ b)
    HomF₁ (f' , f) = λ g → lift (f ∘C (lower g ∘C f'))

    abstract
      id-HomF : {a : Obj (C op ×C C)} → HomF₁ (id (C op ×C C) {a}) ≡ id SetCat
      id-HomF {a} = begin
        HomF₁ (id (C op ×C C))
          ≡⟨⟩
        ( λ g → lift (id (C op) ∘C (lower g ∘C id C)) )
          ≡⟨ fun-ext (λ g → cong lift (right-id C)) ⟩
        ( λ g → lift (lower g ∘C id C) )
          ≡⟨ fun-ext (λ g → cong lift (left-id C)) ⟩
        ( λ g → g )
          ≡⟨⟩
        id SetCat ∎

    abstract
      compose-HomF : {a b c : Obj (C op ×C C)} {f : Hom (C op ×C C) a b} {g : Hom (C op ×C C) b c} 
                   → HomF₁ (g ∘C×C f) ≡ (HomF₁ g) ∘Set (HomF₁ f)
      compose-HomF {f = f' , f} {g' , g} = begin
        HomF₁ (f' ∘C g' , g ∘C f)
          ≡⟨⟩
        (λ h → lift ((g ∘C f) ∘C (lower h ∘C (f' ∘C g'))) )
          ≡⟨ fun-ext (λ h → cong (λ X → lift ((g ∘C f) ∘C X)) (assoc C)) ⟩ 
        (λ h → lift ((g ∘C f) ∘C ((lower h ∘C f') ∘C g')) )
          ≡⟨ fun-ext (λ h → cong lift (sym $ assoc C)) ⟩ 
        (λ h → lift (g ∘C (f ∘C ((lower h ∘C f') ∘C g'))) )
          ≡⟨ fun-ext (λ h → cong (λ X → lift (g ∘C X)) (assoc C)) ⟩ 
        (λ h → lift (g ∘C ((f ∘C (lower h ∘C f')) ∘C g')) )
          ≡⟨⟩ 
        (λ h → lift (g ∘C (lower {ℓ = ℓSet ⊔ ℓC₀} (lift (f ∘C (lower h ∘C f'))) ∘C g')))
          ≡⟨⟩ 
        (λ h → lift (g ∘C (lower {ℓ = ℓSet ⊔ ℓC₀} h ∘C g'))) ∘Set (λ h' → lift (f ∘C (lower h' ∘C f')))
          ≡⟨⟩ 
        (HomF₁ (g' , g)) ∘Set (HomF₁ (f' , f)) ∎
