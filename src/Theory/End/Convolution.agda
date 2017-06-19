 
open import Level
open import Function renaming ( _∘_ to _∘F_ ; id to idF )

open import Data.Product

open import Relation.Binary.PropositionalEquality hiding ( [_] )
open ≡-Reasoning

open import Extensionality
open import Theory.Category.Definition
open import Theory.Category.Examples
open import Theory.Category.Monoidal
open import Theory.Functor.Definition
open import Theory.End.Definition
open import Theory.End.Wedge

module Theory.End.Convolution {ℓC₀ ℓC₁ ℓSet : Level} {C : Category {ℓC₀} {ℓC₁}} (CMon : MonoidalCategory C) where

open Category
open Functor

private
  Set' = setCategory {ℓSet ⊔ ℓC₁ ⊔ ℓC₀}

  _⊗C₀_ = MonoidalCategory._⊗₀_ CMon
  _⊗C₁_ = MonoidalCategory._⊗₁_ CMon
  _∘C_ = _∘_ C
  CC×CC = (C ×C C) op ×C (C ×C C)

convolutionFunctor : (F G : Functor C Set') → (c : Obj C) → Functor CC×CC Set'
convolutionFunctor (functor F₀ F₁ F-id F-compose) (functor G₀ G₁ G-id G-compose) c = functor dayF₀ dayF₁ day-id day-compose
  where
    dayF₀ : Obj (((C ×C C) op) ×C (C ×C C)) → Obj Set'
    dayF₀ ((c₁ , c₁') , (c₂ , c₂')) = Hom C (c₁ ⊗C₀ c₁') c × F₀ c₂ × G₀ c₂'
    
    dayF₁ : {a b : Obj CC×CC} → Hom CC×CC a b → Hom Set' (dayF₀ a) (dayF₀ b)
    dayF₁ {a} {b} ((f₁ , f₁') , (f₂ , f₂')) (homC , Fc , Fc') = (homC ∘C (f₁ ⊗C₁ f₁')) , F₁ f₂ Fc , G₁ f₂' Fc'
    
    day-id : {a : Obj CC×CC} → dayF₁ {a} {a} (id CC×CC) ≡ id Set'
    day-id {a} = begin
      dayF₁ {a} {a} (id CC×CC) 
        ≡⟨⟩
      (λ x → (proj₁ x ∘C (id C ⊗C₁ id C)) , F₁ (id C) (proj₁ (proj₂ x)) , G₁ (id C) (proj₂ (proj₂ x)))
        ≡⟨ fun-ext (λ x → cong₂ (λ X Y → (proj₁ x ∘C (id C ⊗C₁ id C)) , X , Y) (cong (λ X → X (proj₁ (proj₂ x))) F-id) (cong (λ X → X (proj₂ (proj₂ x))) G-id)) ⟩
      (λ x → (proj₁ x ∘C (id C ⊗C₁ id C)) , proj₁ (proj₂ x) , proj₂ (proj₂ x))
        ≡⟨⟩
      (λ x → (proj₁ x ∘C (id C ⊗C₁ id C)) , proj₂ x)
        ≡⟨ fun-ext (λ x → cong (λ X → (proj₁ x ∘C X) , proj₂ x) (Functor.id (MonoidalCategory.tensor CMon))) ⟩
      (λ x → (proj₁ x ∘C id C) , proj₂ x)
        ≡⟨ fun-ext (λ x → cong (λ X → X , proj₂ x) (Category.left-id C)) ⟩
      (λ x → proj₁ x , proj₂ x)
        ≡⟨⟩
      (λ x → x)
        ≡⟨⟩
      id Set' ∎
        
    _∘CC×CC_ = Category._∘_ CC×CC
    
    day-compose : {x y z : Obj CC×CC}
                → {f : Hom CC×CC x y} {g : Hom CC×CC y z}
                → dayF₁ (g ∘CC×CC f) ≡ dayF₁ g ∘F dayF₁ f
    day-compose {x} {y} {z} {(f₁ , f₁') , (f₂ , f₂')} {(g₁ , g₁') , (g₂ , g₂')} = begin
      dayF₁ (g ∘CC×CC f)
        ≡⟨⟩
      (λ a → (proj₁ a ∘C ((f₁ ∘C g₁) ⊗C₁ (f₁' ∘C g₁'))) , F₁ (g₂ ∘C f₂) (proj₁ (proj₂ a)) , G₁ (g₂' ∘C f₂') (proj₂ (proj₂ a)))
        ≡⟨ fun-ext (λ a → cong (λ X → (proj₁ a ∘C X) , F₁ (g₂ ∘C f₂) (proj₁ (proj₂ a)) , G₁ (g₂' ∘C f₂') (proj₂ (proj₂ a))) (MonoidalCategory.exchange CMon)) ⟩
      (λ a → (proj₁ a ∘C ((f₁ ⊗C₁ f₁') ∘C (g₁ ⊗C₁ g₁'))) , F₁ (g₂ ∘C f₂) (proj₁ (proj₂ a)) , G₁ (g₂' ∘C f₂') (proj₂ (proj₂ a)))
        ≡⟨ fun-ext (λ a → cong (λ X → X , F₁ (g₂ ∘C f₂) (proj₁ (proj₂ a)) , G₁ (g₂' ∘C f₂') (proj₂ (proj₂ a))) (Category.assoc C)) ⟩
      (λ a → ((proj₁ a ∘C (f₁ ⊗C₁ f₁')) ∘C (g₁ ⊗C₁ g₁')) , F₁ (g₂ ∘C f₂) (proj₁ (proj₂ a)) , G₁ (g₂' ∘C f₂') (proj₂ (proj₂ a)))
        ≡⟨ fun-ext (λ a → cong₂ (λ X Y → ((proj₁ a ∘C (f₁ ⊗C₁ f₁')) ∘C (g₁ ⊗C₁ g₁')) , X , Y) (cong (λ X → X (proj₁ (proj₂ a))) F-compose) (cong (λ X → X (proj₂ (proj₂ a))) G-compose)) ⟩
      (λ a → ((proj₁ a ∘C (f₁ ⊗C₁ f₁')) ∘C (g₁ ⊗C₁ g₁')) , F₁ g₂ (F₁ f₂ (proj₁ (proj₂ a))) , G₁ g₂' (G₁ f₂' (proj₂ (proj₂ a))))
        ≡⟨⟩
      (λ a → (proj₁ a ∘C (g₁ ⊗C₁ g₁')) , F₁ g₂ (proj₁ (proj₂ a)) , G₁ g₂' (proj₂ (proj₂ a))) ∘F (λ a → (proj₁ a ∘C (f₁ ⊗C₁ f₁')) , F₁ f₂ (proj₁ (proj₂ a)) , G₁ f₂' (proj₂ (proj₂ a)))
        ≡⟨⟩
      dayF₁ g ∘F dayF₁ f ∎
      where f = (f₁ , f₁') , (f₂ , f₂')
            g = (g₁ , g₁') , (g₂ , g₂')
