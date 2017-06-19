 
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
open import Theory.Natural.Transformation
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

convolutionTransformation : (F G : Functor C Set') → {a b : Obj C} → Hom C a b → NaturalTransformation (convolutionFunctor F G a) (convolutionFunctor F G b)
convolutionTransformation (functor F₀ F₁ F-id F-compose) (functor G₀ G₁ G-id G-compose) {a} {b} g = naturalTransformation η nat
  where
    F = functor F₀ F₁ F-id F-compose
    G = functor G₀ G₁ G-id G-compose

    η : (c : Obj CC×CC) → Hom Set' ([ convolutionFunctor F G a ]₀ c) ([ convolutionFunctor F G b ]₀ c)
    η ((c₀⁻ , c₁⁻) , (c₀⁺ , c₁⁺)) (f , Fc₀ , Gc₁) = (g ∘C f) , Fc₀ , Gc₁
    
    nat : {x y : Obj CC×CC} {f : Hom CC×CC x y} → [ convolutionFunctor F G b ]₁ f ∘F η x ≡ η y ∘F [ convolutionFunctor F G a ]₁ f
    nat {x} {y} {(f₀⁻ , f₁⁻) , (f₀⁺ , f₁⁺)} = begin
      (λ {(f , Fc , Gc) → [ convolutionFunctor F G b ]₁ ((f₀⁻ , f₁⁻) , (f₀⁺ , f₁⁺)) ((g ∘C f) , Fc , Gc)})
        ≡⟨⟩
      (λ {(f , Fc , Gc) → (((g ∘C f) ∘C (f₀⁻ ⊗C₁ f₁⁻)) , F₁ f₀⁺ Fc , G₁ f₁⁺ Gc)})
        ≡⟨ fun-ext (λ {(f , Fc , Gc) → cong (λ X → (X , F₁ f₀⁺ Fc , G₁ f₁⁺ Gc)) (sym $ assoc C)}) ⟩
      (λ {(f , Fc , Gc) → ((g ∘C (f ∘C (f₀⁻ ⊗C₁ f₁⁻))) , F₁ f₀⁺ Fc , G₁ f₁⁺ Gc)})
        ≡⟨⟩
      (λ {(f , Fc , Gc) → η y ([ convolutionFunctor F G a ]₁ ((f₀⁻ , f₁⁻) , (f₀⁺ , f₁⁺)) (f , Fc , Gc))}) ∎

convolution-transformation-id : (F G : Functor C Set') → (a : Obj C) → convolutionTransformation F G (id C {a}) ≡ Id⟨ convolutionFunctor F G a ⟩
convolution-transformation-id F G a = natural-transformation-eq $ fun-ext $ λ (c : Obj CC×CC) → fun-ext (λ {(f , Fc , Gc) → cong (λ X → X , Fc , Gc) (right-id C)})
