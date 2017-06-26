 
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
open import Theory.End.Properties
open import Theory.End.Wedge

module Theory.End.Convolution where

open Category
open Functor

convolutionFunctor : {ℓC₀ ℓC₁ ℓSet : Level} {C : Category {ℓC₀} {ℓC₁}} (CMon : MonoidalCategory C) 
                   → (F G : Functor C (setCategory {ℓSet ⊔ ℓC₁ ⊔ ℓC₀})) → (c : Obj C) 
                   → Functor ((C ×C C) op ×C (C ×C C)) (setCategory {ℓSet ⊔ ℓC₁ ⊔ ℓC₀})
convolutionFunctor {ℓC₀} {ℓC₁} {ℓSet} {C} CMon (functor F₀ F₁ F-id F-compose) (functor G₀ G₁ G-id G-compose) c = functor dayF₀ dayF₁ day-id day-compose
  where
    Set' = setCategory {ℓSet ⊔ ℓC₁ ⊔ ℓC₀}
    CC×CC = (C ×C C) op ×C (C ×C C)

    _⊗C₀_ = MonoidalCategory._⊗₀_ CMon
    _⊗C₁_ = MonoidalCategory._⊗₁_ CMon
    _∘C_ = _∘_ C
    _∘CC×CC_ = Category._∘_ CC×CC
    
    dayF₀ : Obj (((C ×C C) op) ×C (C ×C C)) → Obj Set'
    dayF₀ ((c₁ , c₁') , (c₂ , c₂')) = Hom C (c₁ ⊗C₀ c₁') c × F₀ c₂ × G₀ c₂'
    
    dayF₁ : {a b : Obj CC×CC} → Hom CC×CC a b → Hom Set' (dayF₀ a) (dayF₀ b)
    dayF₁ {a} {b} ((f₁ , f₁') , (f₂ , f₂')) (homC , Fc , Fc') = (homC ∘C (f₁ ⊗C₁ f₁')) , F₁ f₂ Fc , G₁ f₂' Fc'

    abstract
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

convolutionTransformation : {ℓC₀ ℓC₁ ℓSet : Level} {C : Category {ℓC₀} {ℓC₁}} (CMon : MonoidalCategory C) 
                          → {F G F' G' : Functor C (setCategory {ℓSet ⊔ ℓC₁ ⊔ ℓC₀})} 
                          → (α : NaturalTransformation F F') → (β : NaturalTransformation G G')
                          → {a b : Obj C} → Hom C a b 
                          → NaturalTransformation (convolutionFunctor {ℓSet = ℓSet} CMon F G a) (convolutionFunctor {ℓSet = ℓSet} CMon F' G' b)
convolutionTransformation {ℓC₀} {ℓC₁} {ℓSet} {C} CMon {F} {G} {F'} {G'} α β {a} {b} g = naturalTransformation η nat
  where
    Set' = setCategory {ℓSet ⊔ ℓC₁ ⊔ ℓC₀}
    CC×CC = (C ×C C) op ×C (C ×C C)
    
    _⊗C₀_ = MonoidalCategory._⊗₀_ CMon
    _⊗C₁_ = MonoidalCategory._⊗₁_ CMon
    _∘C_ = _∘_ C
    _∘CC×CC_ = Category._∘_ CC×CC
    
    open NaturalTransformation renaming ( η to nat-η )
    
    η : (x' : Obj CC×CC) → Hom Set' ([ convolutionFunctor {ℓSet = ℓSet} CMon F G a ]₀ x') ([ convolutionFunctor {ℓSet = ℓSet} CMon F' G' b ]₀ x')
    η ((c₀⁻ , c₁⁻) , (c₀⁺ , c₁⁺)) (f , Fc₀ , Gc₁) = (g ∘C f) , nat-η α c₀⁺ Fc₀ , nat-η β c₁⁺ Gc₁

    abstract
      nat : {x y : Obj CC×CC} {f : Hom CC×CC x y} → [ convolutionFunctor {ℓSet = ℓSet} CMon F' G' b ]₁ f ∘F η x ≡ η y ∘F [ convolutionFunctor {ℓSet = ℓSet} CMon F G a ]₁ f
      nat {x} {y} {f} = begin
        [ convolutionFunctor {ℓSet = ℓSet} CMon F' G' b ]₁ f ∘F η x
          ≡⟨⟩
        (λ {(h , Fc₀ , Gc₁) → ((g ∘C h) ∘C ((proj₁ (proj₁ f)) ⊗C₁ (proj₂ (proj₁ f)))) , F₁ F' (proj₁ (proj₂ f)) (nat-η α (proj₁ (proj₂  x)) Fc₀) , F₁ G' (proj₂ (proj₂ f)) (nat-η β (proj₂ (proj₂ x)) Gc₁)})
          ≡⟨ fun-ext (λ {(h , Fc₀ , Gc₁) → cong (λ X → X , F₁ F' (proj₁ (proj₂ f)) (nat-η α (proj₁ (proj₂ x)) Fc₀) , F₁ G' (proj₂ (proj₂ f)) (nat-η β (proj₂ (proj₂ x)) Gc₁)) (sym (assoc C))}) ⟩
        (λ {(h , Fc₀ , Gc₁) → (g ∘C (h ∘C ((proj₁ (proj₁ f)) ⊗C₁ (proj₂ (proj₁ f))))) , F₁ F' (proj₁ (proj₂ f)) (nat-η α (proj₁ (proj₂  x)) Fc₀) , F₁ G' (proj₂ (proj₂ f)) (nat-η β (proj₂ (proj₂ x)) Gc₁)})
          ≡⟨ fun-ext (λ {(h , Fc₀ , Gc₁) → cong₂ (λ X Y → (g ∘C (h ∘C ((proj₁ (proj₁ f)) ⊗C₁ (proj₂ (proj₁ f))))) , X , Y) (cong (λ Z → Z Fc₀) (natural α)) (cong (λ Z → Z Gc₁) (natural β))}) ⟩
        (λ {(h , Fc₀ , Gc₁) → (g ∘C (h ∘C ((proj₁ (proj₁ f)) ⊗C₁ (proj₂ (proj₁ f))))) , nat-η α (proj₁ (proj₂ y)) (F₁ F (proj₁ (proj₂ f)) Fc₀) , nat-η β (proj₂ (proj₂ y)) (F₁ G (proj₂ (proj₂ f)) Gc₁)})
          ≡⟨⟩
        η y ∘F [ convolutionFunctor {ℓSet = ℓSet} CMon F G a ]₁ f ∎

convolutionTransObj : {ℓC₀ ℓC₁ ℓSet : Level} {C : Category {ℓC₀} {ℓC₁}} (CMon : MonoidalCategory C) 
                    → (F G : Functor C (setCategory {ℓSet ⊔ ℓC₁ ⊔ ℓC₀})) → {a b : Obj C} → Hom C a b 
                    → NaturalTransformation (convolutionFunctor {ℓSet = ℓSet} CMon F G a) (convolutionFunctor {ℓSet = ℓSet} CMon F G b)
convolutionTransObj {ℓC₀} {ℓC₁} {ℓSet} {C} CMon F G f = convolutionTransformation {ℓSet = ℓSet} CMon (Id⟨ F ⟩) (Id⟨ G ⟩) f

convolutionTransFun : {ℓC₀ ℓC₁ ℓSet : Level} {C : Category {ℓC₀} {ℓC₁}} (CMon : MonoidalCategory C) 
                    → {F G F' G' : Functor C (setCategory {ℓSet ⊔ ℓC₁ ⊔ ℓC₀})} 
                    → (α : NaturalTransformation F F') → (β : NaturalTransformation G G') 
                    → (x : Obj C)
                    → NaturalTransformation (convolutionFunctor {ℓSet = ℓSet} CMon F G x) (convolutionFunctor {ℓSet = ℓSet} CMon F' G' x)
convolutionTransFun {ℓC₀} {ℓC₁} {ℓSet} {C} CMon α β x = convolutionTransformation {ℓSet = ℓSet} CMon α β (Category.id C {x})

abstract
  convolution-trans-obj-id : {ℓC₀ ℓC₁ ℓSet : Level} {C : Category {ℓC₀} {ℓC₁}} (CMon : MonoidalCategory C) 
                         → (F G : Functor C (setCategory {ℓSet ⊔ ℓC₁ ⊔ ℓC₀})) → (a : Obj C) → convolutionTransObj {ℓSet = ℓSet} CMon F G (id C {a}) ≡ Id⟨ convolutionFunctor {ℓSet = ℓSet} CMon F G a ⟩
  convolution-trans-obj-id {ℓC₀} {ℓC₁} {ℓSet} {C} CMon F G a = natural-transformation-eq $ fun-ext $ λ (c : Obj ((C ×C C) op ×C (C ×C C))) → fun-ext (λ {(f , Fc , Gc) → cong (λ X → X , Fc , Gc) (right-id C)})

