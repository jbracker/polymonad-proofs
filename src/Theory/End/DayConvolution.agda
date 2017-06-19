
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

module Theory.End.DayConvolution {ℓC₀ ℓC₁ ℓSet : Level} {C : Category {ℓC₀} {ℓC₁}} (CMon : MonoidalCategory C) where

open Category
open Functor

private
  Set' = setCategory {ℓSet ⊔ ℓC₁ ⊔ ℓC₀}

  _⊗C₀_ = MonoidalCategory._⊗₀_ CMon
  _⊗C₁_ = MonoidalCategory._⊗₁_ CMon
  _∘C_ = _∘_ C

open import Theory.End.Convolution {ℓC₀} {ℓC₁} {ℓSet} {C} CMon renaming ( convolutionFunctor to dayF )
open import Theory.End.Properties {ℓC₀} {ℓC₁} {ℓSet} {C ×C C}

dayConvolution : Functor ([ C , Set' ] ×C [ C , Set' ]) [ C , Set' ]
dayConvolution = functor day₀ day₁ {!!} {!!}
  where
    CC×CC = (C ×C C) op ×C (C ×C C)
    
    dayEnd : (F G : Functor C Set') → (c : Obj C) → CoEnd (dayF F G c)
    dayEnd F G c = setCoEnd ℓSet (dayF F G c) -- (ℓSet ⊔ ℓC₀ ⊔ ℓC₁)
    
    day₀ : Obj ([ C , Set' ] ×C [ C , Set' ]) → Obj [ C , Set' ]
    day₀ (F , G) = functor d0₀ d0₁ d0-id d0-compose
      where
        d0₀ : Obj C → Obj Set'
        d0₀ c = CoEnd.co-∫ (dayEnd F G c)
        
        d0₁ : {a b : Obj C} → Hom C a b → Hom Set' (Set-co-∫ ℓSet (dayF F G a)) (Set-co-∫ ℓSet (dayF F G b))
        d0₁ {a} {b} f = coendMorph (convolutionTransformation F G f)
        
        d0-id : {a : Obj C} → d0₁ {a} {a} (id C) ≡ id Set'
        d0-id {a} = begin
          coendMorph (convolutionTransformation F G (id C))
            ≡⟨ cong (λ X → coendMorph X) (convolution-transformation-id F G a) ⟩
          coendMorph Id⟨ dayF F G a ⟩
            ≡⟨⟩
          proj₁ (CoEnd.co-universal (setCoEnd ℓSet (dayF F G a)) (cowedgeTransform Id⟨ dayF F G a ⟩ (CoEnd.co-e (setCoEnd ℓSet (dayF F G a)))))
          -- The mapping to the end is unique, therefore it has to be equal to the identity in this case. 
            ≡⟨ sym ((proj₁ (proj₂ (CoEnd.co-universal (setCoEnd ℓSet (dayF F G a)) (cowedgeTransform Id⟨ dayF F G a ⟩ (CoEnd.co-e (setCoEnd ℓSet (dayF F G a))))) )) (λ x → x)) ⟩
          (λ x → x) ∎
        
        d0-compose : {a b c : Obj C} {f : Hom C a b} {g : Hom C b c} → d0₁ (g ∘C f) ≡ d0₁ g ∘F d0₁ f
        d0-compose {a} {b} {c} {f} {g} = begin
          coendMorph (convolutionTransformation F G (g ∘C f))
            ≡⟨ {!!} ⟩
          coendMorph (convolutionTransformation F G g) ∘F coendMorph (convolutionTransformation F G f) ∎
    
    day₁ : {a b : Obj ([ C , Set' ] ×C [ C , Set' ])} → Hom ([ C , Set' ] ×C [ C , Set' ]) a b → Hom [ C , Set' ] (day₀ a) (day₀ b)
    day₁ (α , β) = naturalTransformation {!!} {!!}
    
