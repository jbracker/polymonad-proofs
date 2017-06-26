
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
open import Theory.End.Convolution renaming 
  ( convolutionTransObj to convolutionTransObj' 
  ; convolutionTransFun to convolutionTransFun'
  ; convolutionTransformation to convolutionTransformation'
  ; convolution-trans-obj-id to convolution-trans-obj-id' )
open import Theory.End.Properties renaming 
  ( coendMorph to coendMorph'
  ; coend-morph-unique to coend-morph-unique' )

module Theory.End.DayConvolution  where

open Category
open Functor
open NaturalTransformation renaming ( η to nat-η )

dayConvolution : {ℓC₀ ℓC₁ ℓSet : Level} {C : Category {ℓC₀} {ℓC₁}} (CMon : MonoidalCategory C) 
               → Functor ([ C , setCategory {ℓSet ⊔ ℓC₁ ⊔ ℓC₀} ] ×C [ C , setCategory {ℓSet ⊔ ℓC₁ ⊔ ℓC₀} ]) [ C , setCategory {ℓSet ⊔ ℓC₁ ⊔ ℓC₀} ]
dayConvolution {ℓC₀} {ℓC₁} {ℓSet} {C} CMon = functor day₀ day₁ (λ {a} → day-id {a}) (λ {a b c} {f} {g} → day-compose {a} {b} {c} {f} {g})
  where
    Set' = setCategory {ℓSet ⊔ ℓC₁ ⊔ ℓC₀}
    
    [C,S]×[C,S] = [ C , Set' ] ×C [ C , Set' ]
    CC×CC = (C ×C C) op ×C (C ×C C)

    _⊗C₀_ = MonoidalCategory._⊗₀_ CMon
    _⊗C₁_ = MonoidalCategory._⊗₁_ CMon
    _∘C_ = _∘_ C
    _∘[C,S]_ = _∘_ ([ C , Set' ])
    _∘[C,S]×[C,S]_ = _∘_ [C,S]×[C,S]
    
    dayF = convolutionFunctor {ℓSet = ℓSet} CMon
    convolutionTransObj = convolutionTransObj' {ℓSet = ℓSet} CMon
    convolutionTransFun = convolutionTransFun' {ℓSet = ℓSet} CMon
    convolutionTransformation = convolutionTransformation' {ℓSet = ℓSet} CMon

    convolution-trans-obj-id = convolution-trans-obj-id' {ℓSet = ℓSet} CMon

    coendMorph = coendMorph' {ℓS = ℓSet} {C = C ×C C}
    coend-morph-unique = coend-morph-unique' {ℓS = ℓSet} {C = C ×C C}
    
    dayEnd : (F G : Functor C Set') → (c : Obj C) → CoEnd (dayF F G c)
    dayEnd F G c = setCoEnd ℓSet (dayF F G c) -- (ℓSet ⊔ ℓC₀ ⊔ ℓC₁)
    
    day₀ : Obj [C,S]×[C,S] → Obj [ C , Set' ]
    day₀ (F , G) = functor d0₀ d0₁ (λ {a} → d0-id {a}) (λ {a b c} {f} {g} → d0-compose {a} {b} {c} {f} {g})
      where
        d0₀ : Obj C → Obj Set'
        d0₀ c = CoEnd.co-∫ (dayEnd F G c)
        
        d0₁ : {a b : Obj C} → Hom C a b → Hom Set' (Set-co-∫ ℓSet (dayF F G a)) (Set-co-∫ ℓSet (dayF F G b))
        d0₁ {a} {b} f = coendMorph (convolutionTransObj F G f)

        abstract
          d0-id : {a : Obj C} → d0₁ {a} {a} (id C) ≡ id Set'
          d0-id {a} = begin
            coendMorph (convolutionTransObj F G (id C))
              ≡⟨ cong (λ X → coendMorph X) (convolution-trans-obj-id F G a) ⟩
            coendMorph Id⟨ dayF F G a ⟩
              ≡⟨ sym (coend-morph-unique (Id⟨ dayF F G a ⟩) (λ x → x)) ⟩
            (λ x → x) ∎
        
          d0-compose : {a b c : Obj C} {f : Hom C a b} {g : Hom C b c} → d0₁ (g ∘C f) ≡ d0₁ g ∘F d0₁ f
          d0-compose {a} {b} {c} {f} {g} = begin
            coendMorph (convolutionTransObj F G (g ∘C f))
              ≡⟨ sym (coend-morph-unique (convolutionTransObj F G (g ∘C f)) (coendMorph (convolutionTransObj F G g) ∘F coendMorph (convolutionTransObj F G f))) ⟩
            coendMorph (convolutionTransObj F G g) ∘F coendMorph (convolutionTransObj F G f) ∎
        
    day₁ : {a b : Obj [C,S]×[C,S]} → Hom [C,S]×[C,S] a b → Hom [ C , Set' ] (day₀ a) (day₀ b)
    day₁ {F , G} {F' , G'} (α , β) = naturalTransformation day-η (λ {x y} {f} → day-nat {x} {y} {f}) 
      where
        --      (x : Obj C) → Hom Set' ([ day₀ a ]₀ x) ([ day₀ b ]₀ x)
        day-η : (x : Obj C) → Hom Set' (CoEnd.co-∫ (dayEnd F G x)) (CoEnd.co-∫ (dayEnd F' G' x))
        day-η x = coendMorph (convolutionTransFun α β x)

        abstract
          day-nat : {x y : Obj C} {f : Hom C x y} → [ day₀ (F' , G') ]₁ f ∘F day-η x ≡ day-η y ∘F [ day₀ (F , G) ]₁ f
          day-nat {x} {y} {f} = begin
            [ day₀ (F' , G') ]₁ f ∘F day-η x 
              ≡⟨⟩
            coendMorph (convolutionTransObj F' G' f) ∘F coendMorph (convolutionTransFun α β x)
              ≡⟨ coend-morph-unique (convolutionTransformation α β f) (coendMorph (convolutionTransObj F' G' f) ∘F coendMorph (convolutionTransFun α β x)) ⟩ 
            coendMorph (convolutionTransformation α β f)
              ≡⟨ sym (coend-morph-unique (convolutionTransformation α β f) (coendMorph (convolutionTransFun α β y) ∘F coendMorph (convolutionTransObj F G f))) ⟩ 
            coendMorph (convolutionTransFun α β y) ∘F coendMorph (convolutionTransObj F G f)
              ≡⟨⟩
            day-η y ∘F [ day₀ (F , G) ]₁ f ∎

    abstract
      day-id : {a : Obj [C,S]×[C,S]} → day₁ {a} {a} (id [C,S]×[C,S] {a}) ≡ id [ C , Set' ] {day₀ a}
      day-id {F , G} = natural-transformation-eq $ fun-ext $ λ (c : Obj C) → begin
        coendMorph (convolutionTransFun Id⟨ F ⟩ Id⟨ G ⟩ c)
          ≡⟨ sym (coend-morph-unique (convolutionTransFun Id⟨ F ⟩ Id⟨ G ⟩ c) (λ x → x)) ⟩
        (λ x → x) ∎

    abstract
      day-compose : {a b c : Obj [C,S]×[C,S]}
                  → {f : Hom [C,S]×[C,S] a b} {g : Hom [C,S]×[C,S] b c}
                  → day₁ {a} {c} (g ∘[C,S]×[C,S] f) ≡ day₁ {b} {c} g ∘[C,S] day₁ {a} {b} f
      day-compose {F , G} {F' , G'} {F'' , G''} {α , β} {γ , δ} = natural-transformation-eq $ fun-ext $ λ (c : Obj C) → begin
        nat-η (day₁ {F , G} {F'' , G''} ((γ , δ) ∘[C,S]×[C,S] (α , β))) c
          ≡⟨⟩
        coendMorph (convolutionTransFun ⟨ γ ⟩∘ᵥ⟨ α ⟩ ⟨ δ ⟩∘ᵥ⟨ β ⟩ c)
          ≡⟨ sym (coend-morph-unique (convolutionTransFun ⟨ γ ⟩∘ᵥ⟨ α ⟩ ⟨ δ ⟩∘ᵥ⟨ β ⟩ c) (coendMorph (convolutionTransFun γ δ c) ∘F coendMorph (convolutionTransFun α β c))) ⟩
        coendMorph (convolutionTransFun γ δ c) ∘F coendMorph (convolutionTransFun α β c)
          ≡⟨⟩
        nat-η (day₁ {F' , G'} {F'' , G''} (γ , δ) ∘[C,S] day₁ {F , G} {F' , G'} (α , β)) c ∎
      
