
open import Level
open import Function hiding ( id ) renaming ( _∘_ to _∘F_ )

open import Data.Product

open import Relation.Binary.PropositionalEquality hiding ( [_] )
open ≡-Reasoning

open import Theory.Triple renaming ( _,_,_ to _,'_,'_ )
open import Theory.Category.Definition
open import Theory.Category.Monoidal
open import Theory.Category.Isomorphism
open import Theory.Category.Examples.Functor renaming ( functorCategory to FunCat )
open import Theory.Category.Examples.SetCat renaming ( setCategory to SetCat )
open import Theory.Functor.Definition
open import Theory.Functor.Composition
open import Theory.Functor.Association
open Theory.Functor.Association.Associator
open import Theory.Functor.Application
open import Theory.Natural.Transformation
open import Theory.Natural.Transformation.Properties

open import Theory.End.Definition
open import Theory.End.Convolution
open import Theory.End.DayConvolution
open import Theory.End.Properties
open import Theory.End.Wedge

open import Extensionality
open import Bijection

module Theory.Natural.Transformation.Examples.DayConvolutionAssociator where

open Category 
open Functor hiding ( id )

p : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}} → Functor C D → Functor (C ×C C) D
p {C = C} {D} F = functor (λ {(c⁻ , c⁺) → F₀ F c⁺}) (λ {(f⁻ , f⁺) → F₁ F f⁺}) (Functor.id F) (λ {a b c} {f} {g} → compose F {proj₂ a} {proj₂ b} {proj₂ c} {proj₂ f} {proj₂ g})

postulate 
  day-end-eq : {ℓC₀ ℓC₁ : Level} → (ℓSet : Level) → {C : Category {ℓC₀} {ℓC₁}} → (CMon : MonoidalCategory C) 
             → (F G H : Functor C (SetCat {ℓSet ⊔ ℓC₀ ⊔ ℓC₁})) → (c c₀⁻ c₁⁻ c₀⁺ c₁⁺ : Obj C)
             → (Hom C (MonoidalCategory._⊗₀_ CMon c₀⁻ c₁⁻) c × (Set-co-∫ ℓSet (convolutionFunctor {ℓSet = ℓSet} CMon F G c₀⁺) × F₀ H c₁⁺)) 
             ↔ (Hom C (MonoidalCategory._⊗₀_ CMon c₀⁻ c₁⁻) c × (F₀ F c₀⁺ × Set-co-∫ ℓSet (convolutionFunctor {ℓSet = ℓSet} CMon G H c₁⁺)))

abstract
  q : {ℓC₀ ℓC₁ : Level} → (ℓSet : Level) → {C : Category {ℓC₀} {ℓC₁}} → (CMon : MonoidalCategory C) 
    → (F G H : Functor C (SetCat {ℓSet ⊔ ℓC₀ ⊔ ℓC₁})) → (c : Obj C)
    → convolutionFunctor {ℓSet = ℓSet} CMon (F₀ (dayConvolution {ℓC₀} {ℓC₁} {ℓSet} CMon) (F , G)) H c ≡ convolutionFunctor {ℓSet = ℓSet} CMon F (F₀ (dayConvolution {ℓC₀} {ℓC₁} {ℓSet} CMon) (G , H)) c
  q {ℓC₀} {ℓC₁} ℓSet {C} CMon F G H c = functor-eq eq1 {!!}
    where
      _⊗C₀_ = MonoidalCategory._⊗₀_ CMon
      
      abstract
        eq1 : F₀ (convolutionFunctor {ℓSet = ℓSet} CMon (F₀ (dayConvolution {ℓC₀} {ℓC₁} {ℓSet} CMon) (F , G)) H c) 
            ≡ F₀ (convolutionFunctor {ℓSet = ℓSet} CMon F (F₀ (dayConvolution {ℓC₀} {ℓC₁} {ℓSet} CMon) (G , H)) c)
        eq1 = fun-ext (λ {((c₀⁻ , c₁⁻) , (c₀⁺ , c₁⁺)) → begin 
          F₀ (convolutionFunctor {ℓSet = ℓSet} CMon (F₀ (dayConvolution CMon) (F , G)) H c) ((c₀⁻ , c₁⁻) , (c₀⁺ , c₁⁺))
            ≡⟨⟩
          (Hom C (c₀⁻ ⊗C₀ c₁⁻) c × (F₀ (F₀ (dayConvolution CMon) (F , G)) c₀⁺ × F₀ H c₁⁺))
            ≡⟨⟩
          (Hom C (c₀⁻ ⊗C₀ c₁⁻) c × (Set-co-∫ ℓSet (convolutionFunctor {ℓSet = ℓSet} CMon F G c₀⁺) × F₀ H c₁⁺))
            ≡⟨ {!Bijection.f (day-end-eq ℓSet CMon F G H c c₀⁻ c₁⁻ c₀⁺ c₁⁺)!} ⟩
          (Hom C (c₀⁻ ⊗C₀ c₁⁻) c × (F₀ F c₀⁺ × Set-co-∫ ℓSet (convolutionFunctor {ℓSet = ℓSet} CMon G H c₁⁺)))
            ≡⟨⟩
          (Hom C (c₀⁻ ⊗C₀ c₁⁻) c × (F₀ F c₀⁺ × F₀ (F₀ (dayConvolution CMon) (G , H)) c₁⁺))
            ≡⟨⟩
          F₀ (convolutionFunctor {ℓSet = ℓSet} CMon F (F₀ (dayConvolution CMon) (G , H)) c) ((c₀⁻ , c₁⁻) , (c₀⁺ , c₁⁺)) ∎})

q' : {ℓC₀ ℓC₁ : Level} → (ℓSet : Level) → {C : Category {ℓC₀} {ℓC₁}} → (CMon : MonoidalCategory C) 
   → (F G H : Functor C (SetCat {ℓSet ⊔ ℓC₀ ⊔ ℓC₁})) → (c₀⁺ c₁⁺ : Obj C)
   → (F₀ (F₀ (dayConvolution {ℓSet = ℓSet} CMon) (F , G)) c₀⁺ × F₀ H c₁⁺) 
   → (F₀ F c₀⁺ × F₀ (F₀ (dayConvolution {ℓSet = ℓSet} CMon) (G , H)) c₁⁺)
q' {ℓC₀} {ℓC₁} ℓSet {C} CMon F G H c₀⁺ c₁⁺ (co-∫ , Hc) = {!!} , {!!}

dayAssociator : {ℓC₀ ℓC₁ : Level} → (ℓSet : Level) → {C : Category {ℓC₀} {ℓC₁}} → (CMon : MonoidalCategory C)
              → NaturalTransformation (leftAssociator {C = FunCat C (SetCat {ℓSet ⊔ ℓC₀ ⊔ ℓC₁})} (dayConvolution {ℓC₀} {ℓC₁} {ℓSet} CMon)) 
                                      (rightAssociator {C = FunCat C (SetCat {ℓSet ⊔ ℓC₀ ⊔ ℓC₁})} (dayConvolution {ℓC₀} {ℓC₁} {ℓSet} CMon))
dayAssociator {ℓC₀} {ℓC₁} ℓSet {C} CMon = naturalTransformation {!!} {!!}
  where
    dayConv = dayConvolution {ℓC₀} {ℓC₁} {ℓSet} CMon
    
    Set' = SetCat {ℓSet ⊔ ℓC₀ ⊔ ℓC₁}
    [C,S] = FunCat C Set'
    
    lAssoc = leftAssociator {C = [C,S]} dayConv
    rAssoc = rightAssociator {C = [C,S]} dayConv

    dayF = convolutionFunctor {ℓSet = ℓSet} CMon
    
    η : (x : Obj ([C,S] ×C [C,S] ×C [C,S])) → Hom [C,S] (F₀ lAssoc x) (F₀ rAssoc x)
    η (F ,' G ,' H) = naturalTransformation {!!} {!!}
      where        
        η-assoc : (c : Obj C) → Hom Set' (Set-co-∫ ℓSet (dayF (F₀ dayConv (F , G)) H c)) (Set-co-∫ ℓSet (dayF F (F₀ dayConv (G , H)) c))
        η-assoc c = coendMorph (naturalTransformation η-trans {!!}) -- NaturalTransformation (dayF (F₀ dayConv (F , G)) H c) (dayF F (F₀ dayConv (G , H)) c)
          where 
            η-trans : (c' : Obj ((C ×C C) op ×C (C ×C C))) → Hom SetCat (F₀ (dayF (F₀ dayConv (F , G)) H c) c') (F₀ (dayF F (F₀ dayConv (G , H)) c) c')
            η-trans ((c₀⁻ , c₁⁻) , (c₀⁺ , c₁⁺)) = Bijection.f (day-end-eq ℓSet CMon F G H c c₀⁻ c₁⁻ c₀⁺ c₁⁺)
-- ((c₁ , c₁') , (c₂ , c₂')) = Hom C (c₁ ⊗C₀ c₁') c × F₀ c₂ × G₀ c₂'
