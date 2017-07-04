
open import Level
open import Function renaming ( _∘_ to _∘F_ ; id to idF )

open import Data.Unit
open import Data.Product

open import Relation.Binary.PropositionalEquality hiding ( [_] )
open ≡-Reasoning

open import Extensionality

open import Haskell hiding ( Hask )
open import Haskell.Functor hiding ( functor ) renaming ( Functor to HaskellFunctor )
open import Haskell.Applicative

open import Theory.Category.Definition
open import Theory.Category.Examples
open import Theory.Category.Monoidal
open import Theory.Category.Monoidal.Examples.Unit
open import Theory.Category.Monoidal.Examples.SetCat
open import Theory.Category.Monoidal.Examples.FunctorWithDayConvolution
open import Theory.Functor.Definition hiding ( functor )
open import Theory.Functor.Composition
open import Theory.Functor.Monoidal
open import Theory.Functor.Properties.IsomorphicHaskellFunctor
open import Theory.Functor.Examples.HomFunctor
open import Theory.Natural.Transformation
open import Theory.End.Definition
open import Theory.End.Convolution renaming ( convolutionTransObj to convolutionTransObj' )
open import Theory.End.Properties

module Theory.Functor.Monoidal.Properties.ToMonoidalFunctorIntoDayFunctorCategory where

-- open Category hiding ( Obj ; Hom )
open MonoidalCategory hiding ( id )

LaxMonoidalFunctor→MonoidalFunctorIntoDayFunctorCategory
  : {ℓC₀ ℓC₁ : Level}
  → (ℓSet : Level)
  → {C : Category {ℓC₀} {ℓC₁}}
  → {CMon : MonoidalCategory C}
  → (FMon : LaxMonoidalFunctor CMon (setMonoidalCategory {ℓSet ⊔ ℓC₀ ⊔ ℓC₁}))
  → LaxMonoidalFunctor ⊤-MonCat (functorDayMonoidalCategory ℓSet CMon)
LaxMonoidalFunctor→MonoidalFunctorIntoDayFunctorCategory {ℓC₀} {ℓC₁} ℓSet {C} {CMon} FMon 
  = laxMonoidalFunctor comp ε' μ-nat-trans {!!} {!!} {!!}
  where
    Hask = setCategory {ℓSet ⊔ ℓC₀ ⊔ ℓC₁}
    HaskMon = setMonoidalCategory {ℓSet ⊔ ℓC₀ ⊔ ℓC₁}
    [C,Hask]Mon = functorDayMonoidalCategory ℓSet CMon
    
    open LaxMonoidalFunctor FMon
    open Category
    open Functor hiding ( id )

    _∘⊤_ = _∘_ ⊤-Cat
    _∘C_ = λ {a b c} → _∘_ C {a} {b} {c}

    dayF = convolutionFunctor {ℓSet = ℓSet} CMon
    convolutionTransObj = convolutionTransObj' {ℓSet = ℓSet} CMon
    
    comp : Functor ⊤-Cat [ C , Hask ]
    comp = Functor.functor comp₀ comp₁ comp-id comp-compose
      where
        comp₀ : Obj ⊤-Cat → Functor C Hask
        comp₀ tt = F
        
        comp₁ : {a b : Obj ⊤-Cat} → Hom ⊤-Cat a b → Hom [ C , Hask ] (comp₀ a) (comp₀ b)
        comp₁ {tt} {tt} tt = Id⟨ comp₀ tt ⟩
        
        abstract
          comp-id : {a : Obj ⊤-Cat} → comp₁ (id ⊤-Cat) ≡ id [ C , Hask ]
          comp-id {tt} = refl
        
        abstract
          comp-compose : {a b c : Obj ⊤-Cat} {f : Hom ⊤-Cat a b} {g : Hom ⊤-Cat b c}
                       → comp₁ (g ∘⊤ f) ≡ ⟨ comp₁ g ⟩∘ᵥ⟨ comp₁ f ⟩
          comp-compose {tt} {tt} {tt} {tt} {tt} = sym (Category.left-id [ C , Hask ])
    
    ε' : MonoidalCategory.Hom [C,Hask]Mon (unit [C,Hask]Mon) (Functor.F₀ comp (unit ⊤-MonCat))
    ε' = naturalTransformation η (λ {a b} {f} → nat {a} {b} {f})
      where
        η : (x : Obj C) → Hom Hask (Lift {ℓ = ℓSet ⊔ ℓC₀} (Hom C (MonoidalCategory.unit CMon) x)) ([ F ]₀ x) -- homFunctor ℓSet (MonoidalCategory.unit CMon) = unit [C,Hask]Mon
        η x (lift f) = [ F ]₁ f (ε (lift tt))
        
        abstract
          nat : {a b : Obj C} {f : Hom C a b} → [ F ]₁ f ∘F η a ≡ η b ∘F (λ (g : Lift (Hom C (MonoidalCategory.unit CMon) a)) → lift (f ∘C lower g))
          nat {a} {b} {f} = fun-ext $ λ (g : Lift (Hom C (unit CMon) a)) → begin
            ([ F ]₁ f ∘F η a) g
              ≡⟨⟩
            ([ F ]₁ f ∘F [ F ]₁ (lower g)) (ε (lift tt))
              ≡⟨ cong (λ X → X (ε (lift tt))) (sym $ Functor.compose F) ⟩
            [ F ]₁ (f ∘C lower g) (ε (lift tt))
              ≡⟨⟩
            (η b ∘F (λ g → lift (f ∘C lower g))) g ∎
    
    μ-nat-trans : NaturalTransformation [ tensor [C,Hask]Mon ]∘[ [ comp ]×[ comp ] ] [ comp ]∘[ tensor ⊤-MonCat ]
    μ-nat-trans = naturalTransformation μ-η (λ {a b} {f} → μ-nat {a} {b} {f})
      where
        μ-η : (x : Obj (⊤-Cat ×C ⊤-Cat)) → Hom [ C , Hask ] ([ [ tensor [C,Hask]Mon ]∘[ [ comp ]×[ comp ] ] ]₀ x) ([ [ comp ]∘[ tensor ⊤-MonCat ] ]₀ x)
        μ-η (tt , tt) = naturalTransformation μ-η-η (λ {a b} {f} → μ-η-nat {a} {b} {f})
          where
            μ-η-η : (x : Obj C) → Hom Hask (Set-co-∫ ℓSet (dayF F F x)) ([ F ]₀ x)
            μ-η-η c co-∫ = {!!}
            
            abstract
              μ-η-nat : {a b : Obj C} {f : Hom C a b} 
                      → [ F ]₁ f ∘F μ-η-η a
                      ≡ μ-η-η b ∘F coendMorph (convolutionTransObj F F f)
              μ-η-nat {a} {b} {f} = {!!}
            
        abstract
          μ-nat : {a b : Obj (⊤-Cat ×C ⊤-Cat)} {f : Hom (⊤-Cat ×C ⊤-Cat) a b} 
                → ⟨ Id⟨ F ⟩ ⟩∘ᵥ⟨ μ-η a ⟩
                ≡ ⟨ μ-η b ⟩∘ᵥ⟨ [ tensor [C,Hask]Mon ]₁ (Id⟨ F ⟩ , Id⟨ F ⟩) ⟩
          μ-nat {a} {b} {f} = begin
            ⟨ Id⟨ F ⟩ ⟩∘ᵥ⟨ μ-η a ⟩
              ≡⟨ Category.right-id [ C , Hask ] ⟩
            μ-η a
              ≡⟨ {!!} ⟩
            μ-η b
              ≡⟨ sym (Category.left-id [ C , Hask ]) ⟩
            ⟨ μ-η b ⟩∘ᵥ⟨ Id⟨ [ tensor [C,Hask]Mon ]₀ (F , F) ⟩ ⟩
              ≡⟨ cong (λ X → ⟨ μ-η b ⟩∘ᵥ⟨ X ⟩) (sym (Functor.id (tensor [C,Hask]Mon))) ⟩
            ⟨ μ-η b ⟩∘ᵥ⟨ [ tensor [C,Hask]Mon ]₁ (Id⟨ F ⟩ , Id⟨ F ⟩) ⟩ ∎
