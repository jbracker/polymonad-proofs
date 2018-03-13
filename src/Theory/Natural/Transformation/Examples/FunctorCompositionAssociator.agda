
open import Level
open import Function hiding ( id ) renaming ( _∘_ to _∘F_ )

open import Data.Product

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Extensionality

open import Theory.Triple renaming ( _,_,_ to _,'_,'_ )
open import Theory.Category.Definition
open import Theory.Category.Examples.Functor
open import Theory.Functor.Definition
open import Theory.Functor.Composition
open import Theory.Functor.Association
open import Theory.Functor.Examples.CompositionFunctor
open import Theory.Natural.Transformation

module Theory.Natural.Transformation.Examples.FunctorCompositionAssociator where

open Category
open NaturalTransformation renaming ( η to nat-η )
open Theory.Functor.Association.Associator

functorCompositionAssociator : {ℓC₀ ℓC₁ : Level} (C : Category {ℓC₀} {ℓC₁}) → NaturalTransformation (leftAssociator (compositionFunctor C C C)) (rightAssociator (compositionFunctor C C C))
functorCompositionAssociator C = naturalTransformation nat-assoc-η (λ {a b} {f} → nat-assoc-nat {a} {b} {f})
  where
    Fun = functorCategory C C
    comp = compositionFunctor C C C
    _∘C_ = _∘_ C
    lAssoc = leftAssociator comp
    rAssoc = rightAssociator comp
    
    nat-assoc-η : (c : Obj (Fun ×C Fun ×C Fun)) → Hom Fun ([ lAssoc ]₀ c) ([ rAssoc ]₀ c)
    nat-assoc-η (F ,' G ,' H) = naturalTransformation η nat
      where
        η : (c : Obj C) → Hom C ([ [ lAssoc ]₀ (F ,' G ,' H) ]₀ c) ([ [ rAssoc ]₀ (F ,' G ,' H) ]₀ c)
        η c = id C {[ F ]₀ ([ G ]₀ ([ H ]₀ c))}
        
        abstract
          nat : {a b : Obj C} {f : Hom C a b} → [ [ lAssoc ]₀ (F ,' G ,' H) ]₁ f ∘C η a ≡ η b ∘C [ [ rAssoc ]₀ (F ,' G ,' H) ]₁ f
          nat {a} {b} {f} = trans (left-id C) (sym (right-id C))
    
    abstract
      nat-assoc-nat : {a b : Obj (Fun ×C Fun ×C Fun)} → {f : Hom ((Fun ×C Fun ×C Fun)) a b} → ⟨ [ rAssoc ]₁ f ⟩∘ᵥ⟨ nat-assoc-η a ⟩ ≡ ⟨ nat-assoc-η b ⟩∘ᵥ⟨ [ lAssoc ]₁ f ⟩
      nat-assoc-nat {F ,' G ,' H} {F' ,' G' ,' H'} {α ,' β ,' γ} = natural-transformation-eq $ fun-ext $ λ (c : Obj C) → begin
        nat-η ⟨ [ rAssoc ]₁ f ⟩∘ᵥ⟨ nat-assoc-η a ⟩ c 
          ≡⟨⟩
        nat-η ([ rAssoc ]₁ f) c ∘C nat-η (nat-assoc-η a) c 
          ≡⟨ left-id C ⟩
        nat-η α ([ G' ]₀ ([ H' ]₀ c)) ∘C [ F ]₁ (nat-η β ([ H' ]₀ c) ∘C [ G ]₁ (nat-η γ c))
          ≡⟨ cong (λ X → nat-η α ([ G' ]₀ ([ H' ]₀ c)) ∘C X) (Functor.compose F) ⟩
        nat-η α ([ G' ]₀ ([ H' ]₀ c)) ∘C ([ F ]₁ (nat-η β ([ H' ]₀ c)) ∘C [ F ]₁ ([ G ]₁ (nat-η γ c)))
          ≡⟨ assoc C ⟩
        (nat-η α ([ G' ]₀ ([ H' ]₀ c)) ∘C [ F ]₁ (nat-η β ([ H' ]₀ c))) ∘C [ F ]₁ ([ G ]₁ (nat-η γ c))
          ≡⟨ sym (right-id C) ⟩
        nat-η (nat-assoc-η b) c ∘C nat-η ([ lAssoc ]₁ f) c
          ≡⟨⟩
        nat-η ⟨ nat-assoc-η b ⟩∘ᵥ⟨ [ lAssoc ]₁ f ⟩ c ∎
        where 
          f = α ,' β ,' γ
          a = F ,' G ,' H
          b = F' ,' G' ,' H'

functorCompositionAssociator' : {ℓC₀ ℓC₁ : Level} (C : Category {ℓC₀} {ℓC₁}) → NaturalTransformation (rightAssociator (compositionFunctor C C C)) (leftAssociator (compositionFunctor C C C))
functorCompositionAssociator' C = naturalTransformation nat-assoc-η (λ {a b} {f} → nat-assoc-nat {a} {b} {f})
  where
    Fun = functorCategory C C
    comp = compositionFunctor C C C
    _∘C_ = _∘_ C
    lAssoc = leftAssociator comp
    rAssoc = rightAssociator comp
    
    nat-assoc-η : (c : Obj (Fun ×C Fun ×C Fun)) → Hom Fun ([ rAssoc ]₀ c) ([ lAssoc ]₀ c)
    nat-assoc-η (F ,' G ,' H) = naturalTransformation η nat
      where
        η : (c : Obj C) → Hom C ([ [ rAssoc ]₀ (F ,' G ,' H) ]₀ c) ([ [ lAssoc ]₀ (F ,' G ,' H) ]₀ c)
        η c = id C {[ F ]₀ ([ G ]₀ ([ H ]₀ c))}
        
        abstract
          nat : {a b : Obj C} {f : Hom C a b} → [ [ rAssoc ]₀ (F ,' G ,' H) ]₁ f ∘C η a ≡ η b ∘C [ [ lAssoc ]₀ (F ,' G ,' H) ]₁ f
          nat {a} {b} {f} = trans (left-id C) (sym (right-id C))
    
    abstract
      nat-assoc-nat : {a b : Obj (Fun ×C Fun ×C Fun)} → {f : Hom ((Fun ×C Fun ×C Fun)) a b} → ⟨ [ lAssoc ]₁ f ⟩∘ᵥ⟨ nat-assoc-η a ⟩ ≡ ⟨ nat-assoc-η b ⟩∘ᵥ⟨ [ rAssoc ]₁ f ⟩
      nat-assoc-nat {F ,' G ,' H} {F' ,' G' ,' H'} {α ,' β ,' γ} = natural-transformation-eq $ fun-ext $ λ (c : Obj C) → begin
        nat-η ⟨ [ lAssoc ]₁ f ⟩∘ᵥ⟨ nat-assoc-η a ⟩ c 
          ≡⟨⟩
        nat-η ([ lAssoc ]₁ f) c ∘C nat-η (nat-assoc-η a) c 
          ≡⟨ left-id C ⟩
        (nat-η α ([ G' ]₀ ([ H' ]₀ c)) ∘C [ F ]₁ (nat-η β ([ H' ]₀ c))) ∘C [ F ]₁ ([ G ]₁ (nat-η γ c))
          ≡⟨ sym (assoc C) ⟩
        nat-η α ([ G' ]₀ ([ H' ]₀ c)) ∘C ([ F ]₁ (nat-η β ([ H' ]₀ c)) ∘C [ F ]₁ ([ G ]₁ (nat-η γ c)))
          ≡⟨ cong (λ X → nat-η α ([ G' ]₀ ([ H' ]₀ c)) ∘C X) (sym $ Functor.compose F) ⟩
        nat-η α ([ G' ]₀ ([ H' ]₀ c)) ∘C [ F ]₁ (nat-η β ([ H' ]₀ c) ∘C [ G ]₁ (nat-η γ c))
          ≡⟨ sym (right-id C) ⟩
        nat-η (nat-assoc-η b) c ∘C nat-η ([ rAssoc ]₁ f) c
          ≡⟨⟩
        nat-η ⟨ nat-assoc-η b ⟩∘ᵥ⟨ [ rAssoc ]₁ f ⟩ c ∎
        where 
          f = α ,' β ,' γ
          a = F ,' G ,' H
          b = F' ,' G' ,' H'
