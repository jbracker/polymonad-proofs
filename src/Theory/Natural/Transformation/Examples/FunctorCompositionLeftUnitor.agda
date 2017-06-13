
open import Level
open import Function hiding ( id )

open import Data.Product

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Extensionality

open import Theory.Category.Definition
open import Theory.Category.Isomorphism
open import Theory.Category.Examples using ( functorCategory )
open import Theory.Functor.Definition
open import Theory.Functor.Composition
open import Theory.Functor.Application
open import Theory.Functor.Examples.CompositionFunctor
open import Theory.Natural.Transformation
open import Theory.Natural.Isomorphism

module Theory.Natural.Transformation.Examples.FunctorCompositionLeftUnitor where

open Category
open NaturalTransformation renaming ( η to nat-η )
open Theory.Functor.Application.BiFunctor

functorCompositionLeftUnitor : {ℓC₀ ℓC₁ : Level} (C : Category {ℓC₀} {ℓC₁}) → NaturalTransformation ([ Id[ C ] ,-] (compositionFunctor C C C)) Id[ functorCategory C C ]
functorCompositionLeftUnitor C = naturalTransformation η (λ {a b} {f} → natural' {a} {b} {f})
  where
    Fun = functorCategory C C
    comp = compositionFunctor C C C
    _∘C_ = Category._∘_ C
    
    η : (F : Functor C C) → Hom Fun ([ [ Id[ C ] ,-] comp ]₀ F) ([ Id[ Fun ] ]₀ F)
    η (functor F₀ F₁ F-id F-compose) = naturalTransformation η' (trans (left-id C) (sym (right-id C)))
      where
        F = functor F₀ F₁ F-id F-compose
            
        η' : (c : Obj C) → Hom C ([ [ [ Id[ C ] ,-] comp ]₀ F ]₀ c) ([ [ Id[ Fun ] ]₀ F ]₀ c)
        η' c = id C {F₀ c}
         
    natural' : {a b : Functor C C} {f : Hom Fun a b} → ⟨ [ Id[ Fun ] ]₁ f ⟩∘ᵥ⟨ η a ⟩ ≡ ⟨ η b ⟩∘ᵥ⟨ [ [ Id[ C ] ,-] comp ]₁ f ⟩
    natural' {F} {G} {α} = natural-transformation-eq $ fun-ext $ λ (c : Obj C) → begin
      nat-η  ⟨ [ Id[ Fun ] ]₁ α ⟩∘ᵥ⟨ η F ⟩ c 
        ≡⟨⟩
      nat-η ([ Id[ Fun ] ]₁ α) c ∘C id C
        ≡⟨ left-id C ⟩
      nat-η ([ Id[ Fun ] ]₁ α) c
        ≡⟨⟩
      nat-η α c
        ≡⟨ sym (right-id C) ⟩
      id C ∘C nat-η α c
        ≡⟨⟩
      nat-η ([ [ Id[ C ] ,-] comp ]₁ α) c
        ≡⟨ sym (right-id C) ⟩
      id C ∘C nat-η ([ [ Id[ C ] ,-] comp ]₁ α) c
        ≡⟨⟩
      nat-η ⟨ η G ⟩∘ᵥ⟨ [ [ Id[ C ] ,-] comp ]₁ α ⟩ c ∎

functorCompositionLeftUnitor' : {ℓC₀ ℓC₁ : Level} (C : Category {ℓC₀} {ℓC₁}) → NaturalTransformation Id[ functorCategory C C ] ([ Id[ C ] ,-] (compositionFunctor C C C))
functorCompositionLeftUnitor' C = naturalTransformation η (λ {a b} {f} → natural' {a} {b} {f})
  where
    Fun = functorCategory C C
    comp = compositionFunctor C C C
    _∘C_ = Category._∘_ C
    
    η : (F : Functor C C) → Hom Fun ([ Id[ Fun ] ]₀ F) ([ [ Id[ C ] ,-] comp ]₀ F)
    η (functor F₀ F₁ F-id F-compose) = naturalTransformation η' (trans (left-id C) (sym (right-id C)))
      where
        F = functor F₀ F₁ F-id F-compose
            
        η' : (c : Obj C) → Hom C ([ [ Id[ Fun ] ]₀ F ]₀ c) ([ [ [ Id[ C ] ,-] comp ]₀ F ]₀ c)
        η' c = id C {F₀ c}

    natural' : {a b : Functor C C} {f : Hom Fun a b} → ⟨ [ [ Id[ C ] ,-] comp ]₁ f ⟩∘ᵥ⟨ η a ⟩ ≡ ⟨ η b ⟩∘ᵥ⟨ [ Id[ Fun ] ]₁ f ⟩
    natural' {F} {G} {α} = natural-transformation-eq $ fun-ext $ λ (c : Obj C) → begin
      nat-η ⟨ [ [ Id[ C ] ,-] comp ]₁ α ⟩∘ᵥ⟨ η F ⟩ c 
        ≡⟨⟩
      nat-η ([ [ Id[ C ] ,-] comp ]₁ α) c ∘C id C
        ≡⟨ left-id C ⟩
      nat-η ([ [ Id[ C ] ,-] comp ]₁ α) c
        ≡⟨⟩
      id C ∘C nat-η α c
        ≡⟨ right-id C ⟩
      nat-η α c
        ≡⟨⟩
      nat-η ([ Id[ Fun ] ]₁ α) c
        ≡⟨ sym (right-id C) ⟩
      id C ∘C nat-η ([ Id[ Fun ] ]₁ α) c
        ≡⟨⟩
      nat-η ⟨ η G ⟩∘ᵥ⟨ [ Id[ Fun ] ]₁ α ⟩ c ∎ 
