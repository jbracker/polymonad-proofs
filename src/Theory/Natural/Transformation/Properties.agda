
open import Level
open import Function hiding ( id )

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Extensionality

open import Theory.Category.Definition
open import Theory.Functor.Definition
open import Theory.Natural.Transformation

module Theory.Natural.Transformation.Properties where

open Category
open NaturalTransformation

abstract
  composition-exchange : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ ℓE₀ ℓE₁ : Level} 
                       → {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}} {E : Category {ℓE₀} {ℓE₁}} 
                       → {F F' F'' : Functor D E} {G G' G'' : Functor C D}
                       → (α : NaturalTransformation F' F'') (β : NaturalTransformation F F') (γ : NaturalTransformation G' G'') (δ : NaturalTransformation G G')
                       → ⟨ ⟨ α ⟩∘ᵥ⟨ β ⟩ ⟩∘ₕ⟨ ⟨ γ ⟩∘ᵥ⟨ δ ⟩ ⟩ ≡ ⟨ ⟨ α ⟩∘ₕ⟨ γ ⟩ ⟩∘ᵥ⟨ ⟨ β ⟩∘ₕ⟨ δ ⟩ ⟩
  composition-exchange {C = C} {D} {E} {F} {F'} {F''} {G} {G'} {G''} α β γ δ = natural-transformation-eq $ fun-ext $ λ (c : Obj C) → begin
    η (⟨ ⟨ α ⟩∘ᵥ⟨ β ⟩ ⟩∘ₕ⟨ ⟨ γ ⟩∘ᵥ⟨ δ ⟩ ⟩) c  
      ≡⟨⟩
    (η α ([ G'' ]₀ c) ∘E η β ([ G'' ]₀ c)) ∘E [ F ]₁ (η γ c ∘D η δ c)
      ≡⟨ cong (λ X → (η α ([ G'' ]₀ c) ∘E η β ([ G'' ]₀ c)) ∘E X) (Functor.compose F) ⟩
    (η α ([ G'' ]₀ c) ∘E η β ([ G'' ]₀ c)) ∘E ([ F ]₁ (η γ c) ∘E [ F ]₁ (η δ c))
      ≡⟨ sym $ assoc E ⟩
    η α ([ G'' ]₀ c) ∘E (η β ([ G'' ]₀ c) ∘E ([ F ]₁ (η γ c) ∘E [ F ]₁ (η δ c)))
      ≡⟨ cong (λ X → η α ([ G'' ]₀ c) ∘E X) (assoc E) ⟩
    η α ([ G'' ]₀ c) ∘E ((η β ([ G'' ]₀ c) ∘E [ F ]₁ (η γ c)) ∘E [ F ]₁ (η δ c))
      ≡⟨ cong (λ X → η α ([ G'' ]₀ c) ∘E (X ∘E [ F ]₁ (η δ c))) (sym $ natural β) ⟩
    η α ([ G'' ]₀ c) ∘E (([ F' ]₁ (η γ c) ∘E η β ([ G' ]₀ c)) ∘E [ F ]₁ (η δ c))
      ≡⟨ cong (λ X → η α ([ G'' ]₀ c) ∘E X) (sym $ assoc E) ⟩
    η α ([ G'' ]₀ c) ∘E ([ F' ]₁ (η γ c) ∘E (η β ([ G' ]₀ c) ∘E [ F ]₁ (η δ c)))
      ≡⟨ assoc E ⟩
    (η α ([ G'' ]₀ c) ∘E [ F' ]₁ (η γ c)) ∘E (η β ([ G' ]₀ c) ∘E [ F ]₁ (η δ c))
      ≡⟨⟩
    η ⟨ ⟨ α ⟩∘ₕ⟨ γ ⟩ ⟩∘ᵥ⟨ ⟨ β ⟩∘ₕ⟨ δ ⟩ ⟩ c ∎
    where
      _∘D_ = Category._∘_ D
      _∘E_ = Category._∘_ E
    
