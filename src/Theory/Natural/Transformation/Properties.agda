
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

composition-exchange : {ℓC₀ ℓC₁ : Level} 
                     → {C : Category {ℓC₀} {ℓC₁}} 
                     → {F G H F' G' H' : Functor C C}
                     → (α : NaturalTransformation G H) (β : NaturalTransformation F G) (γ : NaturalTransformation G' H') (δ : NaturalTransformation F' G')
                     → ⟨ ⟨ α ⟩∘ᵥ⟨ β ⟩ ⟩∘ₕ⟨ ⟨ γ ⟩∘ᵥ⟨ δ ⟩ ⟩ ≡ ⟨ ⟨ α ⟩∘ₕ⟨ γ ⟩ ⟩∘ᵥ⟨ ⟨ β ⟩∘ₕ⟨ δ ⟩ ⟩
composition-exchange {C = C} {F} {G} {H} {F'} {G'} {H'} α β γ δ = natural-transformation-eq $ fun-ext $ λ (c : Obj C) → begin
  η (⟨ ⟨ α ⟩∘ᵥ⟨ β ⟩ ⟩∘ₕ⟨ ⟨ γ ⟩∘ᵥ⟨ δ ⟩ ⟩) c  
    ≡⟨⟩
  (η α ([ H' ]₀ c) ∘C η β ([ H' ]₀ c)) ∘C [ F ]₁ (η γ c ∘C η δ c)
    ≡⟨ cong (λ X → (η α ([ H' ]₀ c) ∘C η β ([ H' ]₀ c)) ∘C X) (Functor.compose F) ⟩
  (η α ([ H' ]₀ c) ∘C η β ([ H' ]₀ c)) ∘C ([ F ]₁ (η γ c) ∘C [ F ]₁ (η δ c))
    ≡⟨ sym $ assoc C ⟩
  η α ([ H' ]₀ c) ∘C (η β ([ H' ]₀ c) ∘C ([ F ]₁ (η γ c) ∘C [ F ]₁ (η δ c)))
    ≡⟨ cong (λ X → η α ([ H' ]₀ c) ∘C X) (assoc C) ⟩
  η α ([ H' ]₀ c) ∘C ((η β ([ H' ]₀ c) ∘C [ F ]₁ (η γ c)) ∘C [ F ]₁ (η δ c))
    ≡⟨ cong (λ X → η α ([ H' ]₀ c) ∘C (X ∘C [ F ]₁ (η δ c))) (sym $ natural β) ⟩
  η α ([ H' ]₀ c) ∘C (([ G ]₁ (η γ c) ∘C η β ([ G' ]₀ c)) ∘C [ F ]₁ (η δ c))
    ≡⟨ cong (λ X → η α ([ H' ]₀ c) ∘C X) (sym $ assoc C) ⟩
  η α ([ H' ]₀ c) ∘C ([ G ]₁ (η γ c) ∘C (η β ([ G' ]₀ c) ∘C [ F ]₁ (η δ c)))
    ≡⟨ assoc C ⟩
  (η α ([ H' ]₀ c) ∘C [ G ]₁ (η γ c)) ∘C (η β ([ G' ]₀ c) ∘C [ F ]₁ (η δ c))
    ≡⟨⟩
  η ⟨ ⟨ α ⟩∘ₕ⟨ γ ⟩ ⟩∘ᵥ⟨ ⟨ β ⟩∘ₕ⟨ δ ⟩ ⟩ c ∎
  where
    _∘C_ = Category._∘_ C
