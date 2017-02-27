
module Theory.Functor.Examples where 

-- Stdlib
open import Level renaming ( suc to lsuc ; zero to lzero )
open import Function hiding ( id ) renaming ( _∘_ to _∘F_ )
open import Data.Product renaming ( _,_ to _,'_ ; proj₁ to proj₁' ; proj₂ to proj₂' )
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality hiding ( cong ; subst ; subst₂ ; sym ; trans )
open ≡-Reasoning 

-- Local
open import Utilities
open import Extensionality
open import Theory.Triple
open import Theory.Category
open import Theory.Functor
open import Theory.Functor.Composition
open import Theory.Natural.Transformation
open import Theory.Natural.Transformation.Whisker

open import Theory.Category.Examples renaming ( functorCategory to Fun )

-------------------------------------------------------------------------------
-- Horizontal composition functor for natural transformations.
-------------------------------------------------------------------------------
natTransCompositionHorzFunctor 
  : {ℓA₀ ℓA₁ ℓB₀ ℓB₁ ℓC₀ ℓC₁ : Level} 
  → {A : Category {ℓA₀} {ℓA₁}} {B : Category {ℓB₀} {ℓB₁}} {C : Category {ℓC₀} {ℓC₁}} 
  → Functor (Fun B C ×C Fun A B) (Fun A C)
natTransCompositionHorzFunctor {A = A} {B} {C} = record 
  { F₀ = F₀ 
  ; F₁ = F₁
  ; id = λ {F} → id {F}
  ; compose = λ {F} {G} {H} {α} {β} → compose {F} {G} {H} {α} {β} 
  } where  
    open Category renaming ( id to idC )
    open NaturalTransformation
    
    F₀ : Obj (Fun B C ×C Fun A B) → Obj (Fun A C)
    F₀ (G ,' F) = [ G ]∘[ F ]
    
    F₁ : {F G : Obj (Fun B C ×C Fun A B)} 
       → Hom (Fun B C ×C Fun A B) F G → Hom (Fun A C) (F₀ F) (F₀ G)
    F₁ (α ,' β) = ⟨ α ⟩∘ₕ⟨ β ⟩
    
    id : {F : Obj (Fun B C ×C Fun A B)} 
       → F₁ {F = F} {G = F} (idC (Fun B C ×C Fun A B)) ≡ idC (Fun A C)
    id {F} = begin 
      F₁ {F = F} {G = F} (idC (Fun B C ×C Fun A B)) 
        ≡⟨ refl ⟩
      ⟨ Id⟨ proj₁' F ⟩ ⟩∘ₕ⟨ Id⟨ proj₂' F ⟩ ⟩ 
        ≡⟨ natural-transformation-eq lemma ⟩
      Id⟨ [ proj₁' F ]∘[ proj₂' F ] ⟩
        ≡⟨ refl ⟩
      Category.id (Fun A C) {a = [ proj₁' F ]∘[ proj₂' F ]} ∎
      where
        _∘C_ = _∘_ C
        
        lemma : η ⟨ Id⟨ proj₁' F ⟩ ⟩∘ₕ⟨ Id⟨ proj₂' F ⟩ ⟩ ≡ η Id⟨ [ proj₁' F ]∘[ proj₂' F ] ⟩
        lemma = fun-ext $ λ (x : Obj A) → begin 
          η ⟨ Id⟨ proj₁' F ⟩ ⟩∘ₕ⟨ Id⟨ proj₂' F ⟩ ⟩ x
            ≡⟨ refl ⟩
          η Id⟨ proj₁' F ⟩ ([ proj₂' F ]₀ x) ∘C [ proj₁' F ]₁ (η Id⟨ proj₂' F ⟩ x)
            ≡⟨ refl ⟩
          idC C ∘C [ proj₁' F ]₁ (idC B)
            ≡⟨ right-id C ⟩
          [ proj₁' F ]₁ (idC B)
            ≡⟨ Functor.id (proj₁' F) ⟩
          idC C
            ≡⟨ refl ⟩
          η Id⟨ [ proj₁' F ]∘[ proj₂' F ] ⟩ x ∎
        
    compose : {F G H : Obj (Fun B C ×C Fun A B)}
         → {α : Hom (Fun B C ×C Fun A B) F G}
         → {β : Hom (Fun B C ×C Fun A B) G H}
         → F₁ ( ⟨ proj₁' β ⟩∘ᵥ⟨ proj₁' α ⟩ ,' ⟨ proj₂' β ⟩∘ᵥ⟨ proj₂' α ⟩ ) ≡ ⟨ F₁ β ⟩∘ᵥ⟨ F₁ α ⟩
    compose {F ,' F'} {G ,' G'} {H ,' H'} {α = α₁ ,' α₂} {β = β₁ ,' β₂} = 
      natural-transformation-eq $ fun-ext $ λ (x : Obj A) → begin
        η ⟨ ⟨ β₁ ⟩∘ᵥ⟨ α₁ ⟩ ⟩∘ₕ⟨ ⟨ β₂ ⟩∘ᵥ⟨ α₂ ⟩ ⟩ x
          ≡⟨ refl ⟩
        η ⟨ β₁ ⟩∘ᵥ⟨ α₁ ⟩ ([ H' ]₀ x) ∘C [ F ]₁ (η ⟨ β₂ ⟩∘ᵥ⟨ α₂ ⟩ x)
          ≡⟨ refl ⟩
        (η β₁ ([ H' ]₀ x) ∘C η α₁ ([ H' ]₀ x)) ∘C [ F ]₁ (η β₂ x ∘B η α₂ x)
           ≡⟨ cong (λ X → (η β₁ ([ H' ]₀ x) ∘C η α₁ ([ H' ]₀ x)) ∘C X) (Functor.compose F) ⟩
        (η β₁ ([ H' ]₀ x) ∘C η α₁ ([ H' ]₀ x)) ∘C ([ F ]₁ (η β₂ x) ∘C [ F ]₁ (η α₂ x))
           ≡⟨ sym (assoc C) ⟩
        η β₁ ([ H' ]₀ x) ∘C (η α₁ ([ H' ]₀ x) ∘C ([ F ]₁ (η β₂ x) ∘C [ F ]₁ (η α₂ x)))
          ≡⟨ cong (λ X → η β₁ ([ H' ]₀ x) ∘C X) (assoc C) ⟩
        η β₁ ([ H' ]₀ x) ∘C ((η α₁ ([ H' ]₀ x) ∘C [ F ]₁ (η β₂ x)) ∘C [ F ]₁ (η α₂ x))
          ≡⟨ cong (λ X → η β₁ ([ H' ]₀ x) ∘C (X ∘C [ F ]₁ (η α₂ x))) (sym (cong (λ X → X x) (cong η (whiskerCompositionHorzEq β₂ α₁)))) ⟩
        η β₁ ([ H' ]₀ x) ∘C (([ G ]₁ (η β₂ x) ∘C η α₁ ([ G' ]₀ x)) ∘C [ F ]₁ (η α₂ x))
          ≡⟨ cong (λ X → η β₁ ([ H' ]₀ x) ∘C X) (sym (assoc C)) ⟩
        η β₁ ([ H' ]₀ x) ∘C ([ G ]₁ (η β₂ x) ∘C (η α₁ ([ G' ]₀ x) ∘C [ F ]₁ (η α₂ x)))
          ≡⟨ assoc C ⟩
        (η β₁ ([ H' ]₀ x) ∘C [ G ]₁ (η β₂ x)) ∘C (η α₁ ([ G' ]₀ x) ∘C [ F ]₁ (η α₂ x))
           ≡⟨ refl ⟩
        η ⟨ β₁ ⟩∘ₕ⟨ β₂ ⟩ x ∘C η ⟨ α₁ ⟩∘ₕ⟨ α₂ ⟩ x
          ≡⟨ refl ⟩
        η ⟨ ⟨ β₁ ⟩∘ₕ⟨ β₂ ⟩ ⟩∘ᵥ⟨ ⟨ α₁ ⟩∘ₕ⟨ α₂ ⟩ ⟩ x ∎
      where _∘B_ = _∘_ B ; _∘C_ = _∘_ C

-------------------------------------------------------------------------------
-- Composition of identity functors
-------------------------------------------------------------------------------
functor-composition-left-id : {ℓA₀ ℓA₁ ℓB₀ ℓB₁ : Level} 
                            → {A : Category {ℓA₀} {ℓA₁}} {B : Category {ℓB₀} {ℓB₁}} 
                            → (F : Functor A B)
                            → [ Id[ B ] ]∘[ F ] ≡ F
functor-composition-left-id F = functor-eq refl refl

functor-composition-right-id : {ℓA₀ ℓA₁ ℓB₀ ℓB₁ : Level} 
                             → {A : Category {ℓA₀} {ℓA₁}} {B : Category {ℓB₀} {ℓB₁}} 
                             → (F : Functor A B)
                             → [ F ]∘[ Id[ A ] ] ≡ F
functor-composition-right-id F = functor-eq refl refl
