
open import Level
open import Function hiding ( id ) renaming ( _∘_ to _∘F_ )

open import Data.Product renaming ( _,_ to _,'_ )

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Extensionality

open import Theory.Triple renaming ( _,_,_ to _,'_,'_ )
open import Theory.Category.Definition
open import Theory.Category.Monoidal
open import Theory.Category.Isomorphism
open import Theory.Category.Examples.Functor
open import Theory.Functor.Definition
open import Theory.Functor.Composition
open import Theory.Natural.Transformation
open import Theory.Natural.Transformation.Properties

module Theory.Functor.Examples.CompositionFunctor 
  {ℓC₀ ℓC₁ ℓD₀ ℓD₁ ℓE₀ ℓE₁ : Level} 
  (C : Category {ℓC₀} {ℓC₁}) (D : Category {ℓD₀} {ℓD₁}) (E : Category {ℓE₀} {ℓE₁})
  where

open Category
open NaturalTransformation

private
  _∘C_ = _∘_ C
  _∘D_ = _∘_ D
  _∘E_ = _∘_ E
    
compositionFunctor : Functor ([ D , E ] ×C [ C , D ]) [ C , E ]
compositionFunctor = functor cf₀ cf₁ (λ {a} → cf-id {a}) (λ {a b c} {f} {g} → cf-comp {a} {b} {c} {f} {g})
  where 
    Src₁ = [ D , E ]
    Src₂ = [ C , D ]
    Src = Src₁ ×C Src₂
    Dst = [ C , E ]
    
    _∘Src_ = _∘_ Src
    
    cf₀ : Obj Src → Obj Dst
    cf₀ (F ,' G) = [ F ]∘[ G ]
        
    cf₁ : {a b : Obj Src} → Hom Src a b → Hom Dst (cf₀ a) (cf₀ b)
    cf₁ {F ,' G} {F' ,' G'} (α ,' β) = ⟨ α ⟩∘ₕ⟨ β ⟩
    
    abstract
      cf-id : {a : Obj Src} → ⟨ id Src₁ {proj₁ a} ⟩∘ₕ⟨ id Src₂ {proj₂ a} ⟩ ≡ id Dst {cf₀ a}
      cf-id {F ,' G} = natural-transformation-eq $ fun-ext $ λ (c : Obj C) → begin
        η (⟨ id Src₁ {F} ⟩∘ₕ⟨ id Src₂ {G} ⟩) c
          ≡⟨⟩
        η (id Src₁ {F}) ([ G ]₀ c) ∘E [ F ]₁ (η (id Src₂ {G}) c)
          ≡⟨⟩
        id E {[ F ]₀ ([ G ]₀ c)} ∘E [ F ]₁ (id D {[ G ]₀ c})
          ≡⟨ cong (λ X → id E {[ F ]₀ ([ G ]₀ c)} ∘E X) (Functor.id F) ⟩ 
        id E {[ F ]₀ ([ G ]₀ c)} ∘E id E {[ F ]₀ ([ G ]₀ c)}
          ≡⟨ left-id E ⟩
        id E {[ F ]₀ ([ G ]₀ c)} ∎
  
    abstract
      cf-comp : {a b c : Obj Src} {f : Hom Src a b} {g : Hom Src b c} 
              → cf₁ (g ∘Src f) ≡ ⟨ cf₁ g ⟩∘ᵥ⟨ cf₁ f ⟩
      cf-comp {F ,' G} {F' ,' G'} {F'' ,' G''} {α ,' β} {α' ,' β'} = composition-exchange {F = F} {F'} {F''} {G} {G'} {G''} α' α β' β
