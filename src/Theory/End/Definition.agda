
open import Level
open import Function renaming ( _∘_ to _∘F_ ) hiding ( id )

open import Data.Product

open import Relation.Binary.PropositionalEquality

open import Utilities
open import Extensionality
open import Theory.Category.Definition
open import Theory.Functor.Definition
open import Theory.Functor.Constant
open import Theory.Functor.Application
open import Theory.End.Wedge
open import Theory.Natural.ExtranaturalTransformation

module Theory.End.Definition where

open Category
open Functor renaming (id to fun-id ; compose to fun-compose)

open Theory.Functor.Application.TriFunctor

--------------------------------------------------------------------------------
-- Definition of ends
-- See: https://ncatlab.org/nlab/show/end#explicit_definition
--------------------------------------------------------------------------------

record End {ℓC₀ ℓC₁ ℓX₀ ℓX₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {X : Category {ℓX₀} {ℓX₁}} (F : Functor (C op ×C C) X) : Set (ℓC₀ ⊔ ℓC₁ ⊔ ℓX₀ ⊔ ℓX₁) where
  constructor end
  field 
    ∫ : Obj X
    e : Wedge ∫ F
    
    universal : {∫' : Obj X} (e' : Wedge ∫' F) → ∃ λ (f : Hom X ∫' ∫) → (IsUnique f) × (Wedge.e e' ≡ Wedge.e (Wedge.compose e f))
    
  private
    _∘X_ = _∘_ X
  
  universal-wedge : {∫' : Obj X} (e' : Wedge ∫' F) → ∃ λ (f : Hom X ∫' ∫) → (IsUnique f) × (e' ≡ Wedge.compose e f)
  universal-wedge {∫'} e' = proj₁ (universal e') , proj₁ (proj₂ (universal e'))
                          , wedge-eq (proj₂ (proj₂ (universal e')))
  
  universal-extranatural : {ℓA₀ ℓA₁ ℓB₀ ℓB₁ : Level} 
                         → (A : Category {ℓA₀} {ℓA₁}) (B : Category {ℓB₀} {ℓB₁}) 
                         → ∀ {∫' : Obj X} (e' : Wedge ∫' F) → ∃ λ (f : Hom X ∫' ∫) → (IsUnique f) × (Wedge.extranatural e' A B ≡ Wedge.extranatural (Wedge.compose e f) A B)
  universal-extranatural A B e' = proj₁ (universal e') , proj₁ (proj₂ (universal e')) 
                                , (extranatural-transformation-eq $ fun-ext $ λ a → fun-ext $ λ b → proj₂ (proj₂ (universal e')))
  
--------------------------------------------------------------------------------
-- Definition of coends
-- See: https://ncatlab.org/nlab/show/end#explicit_definition
--------------------------------------------------------------------------------

record CoEnd {ℓC₀ ℓC₁ ℓX₀ ℓX₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {X : Category {ℓX₀} {ℓX₁}} (F : Functor (C op ×C C) X) : Set (ℓC₀ ⊔ ℓC₁ ⊔ ℓX₀ ⊔ ℓX₁) where
  field
    co-∫ : Obj X
    co-e : CoWedge F co-∫
    
    co-universal : ∀ {co-∫' : Obj X} (co-e' : CoWedge F co-∫') → ∃ λ (f : Hom X co-∫ co-∫') → (IsUnique f) × (co-e' ≡ CoWedge.co-compose co-e f)
    
  private
    _∘X_ = _∘_ X
  
  universal-extranatural : {ℓA₀ ℓA₁ ℓB₀ ℓB₁ : Level} 
                         → (A : Category {ℓA₀} {ℓA₁}) (B : Category {ℓB₀} {ℓB₁}) 
                         → ∀ {co-∫' : Obj X} (co-e' : CoWedge F co-∫') → ∃ λ (f : Hom X co-∫ co-∫') → (IsUnique f) × (CoWedge.extranatural co-e' A B ≡ CoWedge.extranatural (CoWedge.co-compose co-e f) A B)
  universal-extranatural A B co-e' = proj₁ (co-universal co-e') , proj₁ (proj₂ (co-universal co-e')) 
                                   , (extranatural-transformation-eq $ fun-ext $ λ a → fun-ext $ λ b → fun-ext $ λ c → cong (λ Y → CoWedge.co-e Y b) $ proj₂ $ proj₂ $ co-universal co-e')
  
