
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
  field
    w : Obj X
    e : Wedge w F
    
    universal : ∀ {w' : Obj X} (e' : Wedge w' F) → ∃ λ (f : Hom X w' w) → (IsUnique f) × (e' ≡ Wedge.compose e f)
    
  private
    _∘X_ = _∘_ X
  
  universal-extranatural : {ℓA₀ ℓA₁ ℓB₀ ℓB₁ : Level} 
                         → (A : Category {ℓA₀} {ℓA₁}) (B : Category {ℓB₀} {ℓB₁}) 
                         → ∀ {w' : Obj X} (e' : Wedge w' F) → ∃ λ (f : Hom X w' w) → (IsUnique f) × (Wedge.extranatural e' A B ≡ Wedge.extranatural (Wedge.compose e f) A B)
  universal-extranatural A B e' = proj₁ (universal e') , proj₁ (proj₂ (universal e')) 
                                , (extranatural-transformation-eq $ fun-ext $ λ a → fun-ext $ λ b → cong Wedge.e $ proj₂ $ proj₂ $ universal e')
  
--------------------------------------------------------------------------------
-- Definition of coends
-- See: https://ncatlab.org/nlab/show/end#explicit_definition
--------------------------------------------------------------------------------

record CoEnd {ℓC₀ ℓC₁ ℓX₀ ℓX₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {X : Category {ℓX₀} {ℓX₁}} (F : Functor (C op ×C C) X) : Set (ℓC₀ ⊔ ℓC₁ ⊔ ℓX₀ ⊔ ℓX₁) where
  field
    co-w : Obj X
    co-e : CoWedge F co-w
    
    co-universal : ∀ {co-w' : Obj X} (co-e' : CoWedge F co-w') → ∃ λ (f : Hom X co-w co-w') → (IsUnique f) × (co-e' ≡ CoWedge.co-compose co-e f)
    
  private
    _∘X_ = _∘_ X
  
  universal-extranatural : {ℓA₀ ℓA₁ ℓB₀ ℓB₁ : Level} 
                         → (A : Category {ℓA₀} {ℓA₁}) (B : Category {ℓB₀} {ℓB₁}) 
                         → ∀ {co-w' : Obj X} (co-e' : CoWedge F co-w') → ∃ λ (f : Hom X co-w co-w') → (IsUnique f) × (CoWedge.extranatural co-e' A B ≡ CoWedge.extranatural (CoWedge.co-compose co-e f) A B)
  universal-extranatural A B co-e' = proj₁ (co-universal co-e') , proj₁ (proj₂ (co-universal co-e')) 
                                   , (extranatural-transformation-eq $ fun-ext $ λ a → fun-ext $ λ b → fun-ext $ λ c → cong (λ Y → CoWedge.co-e Y b) $ proj₂ $ proj₂ $ co-universal co-e')
  
