
open import Level
open import Function renaming ( _∘_ to _∘F_ ) hiding ( id )

open import Data.Product

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Utilities

open import Theory.Category.Definition
open import Theory.Category.Examples

open import Theory.Functor.Definition
open import Theory.Natural.Transformation
open import Theory.End.Wedge
open import Theory.End.Definition

module Theory.End.Properties where

open Category
open Functor hiding ( id )
open NaturalTransformation renaming ( η to nat-η )

wedgeTransform : {ℓC₀ ℓC₁ ℓS : Level} {C : Category {ℓC₀} {ℓC₁}} 
               → {H H' : Functor (C op ×C C) (setCategory {ℓC₀ ⊔ ℓC₁ ⊔ ℓS})} → (θ : NaturalTransformation H H') → {w : Obj (setCategory {ℓC₀ ⊔ ℓC₁ ⊔ ℓS})} 
               → Wedge w H → Wedge w H'
wedgeTransform {ℓC₀} {ℓC₁} {ℓS} {C} {functor H₀ H₁ H-id H-comp} {functor H'₀ H'₁ H'-id H'-comp} θ {w} (wedge f coher) = wedge f' coher'
  where
    Set' = setCategory {ℓC₀ ⊔ ℓC₁ ⊔ ℓS}
    _∘C_ = _∘_ C
    
    f' : (c : Obj C) → Hom Set' w (H'₀ (c , c))
    f' c = nat-η θ (c , c) ∘F f c
    
    coher' : {c c' : Obj C} (g : Hom C c c') → H'₁ (g , id C) ∘F f' c' ≡ H'₁ (id C , g) ∘F f' c
    coher' {c} {c'} g = begin
      H'₁ (g , id C) ∘F f' c' 
        ≡⟨⟩
      H'₁ (g , id C) ∘F (nat-η θ (c' , c') ∘F f c')
        ≡⟨ cong (λ X → X ∘F f c') (natural θ) ⟩
      (nat-η θ (c , c') ∘F H₁ (g , id C)) ∘F f c'
        ≡⟨ cong (λ X → nat-η θ (c , c') ∘F X) (coher g) ⟩
      (nat-η θ (c , c') ∘F H₁ (id C , g)) ∘F f c
        ≡⟨ cong (λ X → X ∘F f c) (sym (natural θ)) ⟩
      H'₁ (id C , g) ∘F (nat-η θ (c , c) ∘F f c)
        ≡⟨⟩
      H'₁ (id C , g) ∘F f' c ∎

cowedgeTransform : {ℓC₀ ℓC₁ ℓS : Level} {C : Category {ℓC₀} {ℓC₁}} 
                 → {H H' : Functor (C op ×C C) (setCategory {ℓC₀ ⊔ ℓC₁ ⊔ ℓS})} → (θ : NaturalTransformation H H') → {w : Obj (setCategory {ℓC₀ ⊔ ℓC₁ ⊔ ℓS})} 
                 → CoWedge H' w → CoWedge H w
cowedgeTransform {ℓC₀} {ℓC₁} {ℓS} {C} {functor H₀ H₁ H-id H-comp} {functor H'₀ H'₁ H'-id H'-comp} θ {w} (cowedge f coher) = cowedge f' coher'
  where
    Set' = setCategory {ℓC₀ ⊔ ℓC₁ ⊔ ℓS}
    _∘C_ = _∘_ C
    
    f' : (c : Obj C) → Hom Set' (H₀ (c , c)) w
    f' c = f c ∘F nat-η θ (c , c)
    
    coher' : {c c' : Obj C} (g : Hom C c c') → f' c' ∘F H₁ (id C , g) ≡ f' c ∘F H₁ (g , id C)
    coher' {c} {c'} g = begin
      f' c' ∘F H₁ (id C , g) 
        ≡⟨⟩
      (f c' ∘F nat-η θ (c' , c')) ∘F H₁ (id C , g) 
        ≡⟨ cong (λ X → f c' ∘F X) (sym (natural θ)) ⟩
      f c' ∘F (H'₁ (id C , g) ∘F nat-η θ (c' , c)) 
        ≡⟨ cong (λ X → X ∘F nat-η θ (c' , c)) (coher g) ⟩
      f c ∘F (H'₁ (g , id C) ∘F nat-η θ (c' , c))
        ≡⟨ cong (λ X → f c ∘F X) (natural θ) ⟩
      (f c ∘F nat-η θ (c , c)) ∘F H₁ (g , id C)
        ≡⟨⟩
      f' c ∘F H₁ (g , id C) ∎

endMorph : {ℓC₀ ℓC₁ ℓS : Level} {C : Category {ℓC₀} {ℓC₁}} 
         → {H H' : Functor (C op ×C C) (setCategory {ℓC₀ ⊔ ℓC₁ ⊔ ℓS})} 
         → (θ : NaturalTransformation H H') → Hom (setCategory {ℓC₀ ⊔ ℓC₁ ⊔ ℓS}) (Set-∫ ℓS H) (Set-∫ ℓS H')
endMorph {ℓC₀} {ℓC₁} {ℓS} {C} {H} {H'} θ = proj₁ $ End.universal (setEnd ℓS H') $ wedgeTransform {ℓS = ℓS} θ $ End.e $ setEnd ℓS H

coendMorph : {ℓC₀ ℓC₁ ℓS : Level} {C : Category {ℓC₀} {ℓC₁}} 
           → {H H' : Functor (C op ×C C) (setCategory {ℓC₀ ⊔ ℓC₁ ⊔ ℓS})} → (θ : NaturalTransformation H H') 
           → Hom (setCategory {ℓC₀ ⊔ ℓC₁ ⊔ ℓS}) (Set-co-∫ ℓS H) (Set-co-∫ ℓS H')
coendMorph {ℓC₀} {ℓC₁} {ℓS} {C} {H} {H'} θ = proj₁ $ CoEnd.co-universal (setCoEnd ℓS H) $ cowedgeTransform {ℓS = ℓS} θ $ CoEnd.co-e $ setCoEnd ℓS H'

coend-morph-unique : {ℓC₀ ℓC₁ ℓS : Level} {C : Category {ℓC₀} {ℓC₁}} 
                   → {H H' : Functor (C op ×C C) (setCategory {ℓC₀ ⊔ ℓC₁ ⊔ ℓS})} → (θ : NaturalTransformation H H') 
                   → (f : Hom (setCategory {ℓC₀ ⊔ ℓC₁ ⊔ ℓS}) (Set-co-∫ ℓS H) (Set-co-∫ ℓS H')) → f ≡ coendMorph θ
coend-morph-unique {ℓC₀} {ℓC₁} {ℓS} {C} {H} {H'} θ = proj₁ $ proj₂ $ CoEnd.co-universal (setCoEnd ℓS H) $ cowedgeTransform {ℓS = ℓS} θ $ CoEnd.co-e $ setCoEnd ℓS H'
