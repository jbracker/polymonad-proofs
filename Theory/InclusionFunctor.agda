
module Theory.InclusionFunctor where

open import Level renaming ( suc to lsuc ; zero to lzero)
open import Data.Product
open import Relation.Binary.PropositionalEquality


open import Utilities renaming ( _∈_ to _∈'_ )
open import Haskell
open import ProofIrrelevance
open import Theory.Category
open import Theory.Subcategory
open import Theory.Functor

-- Define the subcategory of D in terms of C's inclusion into D through a functor.
InclusionFunctor→Subcategory : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓC₀ ⊔ ℓD₀} {ℓC₀ ⊔ ℓC₁ ⊔ ℓD₀ ⊔ ℓD₁}}
                             → (IncF : Functor C D)
                             → IsInjective (Functor.F₀ IncF)
                             → ((x y : Category.Obj C) → IsInjective (Functor.F₁ IncF {x} {y}))
                             → Subcategory D
InclusionFunctor→Subcategory {C = C} {D = D} IncF injF₀ injF₁ = record 
  { SubObj = SubObj
  ; SubHom = SubHom
  ; closedMorphs = closedMorphs
  ; closedComp = closedComp
  ; closedId = closedId
  } where

    _∘D_ = Category._∘_ D
    _∘C_ = Category._∘_ C
    
    proof-irr-obj : (A : Category.Obj D) → ProofIrrelevance (∃ (λ x → Functor.F₀ IncF x ≡ A))
    proof-irr-obj ._ (x , refl) (y , q) with injF₀ y x q
    proof-irr-obj ._ (x , refl) (.x , refl) | refl = refl
    
    SubObj : PropSubsetOf (Category.Obj D)
    SubObj A = (∃ λ (x : Category.Obj C) → Functor.F₀ IncF x ≡ A) , proof-irr-obj A
    
    proof-irr-hom : (A B : Category.Obj D) → (f : Category.Hom D A B) 
                  → ProofIrrelevance ( ∃ λ (x : A ∈ SubObj) → ∃ λ (y : B ∈ SubObj) → ∃ λ (g : Category.Hom C (proj₁ x) (proj₁ y)) 
                                       → Functor.F₁ IncF g ≡ subst₂ (Category.Hom D) (sym (proj₂ x)) (sym (proj₂ y)) f)
    proof-irr-hom ._ ._ ._ ((x₁ , refl) , (y₁ , refl) , g₁ , refl) ((x₂ , Fx₂≡Fx₁) , (y₂ , Fy₂≡Fy₁) , g₂ , Fg₁≡Fg₂) with injF₀ x₂ x₁ Fx₂≡Fx₁ | injF₀ y₂ y₁ Fy₂≡Fy₁
    proof-irr-hom ._ ._ ._ ((x₁ , refl) , (y₁ , refl) , g₁ , refl) ((.x₁ , refl) , (.y₁ , refl) , g₂ , Fg₂≡Fg₁) | refl | refl with injF₁ x₁ y₁ g₂ g₁ Fg₂≡Fg₁
    proof-irr-hom ._ ._ ._ ((x₁ , refl) , (y₁ , refl) , g₁ , refl) ((.x₁ , refl) , (.y₁ , refl) , .g₁ , refl) | refl | refl | refl = refl
    
    SubHom : (a b : Category.Obj D) → PropSubsetOf (Category.Hom D a b)
    SubHom A B f = ( ∃ λ (x : A ∈ SubObj) → ∃ λ (y : B ∈ SubObj) → ∃ λ (g : Category.Hom C (proj₁ x) (proj₁ y)) 
                     → Functor.F₁ IncF g ≡ subst₂ (Category.Hom D) (sym (proj₂ x)) (sym (proj₂ y)) f) 
                 , proof-irr-hom A B f
    
    closedMorphs : {α β : Category.Obj D} 
                 → (f : Category.Hom D α β) 
                 → (f ∈ SubHom α β) → (α ∈ SubObj) × (β ∈ SubObj)
    closedMorphs {._} {._} ._ ((x , refl) , (y , refl) , g , refl) = (x , refl) , (y , refl)
    
    closedComp : {α β γ : Category.Obj D}
               → (f : Category.Hom D α β)
               → (g : Category.Hom D β γ)
               → (f ∈ SubHom α β) → (g ∈ SubHom β γ)
               → ((g ∘D f) ∈ SubHom α γ)
    closedComp {._} {._} {._} ._ g ((x₁ , refl) , (y₁ , refl) , g₁ , refl) ((x₂ , Fx₂≡Fy₁) , (y₂ , refl) , g₂ , Fg₂≡Fg₁) with injF₀ x₂ y₁ Fx₂≡Fy₁
    closedComp {._} {._} {._} ._ ._ ((x₁ , refl) , (y₁ , refl) , g₁ , refl) ((.y₁ , refl) , (y₂ , refl) , g₂ , refl) | refl = (x₁ , refl) , (y₂ , refl) , (g₂ ∘C g₁) , Functor.dist IncF
    
    closedId : {α : Category.Obj D}
             → (α ∈ SubObj) → (Category.id D ∈ SubHom α α)
    closedId {._} (x , refl) = (x , refl) , (x , refl) , Category.id C , Functor.id IncF

InclusionFunctor→LiftSubcategory : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}}
                                 → (IncF : Functor C D)
                                 → IsInjective (Functor.F₀ IncF)
                                 → ((x y : Category.Obj C) → IsInjective (Functor.F₁ IncF {x} {y}))
                                 → Subcategory (liftCategory {ℓL₀ = ℓC₀ ⊔ ℓD₀} {ℓL₁ = ℓC₀ ⊔ ℓC₁ ⊔ ℓD₀ ⊔ ℓD₁} D)
InclusionFunctor→LiftSubcategory {ℓC₀} {ℓC₁} {ℓD₀} {ℓD₁} {C} {D} IncF injF₀ injF₁ = InclusionFunctor→Subcategory {ℓD₀ = ℓD₀} {ℓD₁ = ℓD₁} LiftIncF liftInjF₀ liftInjF₁
  where
    LiftD = liftCategory D
    
    LiftIncF : Functor C LiftD
    LiftIncF = record 
      { F₀ = λ x → lift (Functor.F₀ IncF x) 
      ; F₁ = λ f → lift (Functor.F₁ IncF f) 
      ; id = λ {a} → cong lift (Functor.id IncF {a}) 
      ; dist = λ {a} {b} {c} {f} {g} → cong lift (Functor.dist IncF {a} {b} {c} {f} {g}) 
      }
    
    LiftIncF₀≡IncF₀ : (x : Category.Obj C) → Functor.F₀ LiftIncF x ≡ lift (Functor.F₀ IncF x)
    LiftIncF₀≡IncF₀ x = refl
    
    LiftIncF₁≡IncF₁ : {x y : Category.Obj C} → (f : Category.Hom C x y) → Functor.F₁ LiftIncF f ≡ lift (Functor.F₁ IncF f)
    LiftIncF₁≡IncF₁ f = refl
    
    liftObjEq : {ℓ : Level} {a b : Category.Obj D} → lift {ℓ = ℓ} a ≡ lift {ℓ = ℓ} b → a ≡ b
    liftObjEq refl = refl
    
    liftHomEq : {ℓ : Level} {a b : Category.Obj D} {f g : Category.Hom D a b} → lift {ℓ = ℓ} f ≡ lift {ℓ = ℓ} g → f ≡ g
    liftHomEq refl = refl
    
    liftInjF₀ : IsInjective (Functor.F₀ LiftIncF)
    liftInjF₀ x y p with LiftIncF₀≡IncF₀ x | LiftIncF₀≡IncF₀ y
    liftInjF₀ x y p | refl | refl = injF₀ x y (liftObjEq p)
    
    liftInjF₁ : (x y : Category.Obj C) → IsInjective (Functor.F₁ LiftIncF {x} {y})
    liftInjF₁ x y f g p with LiftIncF₁≡IncF₁ f | LiftIncF₁≡IncF₁ g 
    liftInjF₁ x y f g p | refl | refl = injF₁ x y f g (liftHomEq p)
