
open import Level
open import Function renaming ( _∘_ to _∘F_ ; id to idF )

open import Data.Product
open import Data.Unit

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality

open import Extensionality
open import Theory.Category.Definition
open import Theory.Functor.Definition
open import Theory.TwoCategory.Definition

open import Theory.Category.Examples.Codiscrete

module Theory.TwoCategory.Examples.CodiscreteHomCat where

codiscreteHomCatTwoCategory : {ℓObj ℓHom : Level} → Category {ℓObj} {ℓHom} → StrictTwoCategory {ℓObj} {ℓHom} {ℓHom}
codiscreteHomCatTwoCategory {ℓObj} {ℓHom} C = record
  { Cell₀ = Obj C
  ; HomCat = HomCat
  ; comp = comp
  ; id₁ = id₁
  ; horizontalIdL₁ = left-id C
  ; horizontalIdL₂ = refl
  ; horizontalIdR₁ = right-id C
  ; horizontalIdR₂ = refl
  ; horizontalAssoc₁ = assoc C
  ; horizontalAssoc₂ = refl
  } where
    open Category

    _∘C_ = _∘_ C

    HomCat : Obj C → Obj C → Category
    HomCat a b = codiscreteCategory (Hom C a b)

    comp : {a b c : Obj C} → Functor (HomCat b c ×C HomCat a b) (HomCat a c)
    comp {a} {b} {c} = functor F₀ (λ {x y} → F₁ {x} {y}) refl (λ {x y z} → compose {x} {y} {z})
      where
        _∘Comp_ = _∘_ (HomCat b c ×C HomCat a b)
        _∘AC_ = _∘_ (HomCat a c)
        
        F₀ : Obj (HomCat b c ×C HomCat a b) → Obj (HomCat a c)
        F₀ (x , y) = x ∘C y
        
        F₁ : {x y : Obj (HomCat b c ×C HomCat a b)} → Hom (HomCat b c ×C HomCat a b) x y → Hom (HomCat a c) (F₀ x) (F₀ y)
        F₁ (lift tt , lift tt) = lift tt
        
        abstract
          compose : {x y z : Obj (HomCat b c ×C HomCat a b)} 
                  → {f : Hom (HomCat b c ×C HomCat a b) x y} {g : Hom (HomCat b c ×C HomCat a b) y z}
                  → F₁ {x} {z} (_∘Comp_ {x} {y} {z} g f) ≡ _∘AC_ {a = F₀ x} {F₀ y} {F₀ z} (F₁ {x} {y} g) (F₁ {y} {z} f)
          compose {f = lift tt , lift tt} {lift tt , lift tt} = refl
    
    id₁ : {a : Obj C} → Obj (HomCat a a)
    id₁ {a} = id C {a}
