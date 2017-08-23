
open import Level
open import Function renaming ( _∘_ to _∘F_ ; id to idF )

open import Data.Product

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( refl to hrefl ; sym to hsym ; subst₂ to hsubst₂ ; proof-irrelevance to hproof-irrelevance )

open import Extensionality
open import Theory.Category.Definition
open import Theory.Functor.Definition
open import Theory.TwoCategory.Definition

open import Theory.Category.Examples.Discrete

module Theory.TwoCategory.Examples.DiscreteHomCat where

discreteHomCatTwoCategory : {ℓObj ℓHom : Level} → Category {ℓObj} {ℓHom} → StrictTwoCategory {ℓObj} {ℓHom} {ℓHom}
discreteHomCatTwoCategory {ℓObj} {ℓHom} C = record
  { Cell₀ = Obj C
  ; HomCat = HomCat
  ; comp = comp
  ; id₁ = id₁
  ; horizontalIdL₁ = left-id C
  ; horizontalIdL₂ = hIdL₂
  ; horizontalIdR₁ = right-id C
  ; horizontalIdR₂ = hIdR₂
  ; horizontalAssoc₁ = assoc C
  ; horizontalAssoc₂ = hAss₂
  } where
    open Category

    _∘C_ = _∘_ C

    HomCat : Obj C → Obj C → Category
    HomCat a b = discreteCategory (Hom C a b)

    comp : {a b c : Obj C} → Functor (HomCat b c ×C HomCat a b) (HomCat a c)
    comp {a} {b} {c} = functor F₀ F₁ refl compose
      where
        _∘Comp_ = _∘_ (HomCat b c ×C HomCat a b)
        _∘AC_ = _∘_ (HomCat a c)
        
        F₀ : Obj (HomCat b c ×C HomCat a b) → Obj (HomCat a c)
        F₀ (x , y) = x ∘C y
        
        F₁ : {x y : Obj (HomCat b c ×C HomCat a b)} → Hom (HomCat b c ×C HomCat a b) x y → Hom (HomCat a c) (F₀ x) (F₀ y)
        F₁ (refl , refl) = refl
        
        abstract
          compose : {x y z : Obj (HomCat b c ×C HomCat a b)} 
                  → {f : Hom (HomCat b c ×C HomCat a b) x y} {g : Hom (HomCat b c ×C HomCat a b) y z}
                  → F₁ (g ∘Comp f) ≡ F₁ g ∘AC F₁ f
          compose {f = refl , refl} {refl , refl} = refl
    
    id₁ : {a : Obj C} → Obj (HomCat a a)
    id₁ {a} = id C {a}
    
    abstract
      subst₂-elim' : {a b : Obj C}
                   → {f g : Obj (HomCat a b)}
                   → (eq : g ≡ f)
                   → refl {ℓHom} {Hom C a b} {f} ≅ refl {ℓHom} {Hom C a b} {g}
      subst₂-elim' refl = hrefl
    
    abstract
      hIdL₂ : {a b : Obj C} {f g : Obj (HomCat a b)} {η : Hom (HomCat a b) f g}
            → [ comp ]₁ (η , id (HomCat a a)) ≅ η
      hIdL₂ {a} {b} {f} {.f} {refl} = subst₂-elim' (sym (left-id C))
    
    abstract
      hIdR₂ : {a b : Obj C} {f g : Obj (HomCat a b)} {η : Hom (HomCat a b) f g} 
            → [ comp ]₁ (id (HomCat b b) , η) ≅ η
      hIdR₂ {a} {b} {f} {.f} {refl} = subst₂-elim' (sym (right-id C)) 
    
    abstract
      hAss₂ : {a b c d : Obj C} 
            → {f f' : Obj (HomCat a b)} {g g' : Obj (HomCat b c)} {h h' : Obj (HomCat c d)}
            → {η : Hom (HomCat c d) h h'} {θ : Hom (HomCat b c) g g'} {ι : Hom (HomCat a b) f f'}
            → [ comp ]₁ (η , [ comp ]₁ (θ , ι)) ≅ ([ comp ]₁ ([ comp ]₁ (η , θ) , ι))
      hAss₂ {a} {b} {c} {d} {f} {.f} {g} {.g} {h} {.h} {refl} {refl} {refl} = subst₂-elim' (sym $ assoc C)
    
