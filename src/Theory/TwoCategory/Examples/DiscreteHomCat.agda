
open import Level
open import Function renaming ( _∘_ to _∘F_ ; id to idF )

open import Data.Product

open import Relation.Binary.PropositionalEquality

open import Extensionality
open import Theory.Category.Definition
open import Theory.Functor.Definition
open import Theory.TwoCategory.Definition

open import Theory.Category.Examples

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
  ; whiskerCoher1' = λ {a} {b} {c} {d} {f} {g} {h} {i} {η} → w₁ {a} {b} {c} {d} {f} {g} {h} {i} {η}
  ; whiskerCoher2' = λ {a} {b} {c} {d} {f} {g} {h} {i} {η} → w₂ {a} {b} {c} {d} {f} {g} {h} {i} {η}
  ; whiskerCoher3' = λ {a} {b} {c} {d} {f} {g} {h} {i} {η} → w₃ {a} {b} {c} {d} {f} {g} {h} {i} {η}
  ; whiskerCoher4' = λ {a} {b} {c} {f} {g} {h} {i} {η} {θ} → w₄ {a} {b} {c} {f} {g} {h} {i} {η} {θ}
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
        
        compose : {x y z : Obj (HomCat b c ×C HomCat a b)} 
                → {f : Hom (HomCat b c ×C HomCat a b) x y} {g : Hom (HomCat b c ×C HomCat a b) y z}
                → F₁ (g ∘Comp f) ≡ F₁ g ∘AC F₁ f
        compose {f = refl , refl} {refl , refl} = refl
    
    id₁ : {a : Obj C} → Obj (HomCat a a)
    id₁ {a} = id C {a}
    
    subst₂-elim : {a b : Obj C}
                → {f g : Obj (HomCat a b)}
                → (eq : g ≡ f) 
                → refl {ℓHom} {Hom C a b} {f} ≡ subst₂ (Hom (HomCat a b)) eq eq (refl {ℓHom} {Hom C a b} {g})
    subst₂-elim refl = refl
    
    hIdL₂ : {a b : Obj C} {f g : Obj (HomCat a b)} {η : Hom (HomCat a b) f g}
          → [ comp ]₁ (η , id (HomCat a a)) ≡ subst₂ (Hom (HomCat a b)) (sym (left-id C)) (sym (left-id C)) η
    hIdL₂ {a} {b} {f} {.f} {refl} = subst₂-elim (sym (left-id C))
    
    hIdR₂ : {a b : Obj C} {f g : Obj (HomCat a b)} {η : Hom (HomCat a b) f g} 
          → [ comp ]₁ (id (HomCat b b) , η) ≡ subst₂ (Hom (HomCat a b)) (sym (right-id C)) (sym (right-id C)) η
    hIdR₂ {a} {b} {f} {.f} {refl} = subst₂-elim (sym (right-id C)) 
    
    hAss₂ : {a b c d : Obj C} 
          → {f f' : Obj (HomCat a b)} {g g' : Obj (HomCat b c)} {h h' : Obj (HomCat c d)}
          → {η : Hom (HomCat c d) h h'} {θ : Hom (HomCat b c) g g'} {ι : Hom (HomCat a b) f f'}
          → [ comp ]₁ (η , [ comp ]₁ (θ , ι)) ≡ subst₂ (Hom (HomCat a d)) (sym (assoc C)) (sym (assoc C)) ([ comp ]₁ ([ comp ]₁ (η , θ) , ι))
    hAss₂ {a} {b} {c} {d} {f} {.f} {g} {.g} {h} {.h} {refl} {refl} {refl}= subst₂-elim (sym $ assoc C)
    
    w₁ : {a b c d : Obj C}
       → {f : Obj (HomCat a b)} {g : Obj (HomCat b c)} {h i : Obj (HomCat c d)}
       → {η : Hom (HomCat c d) h i} 
       → [ comp ]₁ (η , id (HomCat a c)) 
       ≡ subst₂ (Hom (HomCat a d)) (sym (assoc C)) (sym (assoc C)) ([ comp ]₁ ([ comp ]₁ (η , id (HomCat b c)) , id (HomCat a b)))
    w₁ {a} {b} {c} {d} {f} {g} {h} {.h} {refl} = subst₂-elim (sym $ assoc C)
    
    w₂ : {a b c d : Obj C} 
       → {f : Obj (HomCat a b)} {g h : Obj (HomCat b c)} {i : Obj (HomCat c d)}
       → {η : Hom (HomCat b c) g h} 
       → Functor.F₁ comp (id (HomCat c d) , Functor.F₁ comp (η , id (HomCat a b))) 
       ≡ subst₂ (Hom (HomCat a d)) (sym (assoc C)) (sym (assoc C)) ([ comp ]₁ ([ comp ]₁ (id (HomCat c d) , η) , id (HomCat a b)))
    w₂ {a} {b} {c} {d} {f} {g} {.g} {i} {refl} = subst₂-elim (sym $ assoc C)
    
    w₃ : {a b c d : Obj C} 
       → {f g : Obj (HomCat a b)} {h : Obj (HomCat b c)} {i : Obj (HomCat c d)}
       → {η : Hom (HomCat a b) f g}
       → Functor.F₁ comp (id (HomCat c d) , Functor.F₁ comp (id (HomCat b c) , η))
       ≡ subst₂ (Hom (HomCat a d)) (sym (assoc C)) (sym (assoc C)) ([ comp ]₁ (id (HomCat b d) , η))
    w₃ {a} {b} {c} {d} {f} {.f} {h} {i} {refl} = subst₂-elim (sym $ assoc C)
    
    w₄ : {a b c : Obj C} 
       → {f g : Obj (HomCat a b)} {h i : Obj (HomCat b c)}
       → {η : Hom (HomCat a b) f g} {θ : Hom (HomCat b c) h i}
       → (HomCat a c ∘ [ comp ]₁ (id (HomCat b c) , η)) ([ comp ]₁ (θ , id (HomCat a b)))
       ≡ (HomCat a c ∘ [ comp ]₁ (θ , id (HomCat a b))) ([ comp ]₁ (id (HomCat b c) , η))
    w₄ {a} {b} {c} {f} {.f} {h} {.h} {refl} {refl} = refl
