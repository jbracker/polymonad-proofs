
open import Level
open import Function renaming ( _∘_ to _∘F_ ; id to idF )

open import Data.Product
open import Data.Unit

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( refl to hrefl ; sym to hsym ; cong to hcong ; cong₂ to hcong₂ )
open ≅-Reasoning

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
  ; left-id = left-id C
  ; horizontal-left-id = h-left-id
  ; right-id = right-id C
  ; horizontal-right-id = h-right-id
  ; assoc = assoc C
  ; horizontal-assoc = h-assoc
  } where
    open Category

    _∘C_ = _∘_ C

    HomCat : Obj C → Obj C → Category
    HomCat a b = codiscreteCategory (Hom C a b)

    comp : {a b c : Obj C} → Functor (HomCat b c ×C HomCat a b) (HomCat a c)
    comp {a} {b} {c} = functor F₀ (λ {x y} → F₁ {x} {y}) F-id (λ {x y z} → compose {x} {y} {z})
      where
        _∘Comp_ = _∘_ (HomCat b c ×C HomCat a b)
        _∘AC_ = _∘_ (HomCat a c)
        
        F₀ : Obj (HomCat b c ×C HomCat a b) → Obj (HomCat a c)
        F₀ (x , y) = x ∘C y
        
        F₁ : {x y : Obj (HomCat b c ×C HomCat a b)} → Hom (HomCat b c ×C HomCat a b) x y → Hom (HomCat a c) (F₀ x) (F₀ y)
        F₁ {a , b} {c , d} (codisc .a .c , codisc .b .d) = codisc (a ∘C b) (c ∘C d)

        abstract
          F-id : {x : Obj (HomCat b c ×C HomCat a b)} → F₁ (id (HomCat b c ×C HomCat a b) {x}) ≡ id (HomCat a c)
          F-id {x} = refl
        
        abstract
          compose : {x y z : Obj (HomCat b c ×C HomCat a b)}
                  → {f : Hom (HomCat b c ×C HomCat a b) x y} {g : Hom (HomCat b c ×C HomCat a b) y z}
                  → F₁ (g ∘Comp f) ≡ F₁ g ∘AC F₁ f
          compose {x₀ , x₁} {y₀ , y₁} {z₀ , z₁} {codisc .x₀ .y₀ , codisc .x₁ .y₁} {codisc .y₀ .z₀ , codisc .y₁ .z₁} = refl
    
    id₁ : {a : Obj C} → Obj (HomCat a a)
    id₁ {a} = id C {a}

    h-left-id : {a b : Obj C} {f g : Obj (HomCat a b)} {η : Hom (HomCat a b) f g}
              → [ comp ]₁ (η , id (HomCat a a)) ≅ η
    h-left-id {a} {b} {x} {y} {codisc .x .y} = begin
      [ comp ]₁ (codisc x y , codisc (id C {a}) (id C {a})) 
        ≅⟨ hrefl ⟩
      codisc (x ∘C id C {a}) (y ∘C id C {a}) 
        ≅⟨ hcong₂ codisc (≡-to-≅ (left-id C)) (≡-to-≅ (left-id C)) ⟩
      codisc x y ∎
    
    h-right-id : {a b : Obj C} {f g : Obj (HomCat a b)} {η : Hom (HomCat a b) f g}
               → [ comp ]₁ (id (HomCat b b) , η) ≅ η
    h-right-id {a} {b} {x} {y} {codisc .x .y} = hcong₂ codisc (≡-to-≅ (right-id C)) (≡-to-≅ (right-id C))
    
    h-assoc : {a b c d : Obj C} {f f' : Obj (HomCat a b)}
            → {g g' : Obj (HomCat b c)} {h h' : Obj (HomCat c d)}
            → {η : Hom (HomCat c d) h h'} {θ : Hom (HomCat b c) g g'} {ι : Hom (HomCat a b) f f'}
            → [ comp ]₁ (η , [ comp ]₁ (θ , ι)) ≅ [ comp ]₁ ([ comp ]₁ (η , θ) , ι)
    h-assoc {a} {b} {c} {d} {f} {f'} {g} {g'} {h} {h'} {codisc .h .h'} {codisc .g .g'} {codisc .f .f'} = hcong₂ codisc (≡-to-≅ $ assoc C) (≡-to-≅ $ assoc C)
