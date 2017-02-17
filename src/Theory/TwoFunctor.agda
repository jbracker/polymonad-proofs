 
module Theory.TwoFunctor where

-- Stdlib
open import Level renaming ( suc to lsuc ; zero to lzero )
open import Function hiding ( id ) renaming ( _∘_ to _∘F_ )
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Local
open import Utilities
open import Theory.Category
open import Theory.Functor
open import Theory.NaturalTransformation
open import Theory.Examples.Functor
open import Theory.TwoCategory

-------------------------------------------------------------------------------
-- Definition of 2-Functors
-------------------------------------------------------------------------------

open Category hiding ( idL ; idR ; assoc ) renaming ( id to idC )
open StrictTwoCategory

record LaxTwoFunctor {ℓC₀ ℓC₁ ℓC₂ ℓD₀ ℓD₁ ℓD₂ : Level} 
                     (C : StrictTwoCategory {ℓC₀} {ℓC₁} {ℓC₂}) 
                     (D : StrictTwoCategory {ℓD₀} {ℓD₁} {ℓD₂}) 
                     : Set (lsuc (ℓC₀ ⊔ ℓC₁ ⊔ ℓC₂ ⊔ ℓD₀ ⊔ ℓD₁ ⊔ ℓD₂)) where
  private
    _▷D_ = _▷_ D
    _▷C_ = _▷_ C

    _◁D_ = _◁_ D
    _◁C_ = _◁_ C
    
    _∘Dₕ_ = _∘ₕ_ D
    _∘Cₕ_ = _∘ₕ_ C

    _∘Dₕ₂_ = _∘ₕ₂_ D

    _∘Dᵥ_ = _∘ᵥ_ D
    _∘Cᵥ_ = _∘ᵥ_ C

    id₁D = id₁ D

  field
    -- Names and structure base on: https://ncatlab.org/nlab/show/pseudofunctor
    -- Of course, adapted to lax 2-functors.
    
    -- P_{x}
    P₀ : Cell₀ C → Cell₀ D
    -- P_{x,y}
    P₁ : {x y : Cell₀ C} → Functor (HomCat C x y) (HomCat D (P₀ x) (P₀ y))
    
    -- P_{id_x}
    η : {x : Cell₀ C}
      → Cell₂ D (id₁ D {P₀ x}) ([ P₁ {x} {x} ]₀ (id₁ C {x}))

    -- P_{x,y,z}
    μ : {x y z : Cell₀ C} {f : Cell₁ C x y} {g : Cell₁ C y z}
         -- (F₁ g ∘ F₁ f) ∼ F₁ (g ∘ f)
         → Cell₂ D ([ P₁ ]₀ g  ∘Dₕ  [ P₁ ]₀ f) ([ P₁ ]₀ (g ∘Cₕ f))
    
    laxFunId₁ : {x y : Cell₀ C} {f : Cell₁ C x y} 
              → ([ P₁ {x} {y} ]₁ (λ' C f)) 
            ∘Dᵥ ( (μ {x} {x} {y} {id₁ C {x}} {f}) 
            ∘Dᵥ   (id₂ D {f = [ P₁ {x} {y} ]₀ f} ∘Dₕ₂ η {x}) )
              ≡ λ' D ([ P₁ {x} {y} ]₀ f)
    
    laxFunId₂ : {x y : Cell₀ C} {f : Cell₁ C x y} 
              → ([ P₁ {x} {y} ]₁ (ρ C f)) 
            ∘Dᵥ ( (μ {x} {y} {y} {f} {id₁ C {y}}) 
            ∘Dᵥ   (η {y} ∘Dₕ₂ id₂ D {f = [ P₁ {x} {y} ]₀ f}) ) 
              ≡ ρ D ([ P₁ {x} {y} ]₀ f)

    laxFunAssoc : {w x y z : Cell₀ C} {f : Cell₁ C w x} {g : Cell₁ C x y} {h : Cell₁ C y z}
               → ([ P₁ {w} {z} ]₁ (α C f g h)) 
             ∘Dᵥ ( (μ {w} {y} {z} {g ∘Cₕ f} {h}) 
             ∘Dᵥ   (id₂ D {P₀ y} {P₀ z} {[ P₁ {y} {z} ]₀ h} ∘Dₕ₂ μ {w} {x} {y} {f} {g}) ) 
               ≡ μ {w} {x} {z} {f} {h ∘Cₕ g} 
             ∘Dᵥ ( (μ {x} {y} {z} {g} {h} ∘Dₕ₂ id₂ D {P₀ w} {P₀ x} {[ P₁ {w} {x} ]₀ f}) 
             ∘Dᵥ   (α D ([ P₁ {w} {x} ]₀ f) ([ P₁ {x} {y} ]₀ g) ([ P₁ {y} {z} ]₀ h)) )
    
-- horizontal composite:  ∘  =   _∘ₕ_  = flip (;)
-- vertical composite:    •  =   _∘ᵥ_

-------------------------------------------------------------------------------
-- Creating a Lax 2-Functor from a Functor.
-------------------------------------------------------------------------------

Functor→LaxTwoFunctor : ∀ {ℓ₀ ℓ₁} {C D : Category {ℓ₀} {ℓ₁}} 
                      → Functor C D → LaxTwoFunctor (Category→StrictTwoCategory C) (Category→StrictTwoCategory D)
Functor→LaxTwoFunctor {ℓ₀} {ℓ₁} {C} {D} F = record
  { P₀ = P₀
  ; P₁ = P₁
  ; η = tt
  ; μ = tt
  ; laxFunId₁ = refl
  ; laxFunId₂ = refl
  ; laxFunAssoc = refl
  } where
      C' = Category→StrictTwoCategory C
      D' = Category→StrictTwoCategory D
      
      P₀ : Cell₀ C' → Cell₀ D'
      P₀ a = [ F ]₀ a
      
      P₁ : {x y : Cell₀ C'} → Functor (HomCat C' x y) (HomCat D' (P₀ x) (P₀ y))
      P₁ {x} {y} = record 
        { F₀ = F₀
        ; F₁ = λ {a} {b} → F₁ {a} {b}
        ; id = refl
        ; compose = refl
        } where
          F₀ : Obj (HomCat C' x y) → Obj (HomCat D' (P₀ x) (P₀ y))
          F₀ f = [ F ]₁ f
          
          F₁ : {a b : Obj (HomCat C' x y)} 
             → Hom (HomCat C' x y) a b → Hom (HomCat D' (P₀ x) (P₀ y)) (F₀ a) (F₀ b)
          F₁ f = tt
{-
LaxTwoFunctor→Functor : ∀ {ℓC₀ ℓC₁ ℓC₂ ℓD₀ ℓD₁ ℓD₂} {C : StrictTwoCategory {ℓC₀} {ℓC₁} {ℓC₂}} {D : StrictTwoCategory {ℓD₀} {ℓD₁} {ℓD₂}}
                      → LaxTwoFunctor C D → Functor (StrictTwoCategory→Category C) (StrictTwoCategory→Category D)
LaxTwoFunctor→Functor LaxF = record 
  { F₀ = LaxTwoFunctor.P₀ LaxF
  ; F₁ = λ x → [ LaxTwoFunctor.P₁ LaxF ]₀ x
  ; id = {!!}
  ; dist = {!!}
  }

Kind = Set₁

Type : Kind
Type = Set₀

Hask : Category {lsuc lzero} {lzero}
Hask = record
  { Obj = Type
  ; Hom = λ a b → (a → b)
  ; _∘_ = λ g f x → g (f x)
  ; id = λ x → x
  ; assoc = refl
  ; idL = refl
  ; idR = refl
  }
-}
{-
q : StrictTwoCategory
q = record
  { Cell₀ = Cell₀'
  ; HomCat = HomCat'
  ; comp = λ {a} {b} {c} → comp' {a} {b} {c}
  ; id₁ = Id[ Hask ]
  ; horizontalIdR₁ = {!!}
  ; horizontalIdR₂ = {!!}
  ; horizontalIdL₁ = {!!}
  ; horizontalIdL₂ = {!!}
  ; horizontalAssoc₁ = {!!}
  ; horizontalAssoc₂ = {!!}
  ; whiskerCoher1' = {!!}
  ; whiskerCoher2' = {!!}
  ; whiskerCoher3' = {!!}
  ; whiskerCoher4' = {!!}
  } where
    Cell₀' = Type
    
    Cell₁' : Cell₀' → Cell₀' → Kind
    Cell₁' a b = Functor Hask Hask
    
    Cell₂' : {a b : Cell₀'} → Cell₁' a b → Cell₁' a b → Kind
    Cell₂' {a} {b} F G = (A : Type) → ([ F ]₀ A → [ G ]₀ A)
    
    _∘'_ : ∀ {a b} {x y z : Cell₁' a b} → Cell₂' {a} {b} y z → Cell₂' {a} {b} x y → Cell₂' {a} {b} x z
    _∘'_ {x} {y} {a} {b} {c} g f h m = g h (f h m)
    
    idHomCat : {F : Functor Hask Hask} → (A : Type) → ([ F ]₀ A → [ F ]₀ A)
    idHomCat A f = f

    HomCat' : Cell₀' → Cell₀' → Category
    HomCat' a b = record
      { Obj = Cell₁' a b
      ; Hom = Cell₂' {a} {b}
      ; _∘_ = λ {x} {y} {z} → _∘'_ {a} {b} {x} {y} {z}
      ; id = λ {F} → idHomCat {F}
      ; assoc = refl
      ; idL = refl
      ; idR = refl
      }
    
    fmap : {A B : Type} {G : Functor Hask Hask} → (A → B) → ([ G ]₀ A) → [ G ]₀ B
    fmap {G = functor F₀ F₁ _ _} f m = F₁ f m
    
    comp' : {a b c : Cell₀'} → Functor (HomCat' b c ×C HomCat' a b) (HomCat' a c)
    comp' {a} {b} {c} = record 
      { F₀ = F₀ 
      ; F₁ = λ {x} {y} → F₁ {x} {y}
      ; id = λ {x} → id {x}
      ; dist = dist 
      } where
        F₀ : Obj (HomCat' b c ×C HomCat' a b) → Obj (HomCat' a c)
        F₀ (G , F) = [ G ]∘[ F ]

        F₁ : {x y : Obj (HomCat' b c ×C HomCat' a b)} 
           → Hom (HomCat' b c ×C HomCat' a b) x y
           → Hom (HomCat' a c) (F₀ x) (F₀ y)
        F₁ {G , F} {G' , F'} (g , f) A GFA = g ([ F' ]₀ A) (fmap {[ F ]₀ A} {[ F' ]₀ A} {G} (f A) GFA)
        
        id : {x : Obj (HomCat' b c ×C HomCat' a b)} 
           → F₁ {x} {x} (idC (HomCat' b c ×C HomCat' a b) {a = x}) ≡ idC (HomCat' a c) {a = F₀ x}
        id {G , F} = begin
          F₁ {x} {x} (idC (HomCat' b c ×C HomCat' a b) {x}) 
            ≡⟨ refl ⟩
          F₁ {x} {x} (idHomCat {G} , idHomCat {F}) 
            ≡⟨ refl ⟩
          (λ A GFA → idHomCat {G} ([ F ]₀ A) (fmap {[ F ]₀ A} {[ F ]₀ A} {G} (idHomCat {F} A) GFA))
            ≡⟨ refl ⟩
          (λ A GFA → fmap {[ F ]₀ A} {[ F ]₀ A} {G} (idHomCat {F} A) GFA)
            ≡⟨ refl ⟩
          (λ A GFA → Functor.F₁ G (idHomCat {F} A) GFA)
            ≡⟨ funExt (λ A → Functor.id G) ⟩
          (λ A GFA → GFA)
            ≡⟨ refl ⟩
          idC (HomCat' a c) {F₀ x} ∎
          where 
            x = G , F
        
        dist : {x y z : Obj (HomCat' b c ×C HomCat' a b)} 
             → {f : Hom (HomCat' b c ×C HomCat' a b) x y}
             → {g : Hom (HomCat' b c ×C HomCat' a b) y z}
             → F₁ {x} {z} (_∘_ (HomCat' b c ×C HomCat' a b) {x} {y} {z} g f) ≡ _∘_ (HomCat' a c) {F₀ x} {F₀ y} {F₀ z} (F₁ {y} {z} g) (F₁ {x} {y} f)
        dist {G , F} {G' , F'} {G'' , F''} {f' , f''} {g' , g''} = begin
          F₁ {x} {z} (g ∘bc×ab f) 
            ≡⟨ refl ⟩
          F₁ {G , F} {G'' , F''} (g' ∘bc f' , g'' ∘ab f'') 
            ≡⟨ refl ⟩ 
          (λ A GFA → (g' ∘bc f') ([ F'' ]₀ A) (Functor.F₁ G ((g'' ∘ab f'') A) GFA))
            ≡⟨ refl ⟩ 
          (λ A GFA → (λ A GFA → g' A (f' A GFA)) ([ F'' ]₀ A) (Functor.F₁ G ((λ A GFA → g'' A (f'' A GFA)) A) GFA))
            ≡⟨ refl ⟩ 
          (λ A GFA → g' ([ F'' ]₀ A) (f' ([ F'' ]₀ A) (Functor.F₁ G (λ GFA → g'' A (f'' A GFA)) GFA)) )
            ≡⟨ funExt (λ A → funExt (λ GFA → cong (λ X → g' ([ F'' ]₀ A) (f' ([ F'' ]₀ A) (X GFA))) (Functor.dist G))) ⟩
          (λ A GFA → g' ([ F'' ]₀ A) (f' ([ F'' ]₀ A) (Functor.F₁ G (g'' A) (Functor.F₁ G (f'' A) GFA))) )
            ≡⟨ {!!} ⟩
          (λ A GFA → g' ([ F'' ]₀ A) (Functor.F₁ G' (g'' A) (f' ([ F' ]₀ A) (Functor.F₁ G (f'' A) GFA))) )
            ≡⟨ refl ⟩
          (λ A GFA → (λ A GFA → g' ([ F'' ]₀ A) (Functor.F₁ G' (g'' A) GFA)) A ((λ A GFA → f' ([ F' ]₀ A) (Functor.F₁ G (f'' A) GFA)) A GFA))
            ≡⟨ refl ⟩
          (λ A GFA → g' ([ F'' ]₀ A) (Functor.F₁ G' (g'' A) GFA)) ∘ac (λ A GFA → f' ([ F' ]₀ A) (Functor.F₁ G (f'' A) GFA))
            ≡⟨ refl ⟩
          (F₁ {y} {z} g) ∘ac (F₁ {x} {y} f) ∎
          where
-- dist : ∀ {a b c} {f : Hom C a b} {g : Hom C b c}   → F₁ (_∘_ C g f) ≡ _∘_ D (F₁ g) (F₁ f)

            x = G , F
            y = G' , F'
            z = G'' , F''
            f = f' , f''
            g = g' , g''
            _∘ab_ = Category._∘_ (HomCat' a b) {F} {F'} {F''}
            _∘bc_ = Category._∘_ (HomCat' b c) {G} {G'} {G''}
            _∘bc×ab_ = Category._∘_ (HomCat' b c ×C HomCat' a b) {x} {y} {z}
            _∘ac_ = Category._∘_ (HomCat' a c) {F₀ x} {F₀ y} {F₀ z}

p : ∀ {ℓ₀ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅} 
  → (C : StrictTwoCategory {ℓ₀} {ℓ₁} {ℓ₂}) → (D : StrictTwoCategory {ℓ₃} {ℓ₄} {ℓ₅})
  → LaxTwoFunctor C D
p = {!!}
-}
