
-- Stdlib
open import Level
open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Data.Unit
open import Data.Product renaming ( _,_ to _,'_ )
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality 
  renaming ( refl to hrefl; sym to hsym ; trans to htrans ; cong to hcong ; cong₂ to hcong₂ ; subst to hsubst ; subst₂ to hsubst₂ ; proof-irrelevance to hproof-irrelevance )
open ≡-Reasoning hiding ( _≅⟨_⟩_ )
-- open ≅-Reasoning hiding ( _≡⟨_⟩_ ) renaming ( begin_ to hbegin_ ; _∎ to _∎h)

-- Local
open import Extensionality
open import Utilities
open import Haskell
open import Theory.Triple
open import Theory.Category.Definition
open import Theory.Category.Examples.Functor
open import Theory.Functor.Definition
open import Theory.Functor.Composition
open import Theory.Natural.Transformation
open import Theory.Natural.Transformation.Examples
open import Theory.Monad.Relative
open import Theory.TwoCategory.Definition
open import Theory.TwoCategory.Examples.Functor
open import Theory.TwoCategory.Examples.DiscreteHomCat
open import Theory.TwoFunctor.Definition


module Theory.TwoFunctor.Properties.FromRelativeMonad where

data Binary : Set where
 one : Binary
 two : Binary

RelIxCat : Category
RelIxCat = record
  { Obj = Binary
  ; Hom = BinHom 
  ; _∘_ = λ {x y z} → comp {x} {y} {z}
  ; id = λ {x} → id' {x}
  ; assoc = λ {a b c d} {f} {g} {h} → assoc {a} {b} {c} {d} {f} {g} {h}
  ; left-id = λ {a b} {f} → left-id {a} {b} {f}
  ; right-id = λ {a b} {f} → right-id {a} {b} {f}
  } where
    BinHom : Binary → Binary → Set zero
    BinHom one one = ⊤
    BinHom one two = Binary
    BinHom two one = ⊥
    BinHom two two = ⊤
    
    comp : {a b c : Binary} → BinHom b c → BinHom a b → BinHom a c
    comp {one} {one} {one} tt tt = tt
    comp {one} {one} {two} g  tt = g
    comp {one} {two} {one} () _
    comp {one} {two} {two} tt f  = f 
    comp {two} {one} {one} tt ()
    comp {two} {one} {two} _  ()
    comp {two} {two} {one} () _
    comp {two} {two} {two} tt tt = tt
    
    id' : {a : Binary} → BinHom a a
    id' {one} = tt
    id' {two} = tt
    
    assoc : {a b c d : Binary} {f : BinHom a b} {g : BinHom b c} {h : BinHom c d} 
          → comp {a} {c} {d} h (comp {a} {b} {c} g f) ≡ comp {a} {b} {d} (comp {b} {c} {d} h g) f
    assoc {one} {one} {one} {one} = refl
    assoc {one} {one} {one} {two} = refl
    assoc {one} {one} {two} {one} {h = ()}
    assoc {one} {one} {two} {two} = refl
    assoc {one} {two} {one} {g = ()}
    assoc {one} {two} {two} {one} {h = ()}
    assoc {one} {two} {two} {two} = refl
    assoc {two} {one} {f = ()}
    assoc {two} {two} {one} {g = ()}
    assoc {two} {two} {two} {one} {h = ()}
    assoc {two} {two} {two} {two} = refl
    
    left-id : {a b : Binary} {f : BinHom a b} → comp {a} {a} {b} f (id' {a}) ≡ f
    left-id {one} {one} = refl
    left-id {one} {two} = refl
    left-id {two} {one} {()}
    left-id {two} {two} = refl

    right-id : {a b : Binary} {f : BinHom a b} → comp {a} {b} {b} (id' {b}) f ≡ f
    right-id {one} {one} = refl
    right-id {one} {two} = refl
    right-id {two} {one} {()}
    right-id {two} {two} = refl
    
open Category
open NaturalTransformation renaming ( η to nat-η )
open StrictTwoCategory

-- TODO: This does not seem to work...
RelativeMonad→LaxTwoFunctor 
  : {ℓ₀ ℓ₁ : Level} 
  → {C : Category {ℓ₀} {ℓ₁}}
  → {D : Category {ℓ₀} {ℓ₁}}
  → {T : Obj C → Obj D}
  → {J : Functor C D}
  → RelativeMonad T J 
  → LaxTwoFunctor (discreteHomCatTwoCategory RelIxCat) (Cat {ℓ₀} {ℓ₁})
RelativeMonad→LaxTwoFunctor {ℓ₀} {ℓ₁} {C} {D} {T} {J} M = record
  { P₀ = P₀
  ; P₁ = λ {x} {y} → P₁ {x} {y}
  ; η = {!!} -- λ {x} → η {x}
  ; μ = {!!} -- λ {x y z} {f} {g} → μ {x} {y} {z} {f} {g}
  ; laxFunId₁ = {!!}
  ; laxFunId₂ = {!!}
  ; laxFunAssoc = {!!}
  } where
    Cat' = functorTwoCategory {ℓ₀} {ℓ₁}
    RelIxCat₂ = discreteHomCatTwoCategory RelIxCat
    
    P₀ : Binary → Category {ℓ₀} {ℓ₁}
    P₀ one = C
    P₀ two = D

    EmptyFunctor : Functor (HomCat RelIxCat₂ two one) (HomCat Cat' D C)
    EmptyFunctor = functor F₀ F₁ fun-id fun-compose
      where
        F₀ : Obj (HomCat RelIxCat₂ two one) → Obj (HomCat Cat' D C)
        F₀ ()
        
        F₁ : {a b : Obj (HomCat RelIxCat₂ two one)} → Hom (HomCat RelIxCat₂ two one) a b → Hom (HomCat Cat' D C) (F₀ a) (F₀ b)
        F₁ {()} {()}
        
        fun-id : {a : Obj (HomCat RelIxCat₂ two one)} → F₁ (id (HomCat RelIxCat₂ two one) {a}) ≡ id (HomCat Cat' D C) {F₀ a}
        fun-id {()}
        
        fun-compose : {a b c : Obj (HomCat RelIxCat₂ two one)} {f : Hom (HomCat RelIxCat₂ two one) a b} {g : Hom (HomCat RelIxCat₂ two one) b c}
                    → F₁ (Category._∘_ (HomCat RelIxCat₂ two one) g f) ≡ ⟨ F₁ g ⟩∘ᵥ⟨ F₁ f ⟩
        fun-compose {()} {()} {()}
    
    P₁ : {x y : Binary} → Functor (HomCat RelIxCat₂ x y) (HomCat Cat' (P₀ x) (P₀ y))
    P₁ {one} {one} = functor (λ _ → Id[ C ]) (λ _ → Id⟨ Id[ C ] ⟩) refl (natural-transformation-eq (fun-ext (λ x → sym $ Category.right-id C)))
    P₁ {two} {two} = functor (λ _ → Id[ D ]) (λ _ → Id⟨ Id[ D ] ⟩) refl (natural-transformation-eq (fun-ext (λ x → sym $ Category.right-id D)))
    P₁ {two} {one} = EmptyFunctor
    P₁ {one} {two} = functor F₀ F₁ (λ {a} → fun-id {a}) (λ {a b c} {f} {g} → fun-compose {a} {b} {c} {f} {g})
      where
        F₀ : Obj (HomCat RelIxCat₂ one two) → Obj (HomCat functorTwoCategory C D)
        F₀ one = J
        F₀ two = RelativeMonad.FunctorT M
        
        F₁ : {a b : Obj (HomCat RelIxCat₂ one two)} → Hom (HomCat RelIxCat₂ one two) a b → Hom (HomCat Cat' C D) (F₀ a) (F₀ b)
        F₁ {one} {.one} refl = Id⟨ J ⟩
        F₁ {two} {.two} refl = Id⟨ RelativeMonad.FunctorT M ⟩
        
        _∘D_ = Category._∘_ D
        
        fun-id : {a : Obj (HomCat RelIxCat₂ one two)} → F₁ {a} {a} (id (HomCat RelIxCat₂ one two)) ≡ id (HomCat Cat' C D)
        fun-id {one} = refl
        fun-id {two} = refl
        
        fun-compose : {a b c : Obj (HomCat RelIxCat₂ one two)} 
                    → {f : Hom (HomCat RelIxCat₂ one two) a b} {g : Hom (HomCat RelIxCat₂ one two) b c}
                    → F₁ (Category._∘_ (HomCat RelIxCat₂ one two) g f) ≡ ⟨ F₁ g ⟩∘ᵥ⟨ F₁ f ⟩
        fun-compose {one} {._} {._} {refl} {refl} = natural-transformation-eq (fun-ext (λ x → sym (right-id D)))
        fun-compose {two} {._} {._} {refl} {refl} = natural-transformation-eq (fun-ext (λ x → sym (right-id D)))
    
    
    η : {x : Cell₀ RelIxCat₂} → Cell₂ Cat' (id₁ Cat') ([ P₁ {x} {x} ]₀ (id₁ RelIxCat₂ {x}))
    η {one} = Id⟨ Id[ C ] ⟩
    η {two} = naturalTransformation (λ x → {!!}) {!!}
    {-
    μ : {x y z : Cell₀ BinCat₂} {f : Cell₁ BinCat₂ x y} {g : Cell₁ BinCat₂ y z}
      → Cell₂ Cat' ([ [ P₁ {y} {z} ]₀ g ]∘[ [ P₁ {x} {y} ]₀ f ]) ([ P₁ {x} {z} ]₀ (_∘ₕ_ BinCat₂ {a = x} {y} {z} g f))
    μ {true}  {true}  {true}  {tt} {tt} = Id⟨ Id[ D ] ⟩
    μ {true}  {true}  {false} {tt} {()}
    μ {true}  {false} {_}     {()} {_}
    μ {false} {true}  {true}  {tt} {tt} = naturalTransformation η' {!!}
      where
        η' : (x : Obj C) → Hom D ([ [ P₁ {false} {true} ]₀ tt ]₀ x) ([ [ P₁ {false} {true} ]₀ tt ]₀ x)
        η' x = id D {[ [ P₁ {false} {true} ]₀ tt ]₀ x}
    μ {false} {true}  {false} {tt} {()}
    μ {false} {false} {true}  {tt} {tt} = naturalTransformation {!!} {!!}
    μ {false} {false} {false} {tt} {tt} = Id⟨ Id[ C ] ⟩

-}
