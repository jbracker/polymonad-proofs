
open import Level
open import Function hiding ( id ; _∘_ )

open import Data.Unit

open import Relation.Binary.PropositionalEquality

open import Theory.Category
open import Theory.Category.Examples
open import Theory.Category.Closed
open import Theory.Category.Closed.Examples
open import Theory.Functor
open import Theory.Functor.Closed
open import Theory.Natural.Transformation
open import Theory.Natural.Isomorphism

open import Theory.Yoneda.HomFunctor
open import Theory.Yoneda.Bijection
open import Theory.Yoneda.Embedding
open import Theory.Yoneda.Isomorphism

module Theory.Haskell.Applicative {ℓC₀ ℓC₁ : Level} {C' : Category {ℓC₀} {ℓC₁}} {C : ClosedCategory C'} (F : ClosedFunctor C (setClosedCategory {ℓC₁})) where

open ClosedCategory
open ClosedFunctor F renaming ( F to F' )


private
  SetCat = setClosedCategory {ℓC₁}
  SetCat' = setCategory {ℓC₁}

  _∘C_ = _∘_ C
  
  C[_,_]₀ = [_,_]₀ C
  C[_,_]₁ = [_,_]₁ C

ap : {a b : Obj C} → (F₀ C[ a , b ]₀) → (Hom SetCat (F₀ a) (F₀ b))
ap {a} {b} = F̂ a b



ap-inv : {a b : Obj C} → (F₀ a → F₀ b) → (F₀ C[ a , b ]₀)
ap-inv {a} {b} = F̂-inv a b 

cnst : (A : Obj SetCat) → A → (Hom SetCat (I SetCat) A)
cnst A a = i SetCat A a

p : (A : Obj SetCat) → (a : A) → cnst A a ≡ (λ _ → a) 
p A a = refl

unit : (I SetCat) → (F₀ (I C))
unit = F⁰

p1 : (a : Obj C) → Hom SetCat (F₀ C[ I C , a ]₀) (F₀ a)
p1 a f = ap f (F⁰ (lift tt))

{-
p2 : (a : Obj C) → F₀ C[ I C , a ]₀
p2 a = ap-inv {!!}

pure : Hom SetCat (I SetCat) {!F⁰ (I C)!}
pure = {!!} --ap (p2 a) (F⁰ (lift tt))

q0 : F₀ (I C)
q0 = F⁰ (lift tt)

q1 : {a : Obj C} → F₀ a → F₀ C[ I C , a ]₀
q1 {a} = F₁ (i C a)

-- f () → (forall a. (() -> a) -> f a)

q2 : F₀ (I C) → (∀ {a : Obj C} → (Hom C (I C) a) → F₀ a)
q2 α {a} f = F₁ f α

q'2 : F₀ (I C) → (∀ {a : Obj C} → (F₀ C[ I C , a ]₀) → F₀ a)
q'2 α {a} f = ap f α

-- (forall a. (() -> a) -> f a) → f ()

q2' : (∀ {a : Obj C} → (Hom C (I C) a) → F₀ a) → F₀ (I C)
q2' f = f {I C} (Category.id C')

q'2' : (∀ {a : Obj C} → F₀ C[ I C , a ]₀ → F₀ a) → F₀ (I C)
q'2' f = f (ap-inv (Category.id SetCat'))

-- (∀ a. (() -> a) -> f a) → (∀ a. a -> f a)

h3 : (a : Obj C) → Hom C (I C) C[ I C , a ]₀
h3 a = {!!}

h2 : (a : Obj C) → Hom C (I C) a
h2 a = i-inv C a ∘C h3 a

q3 : (∀ {a : Obj C} → Hom C (I C) a → F₀ a) → (∀ (a : Obj C) → F₀ a)
q3 f a = f (h2 a)

h0 : (a : Obj C) → F₀ C[ I C , a ]₀
h0 a = {!!}

h1 : {a : Obj C} → F₀ C[ I C , a ]₀ → F₀ a
h1 {a} f = ap f (F⁰ (lift tt))

h1' : {a : Obj C} → F₀ a → F₀ C[ I C , a ]₀
h1' {a} fa = ap-inv (λ _ → fa)

q'3 : (∀ {a : Obj C} → F₀ C[ I C , a ]₀ → F₀ a) → (∀ (a : Obj C) → F₀ a)
q'3 f a = f {!F₀!}

-- (∀ a. a -> f a) → (∀ a. (() -> a) -> f a)
-}
