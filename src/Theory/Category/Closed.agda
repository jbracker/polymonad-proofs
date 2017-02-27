
open import Level renaming ( zero to lzero ; suc to lsuc )

open import Data.Unit
open import Data.Product renaming ( _,_ to _,'_ )

open import Relation.Binary.PropositionalEquality

open import Theory.Category hiding ( category )
open import Theory.Functor
import Theory.Functor.Application
import Theory.Functor.Composition
open import Theory.Natural.Isomorphism
open import Theory.Natural.Transformation
open import Theory.Natural.DinaturalTransformation

module Theory.Category.Closed where

invert : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}}
       → Functor C D → Functor (C op) (D op)
invert (functor F₀ F₁ id compose) = functor F₀ F₁ id compose

invert' : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}}
        → Functor (C op) (D op) → Functor C D
invert' (functor F₀ F₁ id compose) = functor F₀ F₁ id compose


leftId : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}}
       → Functor (⊤-Cat ×C C) D → Functor C D
leftId (functor F₀ F₁ id compose)
  = functor (λ x → F₀ (tt ,' x)) (λ f → F₁ (tt ,' f)) id compose

rightId : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}}
        → Functor (C ×C ⊤-Cat) D → Functor C D
rightId (functor F₀ F₁ id compose)
  = functor (λ x → F₀ (x ,' tt)) (λ f → F₁ (f ,' tt)) id compose

constToAny : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} (C : Category {ℓC₀} {ℓC₁}) {D : Category {ℓD₀} {ℓD₁}}
           → Functor ⊤-Cat D → Functor C D
constToAny C (functor F₀ F₁ id compose) = functor (λ _ → F₀ tt) (λ _ → F₁ tt) id compose

record ClosedCategory {ℓC₀ ℓC₁ : Level} (C : Category {ℓC₀} {ℓC₁}) : Set (lsuc (ℓC₀ ⊔ ℓC₁)) where
  constructor closedCategory

  category = C
  open Category
  
  field
    InternalHom : Functor (C op ×C C) C
    
    I : Obj C
  
  [_,_]₀ : Obj (C op) → Obj C → Obj C
  [_,_]₀ c' c = Functor.F₀ InternalHom (c' ,' c)
  
  [_,_]₁ : {a b : Obj (C op)} {c d : Obj C}
         → Hom (C op) a b → Hom C c d
         → Hom C [ a , c ]₀ [ b , d ]₀
  [_,_]₁ f' f = Functor.F₁ InternalHom (f' ,' f) 
  
  open Theory.Functor.Application.BiFunctor
  
  field
    i : NaturalIsomorphism Id[ C ] ([ I ,-] InternalHom)

    j : (x : Obj C) → Hom C I [ x , x ]₀

    L : (x y z : Obj C) → Hom C [ y , z ]₀ [ [ x , y ]₀ , [ x , z ]₀ ]₀

  -- TODO: Extranaturality
  open Theory.Functor.Composition.BiFunctor
{-
  -- [b,-] → [[a,b],[a,-]] is a natural transformation
  L-natural : (a b : Obj (C op))
            → NaturalTransformation
                ([ b ,-] InternalHom)
                (leftId ([ invert ([ a , b ] InternalHom) , [ a ,-] InternalHom ]∘[ InternalHom ]))
  L-natural a b = naturalTransformation (λ x → L a b x) {!!}

  -- [-,c] → [[a,-],[a,c]] is a natural transformation
  L-natural-op : (a : Obj (C op)) → (c : Obj C)
               → NaturalTransformation
                   ([-, c ] InternalHom)
                   (rightId [ invert ([ a ,-] InternalHom) , [ a , c ] InternalHom ]∘[ InternalHom ])
  L-natural-op a c = naturalTransformation (λ x → L a x c) {!!}
-}
{-
  L-dinatural : (b c : Obj C)
              → DinaturalTransformation
                  (constToAny (C op ×C C) (constFunctor C [ b , c ]₀))
                  [ {![-, b ] InternalHom)!} , {!invert' ([-, c ] InternalHom)!} ]∘[ InternalHom ]
  L-dinatural b c = {!!}
-}
