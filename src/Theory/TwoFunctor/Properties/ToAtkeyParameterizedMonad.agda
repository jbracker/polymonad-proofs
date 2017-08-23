
-- Stdlib
open import Level renaming ( suc to lsuc ; zero to lzero )
open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Data.Unit
open import Data.Product renaming ( _,_ to _,'_ )
open import Data.Sum
open import Data.Unit
open import Data.Empty
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
open import Theory.Category.Examples.Codiscrete
open import Theory.Functor.Definition
open import Theory.Functor.Composition
open import Theory.Natural.Transformation
open import Theory.Natural.Transformation.Examples
open import Theory.Monad.Atkey
open import Theory.TwoCategory.Definition
open import Theory.TwoCategory.Examples.Functor
open import Theory.TwoCategory.Examples.CodiscreteHomCat
open import Theory.TwoCategory.ExampleProperties
open import Theory.TwoFunctor.Definition
open import Theory.TwoFunctor.ConstZeroCell

open Category
open StrictTwoCategory

module Theory.TwoFunctor.Properties.ToAtkeyParameterizedMonad where

LaxTwoFunctor→AtkeyParameterizedMonad
  : {ℓC₀ ℓC₁ ℓS : Level} 
  → {C : Category {ℓC₀} {ℓC₁}}
  → {S : Set ℓS}
  → (F : ConstLaxTwoFunctor (codiscreteHomCatTwoCategory (codiscreteCategory S)) (Cat {ℓC₀} {ℓC₁}) C)
  → AtkeyParameterizedMonad C (codiscreteCategory S)
LaxTwoFunctor→AtkeyParameterizedMonad {C = C} {ObjS} F = record
  { T = T
  ; η = {!!}
  ; μ  = {!!}
  ; naturalη = {!!}
  ; dinaturalη = {!!}
  ; naturalμ = {!!}
  ; naturalμ₁ = {!!}
  ; naturalμ₂ = {!!}
  ; dinaturalμ = {!!}
  ; assoc = {!!}
  ; left-id = {!!}
  ; right-id = {!!}
  } where
    open ConstLaxTwoFunctor F

    S = codiscreteCategory ObjS
    
    T₀ : Obj ((S op) ×C S ×C C) → Obj C
    T₀ (s₀ , s₁ , a) = [ [ P₁ {s₀} {s₁} ]₀ (lift tt) ]₀ a
    
    T₁ : {a b : Obj ((S op) ×C S ×C C)} → Hom ((S op) ×C S ×C C) a b → Hom C (T₀ a) (T₀ b)
    T₁ {sa₀ , sa₁ , a} {sb₀ , sb₁ , b} (lift tt , lift tt , f) = {!!} -- [ [ P₁ {sa₀} {sa₁} ]₀ {!!} ]₁ f

    {-
    ApplyT : {x y : Obj S} → Hom S x y → Functor C C
    ApplyT {x} {y} _ = functor 
      (λ (c : Obj C) → Functor.F₀ T (y , x , c)) 
      (λ {a : Obj C} {b : Obj C} (g : Hom C a b) → Functor.F₁ T (id S {y} , id S {x} , g))
      (λ {a : Obj C} → Functor.id T)
      (λ {a : Obj C} {b : Obj C} {c : Obj C} {g} {h} → trans (cong₂ (λ X Y → Functor.F₁ T (X , Y , (h ∘C g))) (sym (left-id S {y})) (sym (left-id S {x})))
                                                             (Functor.compose T {y , x , a} {y , x , b} {y , x , c} {id S {y} , id S {x} , g} {id S {y} , id S {x} , h}))
    -}
    T : Functor ((S op) ×C S ×C C) C
    T = functor T₀ T₁ {!!} {!!}
