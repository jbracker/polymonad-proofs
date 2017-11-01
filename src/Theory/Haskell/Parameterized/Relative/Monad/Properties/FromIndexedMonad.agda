 
-- Stdlib
open import Level
open import Function hiding ( id ) renaming ( _∘_ to _∘F_ )
open import Data.Unit
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( refl to hrefl ; sym to hsym ; trans to htrans ; subst to hsubst ; cong to hcong ; cong₂ to hcong₂ )
open ≅-Reasoning 

-- Local
open import Bijection renaming ( refl to brefl ; sym to bsym ; trans to btrans )
open import Congruence
open import Extensionality

open import Theory.Category.Definition
open import Theory.Functor.Definition
open import Theory.Functor.Composition
open import Theory.Natural.Transformation

open import Theory.Haskell.Parameterized.Indexed.Monad
open import Theory.Haskell.Parameterized.Indexed.Monad.Equality

open import Theory.Haskell.Parameterized.Relative.Monad
open import Theory.Haskell.Parameterized.Relative.Monad.Equality

open Category renaming ( right-id to cat-right-id ; left-id to cat-left-id ; id to cid )

module Theory.Haskell.Parameterized.Relative.Monad.Properties.FromIndexedMonad 
  {ℓC₀ ℓC₁ ℓI₀ ℓI₁ : Level} 
  {C : Category {ℓC₀} {ℓC₁}} {I : Category {ℓI₀} {ℓI₁}} where 

private
  _∘C_ = _∘_ C
  _∘I_ = _∘_ I

open Functor
open NaturalTransformation renaming ( η to nat-η )

IndexedMonad→ParameterizedRelativeMonad : (T : {i j : Obj I} → Hom I i j → Functor C C) 
                                        → IndexedMonad I T → ParameterizedRelativeMonad I (λ f → F₀ (T f)) Id[ C ] 
IndexedMonad→ParameterizedRelativeMonad T IM = parameterizedRelativeMonad η' kext {!!} {!!} {!!}
  where
    open IndexedMonad IM
    
    η' : (i : Obj I) {a : Obj C} → Hom C a (F₀ (T (cid I {i})) a)
    η' i {a} = nat-η (η i) a
    
    kext : {i j k : Obj I} (f : Hom I i j) (g : Hom I j k) {a b : Obj C} 
         → Hom C a (F₀ (T g) b) → Hom C (F₀ (T f) a) (F₀ (T (g ∘I f)) b)
    kext {i} {j} {k} fI gI {a} {b} f = nat-η (μ fI gI) b ∘C [ T fI ]₁ f
