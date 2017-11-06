
open import Level

open import Data.Product

open import Relation.Binary.PropositionalEquality

open import Bijection renaming ( refl to brefl ; sym to bsym ; trans to btrans )

open import Theory.Triple renaming ( _,_,_ to _,'_,'_ )
open import Theory.Category.Definition
open import Theory.Category.Examples.Discrete renaming ( discreteCategory to Disc )
open import Theory.Category.Examples.Codiscrete renaming ( codiscreteCategory to Codisc )
open import Theory.Functor.Definition
open import Theory.Natural.Transformation
open import Theory.Monad.Atkey
open import Theory.Haskell.Parameterized.Indexed.Monad

module Theory.Haskell.Parameterized.Indexed.Monad.Properties.ToAtkeyParameterizedMonad
  {ℓC₀ ℓC₁ ℓI : Level}
  {C : Category {ℓC₀} {ℓC₁}} {I : Set ℓI}
  where

open Category
open Triple renaming ( proj₁ to p₁ ; proj₂ to p₂ ; proj₃ to p₃ )

IndexedMonad→AtkeyParameterizedMonad 
  : (Σ ({i j : I} → Hom (Codisc I) i j → Functor C C) (IndexedMonad (Codisc I))) 
  → AtkeyParameterizedMonad C (Disc I)
IndexedMonad→AtkeyParameterizedMonad (T , IxMonad) = atkey-parameterized-monad F η μ {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!}
  where
    open NaturalTransformation renaming ( η to nat-η )
    open IndexedMonad IxMonad renaming ( functor to ix-functor ; η to ix-η ; μ to ix-μ )
    
    F : Functor ((Disc I) op ×C Disc I ×C C) C
    F = functor F₀ F₁ F-id (λ {a b c} {f} {g} → F-compose {a} {b} {c} {f} {g})
      where
        F₀ : Obj ((Disc I op) ×C Disc I ×C C) → Obj C
        F₀ (i ,' j ,' a) = Functor.F₀ (T (codisc j i)) a
        
        F₁ : {a b : Obj ((Disc I op) ×C Disc I ×C C)} → Hom ((Disc I op) ×C Disc I ×C C) a b → Hom C (F₀ a) (F₀ b)
        F₁ {i ,' j ,' a} {.i ,' .j ,' b} (refl ,' refl ,' f) = Functor.F₁ (T (codisc j i)) f
        
        F-id : {a : Obj ((Disc I op) ×C Disc I ×C C)} → Functor.F₁ (T (codisc (p₁ a) (p₂ a))) (id C {p₃ a}) ≡ id C
        F-id {i ,' j ,' a} = Functor.id (T (codisc i j))
        
        F-compose : {a b c : Obj ((Disc I op) ×C Disc I ×C C)}
                  → {f : Hom ((Disc I op) ×C Disc I ×C C) a b} {g : Hom ((Disc I op) ×C Disc I ×C C) b c} 
                  → F₁ ((((Disc I op) ×C Disc I ×C C) ∘ g) f) ≡ (C ∘ F₁ g) (F₁ f)
        F-compose {i ,' j ,' a} {.i ,' .j ,' b} {.i ,' .j ,' c} {refl ,' refl ,' f} {refl ,' refl ,' g} = Functor.compose (T (codisc j i))
    
    η : {a : Obj C} {s : Obj (Disc I)} → Hom C a ([ F ]₀ (s ,' s ,' a))
    η {a} {i} = nat-η (ix-η i) a
    
    μ : {a : Obj C} {s₁ s₂ s₃ : Obj (Disc I)} → Hom C ([ F ]₀ (s₁ ,' s₂ ,' [ F ]₀ (s₂ ,' s₃ ,' a))) ([ F ]₀ (s₁ ,' s₃ ,' a))
    μ {a} {i} {j} {k} = nat-η (ix-μ (codisc k j) (codisc j i)) a
