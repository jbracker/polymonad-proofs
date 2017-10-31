 
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

open Category renaming ( right-id to cat-right-id ; left-id to cat-left-id ; id to cat-id )

module Theory.Haskell.Parameterized.Relative.Monad.Properties.ToIndexedMonad 
  {ℓC₀ ℓC₁ ℓI₀ ℓI₁ : Level} 
  {C : Category {ℓC₀} {ℓC₁}} {I : Category {ℓI₀} {ℓI₁}} where 

private
  _∘C_ = _∘_ C
  _∘I_ = _∘_ I

{-
 ParameterizedRelativeMonad (T : {i j : Obj I} → Hom I i j → Obj C → Obj D) 
                                  (J : Functor C D) : Set (ℓC₀ ⊔ ℓC₁ ⊔ ℓD₀ ⊔ ℓD₁ ⊔ ℓI₀ ⊔ ℓI₁) wher

 IndexedMonad  (M : {i j : Obj I} → Hom I i j → Functor C C) : Set (ℓC₀ ⊔ ℓC₁ ⊔ ℓI₀ ⊔ ℓI₁) 
-}
ParameterizedRelativeMonad→IndexedMonad : (T : {i j : Obj I} → Hom I i j → Obj C → Obj C) 
                                        → (PRM : ParameterizedRelativeMonad I T (Id[ C ])) → IndexedMonad I (ParameterizedRelativeMonad.FunctorT PRM)
ParameterizedRelativeMonad→IndexedMonad T PRM = indexedMonad NaturalTransformation-η {!!} {!!} {!!} {!!}
  where
    open ParameterizedRelativeMonad PRM
    
    NatTrans-μ : {i j k : Obj I} (f : Hom I i j) (g : Hom I j k) → NaturalTransformation [ FunctorT g ]∘[ FunctorT f ] (FunctorT ((I ∘ g) f))
    NatTrans-μ {i} {j} {k} fI gI = naturalTransformation {!!} {!!}
      where
        μ : (x : Obj C) → Hom C ([ [ FunctorT gI ]∘[ FunctorT fI ] ]₀ x) ([ FunctorT (gI ∘I fI) ]₀ x)
        μ x = {!kext gI fI ?!}
    
    NatTrans-μ' : {i j k : Obj I} (f : Hom I i j) (g : Hom I j k) → NaturalTransformation [ FunctorT f ]∘[ FunctorT g ] (FunctorT ((I ∘ g) f))
    NatTrans-μ' {i} {j} {k} fI gI = naturalTransformation μ' {!!}
      where
        μ' : (x : Obj C) → Hom C ([ [ FunctorT fI ]∘[ FunctorT gI ] ]₀ x) ([ FunctorT (gI ∘I fI) ]₀ x)
        μ' x = kext fI gI (cat-id C {T gI x})
        
        nat-μ' : {a b : Obj C} {f : Hom C a b}
               → [ FunctorT (gI ∘I fI) ]₁ f ∘C μ' a ≡ μ' b ∘C [ [ FunctorT fI ]∘[ FunctorT gI ] ]₁ f
        nat-μ' {a} {b} {f} = ≅-to-≡ $ begin
          [ FunctorT (gI ∘I fI) ]₁ f ∘C μ' a
            ≡⟨⟩
          subst (λ X → Hom C (T (gI ∘I fI) a) (T X b)) (Category.right-id I) (kext (gI ∘I fI) (cat-id I) (η k ∘C f)) ∘C kext fI gI (cat-id C {T gI a})
            ≡⟨ {!!} ⟩
          kext fI gI (cat-id C {T gI b}) ∘C [ FunctorT fI ]₁ (subst (λ X → Hom C (T gI a) (T X b)) (Category.right-id I) (kext gI (cat-id I) (η k ∘C f)))
            ≡⟨⟩
          μ' b ∘C [ [ FunctorT fI ]∘[ FunctorT gI ] ]₁ f ∎

-- (subst (λ X → Hom C (T gI a) (T X b)) (Category.right-id I) (kext gI (cat-id I) (η k ∘C f)))


{-
η :  (i : Obj I) → {a : Obj C} → Hom D ([ J ]₀ a) (T (id I {i}) a)
    
    kext : {i j k : Obj I} → (f : Hom I i j) (g : Hom I j k) 
         → {a b : Obj C} → Hom D ([ J ]₀ a) (T g b) → Hom D (T f a) (T (g ∘I f) b)
-}
