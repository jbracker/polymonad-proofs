 
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

module Theory.Haskell.Parameterized.Relative.Monad.Properties.ToIndexedMonad 
  {ℓC₀ ℓC₁ ℓI₀ ℓI₁ : Level} 
  {C : Category {ℓC₀} {ℓC₁}} {I : Category {ℓI₀} {ℓI₁}} where 

private
  _∘C_ = _∘_ C
  _∘I_ = _∘_ I

ParameterizedRelativeMonad→IndexedMonad : (T : {i j : Obj I} → Hom I i j → Obj C → Obj C) 
                                        → (PRM : ParameterizedRelativeMonad I T (Id[ C ])) → IndexedMonad I (ParameterizedRelativeMonad.FunctorT PRM)
ParameterizedRelativeMonad→IndexedMonad T PRM = indexedMonad NaturalTransformation-η NatTrans-μ μ-coher η-left-coher η-right-coher
  where
    open ParameterizedRelativeMonad PRM
        
    μ : {i j k : Obj I} (fI : Hom I i j) (gI : Hom I j k)
      → (x : Obj C) → Hom C ([ [ FunctorT gI ]∘[ FunctorT fI ] ]₀ x) ([ FunctorT (gI ∘I fI) ]₀ x)
    μ fI gI x = kext fI gI (cid C {T fI x})
    
    abstract
      μ-coher : {i j k l : Obj I} {f : Hom I i j} {g : Hom I j k} {h : Hom I k l} {x : Obj C}
              → μ (g ∘I f) h x ∘C [ FunctorT h ]₁ (μ f g x)
              ≅ μ f (h ∘I g) x ∘C μ g h ([ FunctorT f ]₀ x)
      μ-coher {i} {j} {k} {l} {fI} {gI} {hI} {x} = begin
        μ (gI ∘I fI) hI x ∘C [ FunctorT hI ]₁ (μ fI gI x)
          ≡⟨⟩
        kext (gI ∘I fI) hI (cid C {T (gI ∘I fI) x}) ∘C subst (λ X → Hom C (T hI (T gI (T fI x))) (T X (T (gI ∘I fI) x))) (cat-left-id I) (kext (cid I) hI (η k ∘C (kext fI gI (cid C {T fI x}))))
          ≅⟨ hcong₂ (λ X Y → kext (gI ∘I fI) X (cid C {T (gI ∘I fI) x}) ∘C Y) 
                    (≡-to-≅ $ sym $ cat-left-id I) 
                    (≡-subst-removable (λ X → Hom C (T hI (T gI (T fI x))) (T X (T (gI ∘I fI) x))) (cat-left-id I) (kext (cid I) hI (η k ∘C (kext fI gI (cid C {T fI x}))))) ⟩
        kext (gI ∘I fI) (hI ∘I cid I) (cid C {T (gI ∘I fI) x}) ∘C kext (cid I) hI (η k ∘C (kext fI gI (cid C {T fI x})))
          ≅⟨ hsym $ coher (gI ∘I fI) (cid I) hI ⟩
        kext (cid I ∘I (gI ∘I fI)) hI (kext (gI ∘I fI) (cid I) (cid C {T (gI ∘I fI) x}) ∘C (η k ∘C (kext fI gI (cid C {T fI x}))))
          ≡⟨ cong (kext (cid I ∘I (gI ∘I fI)) hI) (assoc C) ⟩
        kext (cid I ∘I (gI ∘I fI)) hI ((kext (gI ∘I fI) (cid I) (cid C {T (gI ∘I fI) x}) ∘C η k) ∘C (kext fI gI (cid C {T fI x})))
          ≅⟨ hcong₂ (λ X Y → kext X hI (Y ∘C (kext fI gI (cid C {T fI x})))) (≡-to-≅ $ cat-right-id I) (right-id (gI ∘I fI)) ⟩
        kext (gI ∘I fI) hI (cid C {T (gI ∘I fI) x} ∘C (kext fI gI (cid C {T fI x})))
          ≡⟨ cong (kext (gI ∘I fI) hI) (cat-right-id C) ⟩
        kext (gI ∘I fI) hI (kext fI gI (cid C {T fI x}))
          ≡⟨ cong (kext (gI ∘I fI) hI) (sym $ cat-left-id C) ⟩ 
        kext (gI ∘I fI) hI (kext fI gI (cid C {T fI x}) ∘C cid C {T gI (T fI x)})
          ≅⟨ coher fI gI hI ⟩ 
        kext fI (hI ∘I gI) (cid C {T fI x}) ∘C kext gI hI (cid C {T gI (T fI x)})
          ≡⟨⟩
        μ fI (hI ∘I gI) x ∘C μ gI hI ([ FunctorT fI ]₀ x) ∎
    
    abstract
      η-left-coher : {i j : Obj I} {f : Hom I i j} {x : Obj C} 
                   → μ (cid I) f x ∘C [ FunctorT f ]₁ (η i {x})
                   ≅ cid C { [ FunctorT f ]₀ x }
      η-left-coher {i} {j} {fI} {x} = {!!} {- begin
        μ fI (cid I) x ∘C [ FunctorT fI ]₁ (η j {x})
          ≡⟨⟩
        kext fI (cid I) (cid C {T (cid I) x}) ∘C subst (λ X → Hom C (T fI x) (T X (T (cid I) x))) (cat-right-id I) (kext fI (cid I) (η j ∘C η j {x}))
          ≅⟨ hcong₂ (λ X Y → kext X (cid I) (cid C {T (cid I) x}) ∘C Y) 
                    (≡-to-≅ $ sym $ cat-right-id I) 
                    (≡-subst-removable (λ X → Hom C (T fI x) (T X (T (cid I) x))) (cat-right-id I) (kext fI (cid I) (η j ∘C η j {x}))) ⟩
        kext (cid I ∘I fI) (cid I) (cid C {T (cid I) x}) ∘C kext fI (cid I) (η j ∘C η j {x})
          ≅⟨ hsym $ coher fI (cid I) (cid I) ⟩
        kext fI (cid I ∘I cid I) (kext (cid I) (cid I) (cid C {T (cid I) x}) ∘C (η j ∘C η j {x}))
          ≡⟨ cong (kext fI (cid I ∘I cid I)) (assoc C) ⟩
        kext fI (cid I ∘I cid I) ((kext (cid I) (cid I) (cid C {T (cid I) x}) ∘C η j) ∘C η j {x})
          ≅⟨ hcong₂ (λ X Y → kext fI X (Y ∘C η j {x})) (≡-to-≅ $ cat-right-id I) (right-id (cid I)) ⟩
        kext fI (cid I) (cid C {T (cid I) x} ∘C η j {x})
          ≡⟨ cong (kext fI (cid I)) (cat-right-id C) ⟩
        kext fI (cid I) (η j {x})
          ≅⟨ left-id fI ⟩
        cid C { [ FunctorT fI ]₀ x } ∎ -}
    
    abstract
      η-right-coher : {i j : Obj I} {f : Hom I i j} {x : Obj C} 
                    → μ f (cid I) x ∘C (η j {[ FunctorT f ]₀ x})
                    ≅ cid C { [ FunctorT f ]₀ x }
      η-right-coher {i} {j} {fI} {x} = begin
        μ fI (cid I) x ∘C η j {[ FunctorT fI ]₀ x}
          ≡⟨⟩
        kext fI (cid I) (cid C {T fI x}) ∘C η j {[ FunctorT fI ]₀ x}
          ≅⟨ right-id fI ⟩
        cid C { [ FunctorT fI ]₀ x } ∎

    NatTrans-μ : {i j k : Obj I} (f : Hom I i j) (g : Hom I j k) → NaturalTransformation [ FunctorT g ]∘[ FunctorT f ] (FunctorT ((I ∘ g) f))
    NatTrans-μ {i} {j} {k} fI gI = naturalTransformation (μ fI gI) {!!} {- nat-μ
      where
        abstract
          nat-μ : {a b : Obj C} {f : Hom C a b}
                → [ FunctorT (gI ∘I fI) ]₁ f ∘C μ fI gI a ≡ μ fI gI b ∘C [ [ FunctorT fI ]∘[ FunctorT gI ] ]₁ f
          nat-μ {a} {b} {f} = ≅-to-≡ $ begin
            [ FunctorT (gI ∘I fI) ]₁ f ∘C μ fI gI a
              ≡⟨⟩
            subst (λ X → Hom C (T (gI ∘I fI) a) (T X b)) (cat-right-id I) (kext (gI ∘I fI) (cid I) (η k ∘C f)) ∘C kext fI gI (cid C {T gI a})
              ≅⟨ hcong₂ (λ X Y → (Hom C (T (gI ∘I fI) a) (T X b) ∋ Y) ∘C kext fI gI (cid C {T gI a})) 
                        (≡-to-≅ $ sym $ cat-right-id I) 
                        (≡-subst-removable ((λ X → Hom C (T (gI ∘I fI) a) (T X b))) (cat-right-id I) (kext (gI ∘I fI) (cid I) (η k ∘C f))) ⟩
            kext (gI ∘I fI) (cid I) (η k ∘C f) ∘C kext fI gI (cid C {T gI a})
              ≅⟨ hsym $ coher fI gI (cid I) ⟩
            kext fI (cid I ∘I gI) (kext gI (cid I) (η k ∘C f) ∘C cid C {T gI a})
              ≡⟨ cong (kext fI (cid I ∘I gI)) (cat-left-id C) ⟩
            kext fI (cid I ∘I gI) (kext gI (cid I) (η k ∘C f))
              ≡⟨ cong (kext fI (cid I ∘I gI)) (sym $ cat-right-id C) ⟩
            kext fI (cid I ∘I gI) (cid C {T (cid I ∘I gI) b} ∘C kext gI (cid I) (η k ∘C f))
              ≅⟨ hcong₂ (λ X Y → kext fI X (Y ∘C kext gI (cid I) (η k ∘C f))) 
                        (≡-to-≅ $ sym $ cat-left-id I) 
                        (hsym $ right-id (cid I ∘I gI)) ⟩
            kext fI ((cid I ∘I gI) ∘I cid I) ((kext (cid I) (cid I ∘I gI) (cid C {T (cid I ∘I gI) b}) ∘C η j) ∘C kext gI (cid I) (η k ∘C f))
              ≡⟨ cong (kext fI ((cid I ∘I gI) ∘I cid I)) (sym $ assoc C) ⟩
            kext fI ((cid I ∘I gI) ∘I cid I) (kext (cid I) (cid I ∘I gI) (cid C {T (cid I ∘I gI) b}) ∘C (η j ∘C kext gI (cid I) (η k ∘C f)))
              ≅⟨ coher fI (cid I) (cid I ∘I gI) ⟩
            kext (cid I ∘I fI) (cid I ∘I gI) (cid C {T (cid I ∘I gI) b}) ∘C (kext fI (cid I) (η j ∘C kext gI (cid I) (η k ∘C f)))
              ≡⟨⟩
            kext (cid I ∘I fI) (cid I ∘I gI) (cid C {T (cid I ∘I gI) b}) ∘C (kext fI (cid I) (η j ∘C [ Id[ C ] ]₁ (kext gI (cid I) (η k ∘C f))))
              ≅⟨ hcong₂ (λ X Y → kext X (cid I ∘I gI) (cid C {T (cid I ∘I gI) b}) ∘C Y) 
                        (≡-to-≅ $ cat-right-id I) 
                        (hsym $ ≡-subst-removable ((λ X → Hom C (T fI (T gI a)) (T X (T (cid I ∘I gI) b)))) 
                                                  (cat-right-id I) 
                                                  (kext fI (cid I) (η j ∘C [ Id[ C ] ]₁ (kext gI (cid I) (η k ∘C f))))) ⟩
            kext fI (cid I ∘I gI) (cid C {T (cid I ∘I gI) b}) ∘C subst (λ X → Hom C (T fI (T gI a)) (T X (T (cid I ∘I gI) b))) 
                                                                       (cat-right-id I) 
                                                                       (kext fI (cid I) (η j ∘C [ Id[ C ] ]₁ (kext gI (cid I) (η k ∘C f))))
                 ≡⟨⟩
            kext fI (cid I ∘I gI) (cid C {T (cid I ∘I gI) b}) ∘C [ FunctorT fI ]₁ (kext gI (cid I) (η k ∘C f))
              ≅⟨ hcong₂ (λ X Y → kext fI X (cid C {T X b}) ∘C [ FunctorT fI ]₁ Y) 
                        (≡-to-≅ $ cat-right-id I) 
                        (hsym $ ≡-subst-removable ((λ X → Hom C (T gI a) (T X b))) (cat-right-id I) (kext gI (cid I) (η k ∘C f))) ⟩
            kext fI gI (cid C {T gI b}) ∘C [ FunctorT fI ]₁ (subst (λ X → Hom C (T gI a) (T X b)) (cat-right-id I) (kext gI (cid I) (η k ∘C f)))
              ≡⟨⟩
            μ fI gI b ∘C [ [ FunctorT fI ]∘[ FunctorT gI ] ]₁ f ∎ -}



