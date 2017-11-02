 
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
IndexedMonad→ParameterizedRelativeMonad T IM = parameterizedRelativeMonad η' kext right-id left-id coher
  where
    open IndexedMonad IM
    
    η' : (i : Obj I) {a : Obj C} → Hom C a (F₀ (T (cid I {i})) a)
    η' i {a} = nat-η (η i) a
    
    kext : {i j k : Obj I} (f : Hom I i j) (g : Hom I j k) {a b : Obj C} 
         → Hom C a (F₀ (T g) b) → Hom C (F₀ (T f) a) (F₀ (T (g ∘I f)) b)
    kext {i} {j} {k} fI gI {a} {b} f = nat-η (μ fI gI) b ∘C [ T fI ]₁ f
    
    abstract
      right-id : {i j : Obj I} (f : Hom I i j) {a b : Obj C}
               → {k : Hom C a (F₀ (T f) b)} 
               → kext (cid I {i}) f k ∘C η' i ≅ k
      right-id {i} {j} fI {a} {b} {k} = begin
        kext (cid I {i}) fI k ∘C η' i {a}
          ≡⟨⟩
        (nat-η (μ (cid I {i}) fI) b ∘C [ T (cid I {i}) ]₁ k) ∘C nat-η (η i) a
          ≡⟨ sym $ assoc C ⟩
        nat-η (μ (cid I {i}) fI) b ∘C ([ T (cid I {i}) ]₁ k ∘C nat-η (η i) a)
          ≡⟨ cong (λ X → nat-η (μ (cid I {i}) fI) b ∘C X) (natural (η i)) ⟩
        nat-η (μ (cid I {i}) fI) b ∘C (nat-η (η i) ([ T fI ]₀ b) ∘C [ Id[ C ] ]₁ k)
          ≡⟨ assoc C ⟩
        (nat-η (μ (cid I {i}) fI) b ∘C nat-η (η i) ([ T fI ]₀ b)) ∘C [ Id[ C ] ]₁ k
          ≡⟨⟩
        (nat-η (μ (cid I {i}) fI) b ∘C nat-η (η i) ([ T fI ]₀ b)) ∘C k
          ≅⟨ hcong₂ (λ X Y → (Hom C ([ T fI ]₀ b) ([ T X ]₀ b) ∋ Y) ∘C k) (≡-to-≅ $ cat-left-id I) η-right-coher ⟩
        cid C {[ T fI ]₀ b} ∘C k
          ≡⟨ cat-right-id C ⟩
        k ∎
    
    abstract
      left-id : {i j : Obj I} (f : Hom I i j) {a : Obj C} 
              → kext f (cid I {j}) (η' j) ≅ cid C {F₀ (T f) a}
      left-id {i} {j} fI {a} = begin
        kext fI (cid I {j}) (η' j {a}) 
          ≡⟨⟩
        nat-η (μ fI (cid I {j})) a ∘C [ T fI ]₁ (nat-η (η j) a) -- 
          ≅⟨ η-left-coher ⟩
        cid C {F₀ (T fI) a} ∎
    
    abstract
      coher : {i j v w : Obj I} (f : Hom I i j) (g : Hom I j v) (h : Hom I v w)
            → {a b c : Obj C} {k : Hom C a (F₀ (T g) b)} {l : Hom C b (F₀ (T h) c)}
            → kext f (h ∘I g) (kext g h l ∘C k) ≅ (C ∘ kext (g ∘I f) h l) (kext f g k)
      coher {i} {j} {v} {w} fI gI hI {a} {b} {c} {k} {l} = begin
        kext fI (hI ∘I gI) (kext gI hI l ∘C k)
          ≡⟨⟩
        nat-η (μ fI (hI ∘I gI)) c ∘C [ T fI ]₁ ((nat-η (μ gI hI) c ∘C [ T gI ]₁ l) ∘C k)
          ≡⟨ cong (λ X → nat-η (μ fI (hI ∘I gI)) c ∘C X) (Functor.compose (T fI)) ⟩
        nat-η (μ fI (hI ∘I gI)) c ∘C ([ T fI ]₁ (nat-η (μ gI hI) c ∘C [ T gI ]₁ l) ∘C [ T fI ]₁ k)
          ≡⟨ cong (λ X → nat-η (μ fI (hI ∘I gI)) c ∘C (X ∘C [ T fI ]₁ k)) (Functor.compose (T fI)) ⟩
        nat-η (μ fI (hI ∘I gI)) c ∘C (([ T fI ]₁ (nat-η (μ gI hI) c) ∘C [ T fI ]₁ ([ T gI ]₁ l)) ∘C [ T fI ]₁ k)
          ≡⟨ cong (λ X → nat-η (μ fI (hI ∘I gI)) c ∘C X) (sym $ assoc C) ⟩
        nat-η (μ fI (hI ∘I gI)) c ∘C ([ T fI ]₁ (nat-η (μ gI hI) c) ∘C ([ T fI ]₁ ([ T gI ]₁ l) ∘C [ T fI ]₁ k))
          ≡⟨ assoc C ⟩
        (nat-η (μ fI (hI ∘I gI)) c ∘C [ T fI ]₁ (nat-η (μ gI hI) c)) ∘C ([ T fI ]₁ ([ T gI ]₁ l) ∘C [ T fI ]₁ k)
          ≅⟨ hcong₂ (λ X Y → (Hom C ([ [ T fI ]∘[ [ T gI ]∘[ T hI ] ] ]₀ c) ([ T X ]₀ c) ∋ Y) ∘C ([ T fI ]₁ ([ T gI ]₁ l) ∘C [ T fI ]₁ k))
                    (≡-to-≅ $ sym $ assoc I) μ-coher ⟩
        (nat-η (μ (gI ∘I fI) hI) c ∘C nat-η (μ fI gI) ([ T hI ]₀ c)) ∘C ([ T fI ]₁ ([ T gI ]₁ l) ∘C [ T fI ]₁ k)
          ≡⟨ sym $ assoc C ⟩
        nat-η (μ (gI ∘I fI) hI) c ∘C (nat-η (μ fI gI) ([ T hI ]₀ c) ∘C ([ T fI ]₁ ([ T gI ]₁ l) ∘C [ T fI ]₁ k))
          ≡⟨ cong (λ X → nat-η (μ (gI ∘I fI) hI) c ∘C X) (assoc C) ⟩
        nat-η (μ (gI ∘I fI) hI) c ∘C ((nat-η (μ fI gI) ([ T hI ]₀ c) ∘C [ T fI ]₁ ([ T gI ]₁ l)) ∘C [ T fI ]₁ k)
          ≡⟨ cong (λ X → nat-η (μ (gI ∘I fI) hI) c ∘C (X ∘C [ T fI ]₁ k)) (sym $ natural (μ fI gI)) ⟩
        nat-η (μ (gI ∘I fI) hI) c ∘C (([ T (gI ∘I fI) ]₁ l ∘C nat-η (μ fI gI) b) ∘C [ T fI ]₁ k)
          ≡⟨ cong (λ X → nat-η (μ (gI ∘I fI) hI) c ∘C X) (sym $ assoc C) ⟩
        nat-η (μ (gI ∘I fI) hI) c ∘C ([ T (gI ∘I fI) ]₁ l ∘C (nat-η (μ fI gI) b ∘C [ T fI ]₁ k))
          ≡⟨ assoc C ⟩
        (nat-η (μ (gI ∘I fI) hI) c ∘C [ T (gI ∘I fI) ]₁ l) ∘C (nat-η (μ fI gI) b ∘C [ T fI ]₁ k)
          ≡⟨⟩
        kext (gI ∘I fI) hI l ∘C kext fI gI k ∎

