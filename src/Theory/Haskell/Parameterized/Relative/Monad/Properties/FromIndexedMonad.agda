 
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

open import Theory.Haskell.Parameterized.Relative.Monad

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
         → Hom C a (F₀ (T f) b) → Hom C (F₀ (T g) a) (F₀ (T (g ∘I f)) b)
    kext {i} {j} {k} fI gI {a} {b} f = nat-η (μ fI gI) b ∘C [ T gI ]₁ f
    
    abstract
      right-id : {i j : Obj I} (f : Hom I i j) {a b : Obj C}
               → {k : Hom C a (F₀ (T f) b)} 
               → kext f (cid I {j}) k ∘C η' j ≅ k
      right-id {i} {j} fI {a} {b} {k} = begin
        kext fI (cid I) k ∘C η' j {a}
          ≡⟨⟩
        (nat-η (μ fI (cid I {j})) b ∘C [ T (cid I {j}) ]₁ k) ∘C nat-η (η j) a
          ≡⟨ sym $ assoc C ⟩
        nat-η (μ fI (cid I {j})) b ∘C ([ T (cid I {j}) ]₁ k ∘C nat-η (η j) a)
          ≡⟨ cong (λ X → nat-η (μ fI (cid I {j})) b ∘C X) (natural (η j)) ⟩
        nat-η (μ fI (cid I {j})) b ∘C (nat-η (η j) ([ T fI ]₀ b) ∘C [ Id[ C ] ]₁ k)
          ≡⟨ assoc C ⟩
        (nat-η (μ fI (cid I {j})) b ∘C nat-η (η j) ([ T fI ]₀ b)) ∘C [ Id[ C ] ]₁ k
          ≡⟨⟩
        (nat-η (μ fI (cid I {j})) b ∘C nat-η (η j) ([ T fI ]₀ b)) ∘C k
          ≅⟨ hcong₂ (λ X Y → (Hom C ([ T fI ]₀ b) ([ T X ]₀ b) ∋ Y) ∘C k) (≡-to-≅ $ cat-right-id I) η-right-coher ⟩
        cid C {[ T fI ]₀ b} ∘C k
          ≡⟨ cat-right-id C ⟩
        k ∎
    
    abstract
      left-id : {i j : Obj I} (f : Hom I i j) {a : Obj C} 
              → kext (cid I {i}) f (η' i) ≅ cid C {F₀ (T f) a}
      left-id {i} {j} fI {a} = begin
        kext (cid I {i}) fI (η' i {a}) 
          ≡⟨⟩
        nat-η (μ (cid I {i}) fI) a ∘C [ T fI ]₁ (nat-η (η i) a) -- 
          ≅⟨ η-left-coher ⟩
        cid C {F₀ (T fI) a} ∎
    
    abstract
      coher : {i j v w : Obj I} (f : Hom I i j) (g : Hom I j v) (h : Hom I v w)
            → {a b c : Obj C} {k : Hom C a (F₀ (T g) b)} {l : Hom C b (F₀ (T f) c)}
            → kext (g ∘I f) h (kext f g l ∘C k) ≅ (C ∘ kext f (h ∘I g) l) (kext g h k)
      coher {i} {j} {v} {w} fI gI hI {a} {b} {c} {k} {l} = begin
        kext (gI ∘I fI) hI (kext fI gI l ∘C k)
          ≡⟨⟩
        nat-η (μ (gI ∘I fI) hI) c ∘C [ T hI ]₁ ((nat-η (μ fI gI) c ∘C [ T gI ]₁ l) ∘C k)
          ≡⟨ cong (λ X → nat-η (μ (gI ∘I fI) hI) c ∘C X) (Functor.compose (T hI)) ⟩
        nat-η (μ (gI ∘I fI) hI) c ∘C ([ T hI ]₁ (nat-η (μ fI gI) c ∘C [ T gI ]₁ l) ∘C [ T hI ]₁ k)
          ≡⟨ cong (λ X → nat-η (μ (gI ∘I fI) hI) c ∘C (X ∘C [ T hI ]₁ k)) (Functor.compose (T hI)) ⟩
        nat-η (μ (gI ∘I fI) hI) c ∘C (([ T hI ]₁ (nat-η (μ fI gI) c) ∘C [ T hI ]₁ ([ T gI ]₁ l)) ∘C [ T hI ]₁ k)
          ≡⟨ cong (λ X → nat-η (μ (gI ∘I fI) hI) c ∘C X) (sym $ assoc C) ⟩
        nat-η (μ (gI ∘I fI) hI) c ∘C ([ T hI ]₁ (nat-η (μ fI gI) c) ∘C ([ T hI ]₁ ([ T gI ]₁ l) ∘C [ T hI ]₁ k))
          ≡⟨ assoc C ⟩
        (nat-η (μ (gI ∘I fI) hI) c ∘C [ T hI ]₁ (nat-η (μ fI gI) c)) ∘C ([ T hI ]₁ ([ T gI ]₁ l) ∘C [ T hI ]₁ k)
          ≅⟨ hcong₂ (λ X Y → (Hom C ([ [ T hI ]∘[ [ T gI ]∘[ T fI ] ] ]₀ c) ([ T X ]₀ c) ∋ Y) ∘C ([ T hI ]₁ ([ T gI ]₁ l) ∘C [ T hI ]₁ k))
                    (≡-to-≅ $ assoc I) μ-coher ⟩
        (nat-η (μ fI (hI ∘I gI)) c ∘C nat-η (μ gI hI) ([ T fI ]₀ c)) ∘C ([ T hI ]₁ ([ T gI ]₁ l) ∘C [ T hI ]₁ k)
          ≡⟨ sym $ assoc C ⟩
        nat-η (μ fI (hI ∘I gI)) c ∘C (nat-η (μ gI hI) ([ T fI ]₀ c) ∘C ([ T hI ]₁ ([ T gI ]₁ l) ∘C [ T hI ]₁ k))
          ≡⟨ cong (λ X → nat-η (μ fI (hI ∘I gI)) c ∘C X) (assoc C) ⟩
        nat-η (μ fI (hI ∘I gI)) c ∘C ((nat-η (μ gI hI) ([ T fI ]₀ c) ∘C [ T hI ]₁ ([ T gI ]₁ l)) ∘C [ T hI ]₁ k)
          ≡⟨ cong (λ X → nat-η (μ fI (hI ∘I gI)) c ∘C (X ∘C [ T hI ]₁ k)) (sym $ natural (μ gI hI)) ⟩
        nat-η (μ fI (hI ∘I gI)) c ∘C (([ T (hI ∘I gI) ]₁ l ∘C nat-η (μ gI hI) b) ∘C [ T hI ]₁ k)
          ≡⟨ cong (λ X → nat-η (μ fI (hI ∘I gI)) c ∘C X) (sym $ assoc C) ⟩
        nat-η (μ fI (hI ∘I gI)) c ∘C ([ T (hI ∘I gI) ]₁ l ∘C (nat-η (μ gI hI) b ∘C [ T hI ]₁ k))
          ≡⟨ assoc C ⟩
        (nat-η (μ fI (hI ∘I gI)) c ∘C [ T (hI ∘I gI) ]₁ l) ∘C (nat-η (μ gI hI) b ∘C [ T hI ]₁ k)
          ≡⟨⟩
        kext fI (hI ∘I gI) l ∘C kext gI hI k ∎

