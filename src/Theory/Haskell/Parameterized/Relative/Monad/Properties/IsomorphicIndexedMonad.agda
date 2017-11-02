
-- Stdlib
open import Level
open import Function hiding ( id ) renaming ( _∘_ to _∘F_ )
open import Data.Unit
open import Data.Product

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( refl to hrefl ; sym to hsym ; trans to htrans ; subst to hsubst ; cong to hcong ; cong₂ to hcong₂ )
open ≅-Reasoning 

-- Local
open import Bijection renaming ( refl to brefl ; sym to bsym ; trans to btrans )
open import Congruence
open import Extensionality
open import Equality

open import Theory.Category.Definition
open import Theory.Functor.Definition
open import Theory.Functor.Composition
open import Theory.Natural.Transformation

open import Theory.Haskell.Parameterized.Indexed.Monad
open import Theory.Haskell.Parameterized.Indexed.Monad.Equality

open import Theory.Haskell.Parameterized.Relative.Monad
open import Theory.Haskell.Parameterized.Relative.Monad.Equality
open import Theory.Haskell.Parameterized.Relative.Monad.Properties.FromIndexedMonad
open import Theory.Haskell.Parameterized.Relative.Monad.Properties.ToIndexedMonad

open Category renaming ( right-id to cat-right-id ; left-id to cat-left-id ; id to cid )

module Theory.Haskell.Parameterized.Relative.Monad.Properties.IsomorphicIndexedMonad 
  {ℓC₀ ℓC₁ ℓI₀ ℓI₁ : Level} 
  {C : Category {ℓC₀} {ℓC₁}} {I : Category {ℓI₀} {ℓI₁}} where 

private
  _∘C_ = _∘_ C
  _∘I_ = _∘_ I

open Functor renaming ( id to fun-id )
open Category renaming ( right-id to cat-right-id ; left-id to cat-left-id ; id to cid )
open NaturalTransformation renaming ( η to nat-η )


IndexedMonad↔ParameterizedRelativeMonad : Σ ({i j : Obj I} → Hom I i j → Functor C C) (IndexedMonad I)
                                        ↔ Σ ({i j : Obj I} → Hom I i j → Obj C → Obj C) (λ F → ParameterizedRelativeMonad I F Id[ C ])
IndexedMonad↔ParameterizedRelativeMonad = bijection IM→PRM PRM→IM PRM-id IM-id
  where
    IM→PRM : Σ ({i j : Obj I} → Hom I i j → Functor C C) (IndexedMonad I)
           → Σ ({i j : Obj I} → Hom I i j → Obj C → Obj C) (λ F → ParameterizedRelativeMonad I F Id[ C ])
    IM→PRM (T , IM) = (λ f → F₀ (T f)) , IndexedMonad→ParameterizedRelativeMonad T IM
    
    PRM→IM : Σ ({i j : Obj I} → Hom I i j → Obj C → Obj C) (λ F → ParameterizedRelativeMonad I F Id[ C ])
           → Σ ({i j : Obj I} → Hom I i j → Functor C C) (IndexedMonad I)
    PRM→IM (T₀ , PRM) = IndexedMonad.functor IM , IM
      where IM = ParameterizedRelativeMonad→IndexedMonad T₀ PRM

    abstract
      IM-id : (IM : Σ ({i j : Obj I} → Hom I i j → Functor C C) (IndexedMonad I))
            → PRM→IM (IM→PRM IM) ≡ IM
      IM-id (T , IM) = Σ-eq T-eq $ het-indexed-monad-eq T-eq η-eq μ-eq
        where
          open IndexedMonad

          abstract
            T₁-eq : {i j : Obj I} (fI : Hom I i j)
                  → (λ {a b} f → F₁ (proj₁ (PRM→IM (IM→PRM (T , IM))) {i} {j} fI) {a} {b} f) ≡ F₁ (T fI)
            T₁-eq {i} {j} fI = implicit-fun-ext $ λ a → implicit-fun-ext $ λ b → fun-ext $ λ f → ≅-to-≡ $ begin
              subst (λ X → Hom C (F₀ (T fI) a) (F₀ (T X) b)) (Category.right-id I) (nat-η (μ IM fI (cid I)) b ∘C [ T fI ]₁ (nat-η (η IM j) b ∘C f))
                ≅⟨ ≡-subst-removable (λ X → Hom C (F₀ (T fI) a) (F₀ (T X) b))
                                     (Category.right-id I)
                                     (nat-η (μ IM fI (cid I)) b ∘C [ T fI ]₁ (nat-η (η IM j) b ∘C [ Id[ C ] ]₁ f)) ⟩
              nat-η (μ IM fI (cid I)) b ∘C [ T fI ]₁ (nat-η (η IM j) b ∘C f)
                ≡⟨ cong (λ X → nat-η (μ IM fI (cid I)) b ∘C X) (compose (T fI)) ⟩
              nat-η (μ IM fI (cid I)) b ∘C ([ T fI ]₁ (nat-η (η IM j) b) ∘C [ T fI ]₁ f)
                ≡⟨ assoc C ⟩
              (nat-η (μ IM fI (cid I)) b ∘C [ T fI ]₁ (nat-η (η IM j) b)) ∘C [ T fI ]₁ f
                ≅⟨ hcong₂ (λ X Y → (Hom C (F₀ (T fI) b) (F₀ (T X) b) ∋ Y) ∘C [ T fI ]₁ f)
                          (≡-to-≅ $ cat-right-id I)
                          (η-left-coher IM) ⟩
              cid C ∘C [ T fI ]₁ f
                ≡⟨ cat-right-id C ⟩
              F₁ (T fI) f ∎

          abstract
            T-eq : (λ {i j} fI → proj₁ (PRM→IM (IM→PRM (T , IM))) {i} {j} fI) ≡ T
            T-eq = implicit-fun-ext
                 $ λ i → implicit-fun-ext
                 $ λ j → fun-ext
                 $ λ fI → functor-eq refl (≡-to-≅ (T₁-eq {i} {j} fI))

          abstract
            η-eq : (λ i → η (proj₂ (PRM→IM (IM→PRM (T , IM)))) i) ≅ (λ i → η IM i)
            η-eq = het-fun-ext (hcong (λ X → (λ z → NaturalTransformation Id[ C ] (X (cid I {z})))) (≡-to-≅ $ T-eq))
                 $ λ i → het-natural-transformation-eq refl (cong (λ X → X (cid I)) T-eq) hrefl
          
          abstract
            μ-eq : (λ {i j k} fI gI → μ (proj₂ (PRM→IM (IM→PRM (T , IM)))) {i} {j} {k} fI gI) ≅ (λ {i j k} fI gI → μ IM {i} {j} {k} fI gI)
            μ-eq = het-implicit-fun-ext (hcong (λ X → (λ z → {j k : Obj I} (fI : Hom I z j) (gI : Hom I j k) → NaturalTransformation [ X fI ]∘[ X gI ] (X (gI ∘I fI)))) (≡-to-≅ $ T-eq))
                 $ λ i → het-implicit-fun-ext (hcong (λ X → (λ z → {k : Obj I} (fI : Hom I i z) (gI : Hom I z k) → NaturalTransformation [ X fI ]∘[ X gI ] (X (gI ∘I fI)))) (≡-to-≅ $ T-eq))
                 $ λ j → het-implicit-fun-ext (hcong (λ X → (λ z → (fI : Hom I i j) (gI : Hom I j z) → NaturalTransformation [ X fI ]∘[ X gI ] (X (gI ∘I fI)))) (≡-to-≅ $ T-eq))
                 $ λ k → het-fun-ext (hcong (λ X → (λ z → (gI : Hom I j k) → NaturalTransformation [ X z ]∘[ X gI ] (X (gI ∘I z)))) (≡-to-≅ $ T-eq))
                 $ λ fI → het-fun-ext (hcong (λ X → (λ z → NaturalTransformation [ X fI ]∘[ X z ] (X (z ∘I fI)))) (≡-to-≅ $ T-eq))
                 $ λ gI → het-natural-transformation-eq (cong (λ X → [ X fI ]∘[ X gI ]) T-eq) (cong (λ X → X (gI ∘I fI)) T-eq)
                 $ het-fun-ext (hcong (λ X → (λ z → Hom C ([ [ X fI ]∘[ X gI ] ]₀ z) ([ X (gI ∘I fI) ]₀ z))) (≡-to-≅ $ T-eq))
                 $ λ x → begin
                   nat-η (μ IM fI gI) x ∘C [ T fI ]₁ (cid C {F₀ (T gI) x})
                     ≡⟨ cong (λ X → nat-η (μ IM fI gI) x ∘C X) (fun-id (T fI)) ⟩
                   nat-η (μ IM fI gI) x ∘C cid C {F₀ (T fI) (F₀ (T gI) x)}
                     ≡⟨ cat-left-id C ⟩
                   nat-η (μ IM fI gI) x ∎
    
    abstract
      PRM-id : (PRM : Σ ({i j : Obj I} → Hom I i j → Obj C → Obj C) (λ F → ParameterizedRelativeMonad I F Id[ C ]))
             → IM→PRM (PRM→IM PRM) ≡ PRM
      PRM-id (T₀ , PRM) = Σ-eq refl $ ≡-to-≅ $ parameterized-relative-monad-eq refl $ implicit-fun-ext
                        $ λ i → implicit-fun-ext
                        $ λ j → implicit-fun-ext
                        $ λ k → fun-ext
                        $ λ fI → fun-ext
                        $ λ gI → implicit-fun-ext
                        $ λ a → implicit-fun-ext
                        $ λ b → fun-ext
                        $ λ f → ≅-to-≡ $ begin
                          kext PRM fI gI (cid C {T₀ gI b}) ∘C subst (λ X → Hom C (T₀ fI a) (T₀ X (T₀ gI b))) (cat-right-id I) (kext PRM fI (cid I) (η PRM j ∘C f))
                            ≅⟨ hcong₂ (λ X Y → kext PRM X gI (cid C {T₀ gI b}) ∘C Y)
                                      (≡-to-≅ $ sym $ cat-right-id I)
                                      (≡-subst-removable (λ X → Hom C (T₀ fI a) (T₀ X (T₀ gI b))) (cat-right-id I) (kext PRM fI (cid I) (η PRM j ∘C f))) ⟩
                          kext PRM (cid I ∘I fI) gI (cid C {T₀ gI b}) ∘C kext PRM fI (cid I) (η PRM j ∘C f)
                            ≅⟨ hsym $ coher PRM fI (cid I {j}) gI ⟩
                          kext PRM fI (gI ∘I cid I) (kext PRM (cid I {j}) gI (cid C {T₀ gI b}) ∘C (η PRM j ∘C f))
                            ≡⟨ cong (kext PRM fI (gI ∘I cid I)) (assoc C) ⟩
                          kext PRM fI (gI ∘I cid I) ((kext PRM (cid I {j}) gI (cid C {T₀ gI b}) ∘C η PRM j) ∘C f)
                            ≅⟨ hcong₂ (λ X Y → kext PRM fI X (Y ∘C f)) (≡-to-≅ $ cat-left-id I) (right-id PRM gI) ⟩
                          kext PRM fI gI (cid C {T₀ gI b} ∘C f)
                            ≡⟨ cong (kext PRM fI gI) (cat-right-id C) ⟩
                          kext PRM fI gI f ∎
        where
          open ParameterizedRelativeMonad
    
ParameterizedRelativeMonad↔IndexedMonad : Σ ({i j : Obj I} → Hom I i j → Obj C → Obj C) (λ F → ParameterizedRelativeMonad I F Id[ C ])
                                        ↔ Σ ({i j : Obj I} → Hom I i j → Functor C C) (IndexedMonad I)
ParameterizedRelativeMonad↔IndexedMonad = bsym IndexedMonad↔ParameterizedRelativeMonad
