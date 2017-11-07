
open import Level
open import Function hiding ( id ; _∘_ )

open import Data.Product

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( refl to hrefl ; sym to hsym ; trans to htrans ; cong to hcong )

open import Bijection renaming ( refl to brefl ; sym to bsym ; trans to btrans )
open import Extensionality
open import Equality

open import Theory.Triple renaming ( _,_,_ to _,'_,'_ )
open import Theory.Category.Definition
open import Theory.Category.Examples.Discrete renaming ( discreteCategory to Disc )
open import Theory.Category.Examples.Codiscrete renaming ( codiscreteCategory to Codisc )
open import Theory.Functor.Definition
open import Theory.Functor.Composition
open import Theory.Natural.Transformation
open import Theory.Monad.Atkey
open import Theory.Monad.Atkey.Equality
open import Theory.Haskell.Parameterized.Indexed.Monad
open import Theory.Haskell.Parameterized.Indexed.Monad.Equality

open import Theory.Haskell.Parameterized.Indexed.Monad.Properties.ToAtkeyParameterizedMonad
open import Theory.Haskell.Parameterized.Indexed.Monad.Properties.FromAtkeyParameterizedMonad

module Theory.Haskell.Parameterized.Indexed.Monad.Properties.IsomorphicAtkeyParameterizedMonad
  {ℓC₀ ℓC₁ ℓI : Level}
  {C : Category {ℓC₀} {ℓC₁}} {I : Set ℓI}
  where

open Category

private
  _∘I_ = _∘_ (Codisc I)

IndexedMonad↔AtkeyParameterizedMonad 
  : (Σ ({i j : I} → Hom (Codisc I) i j → Functor C C) (IndexedMonad (Codisc I))) 
  ↔ AtkeyParameterizedMonad C (Disc I)
IndexedMonad↔AtkeyParameterizedMonad =
  bijection IndexedMonad→AtkeyParameterizedMonad AtkeyParameterizedMonad→IndexedMonad APM→IM→APM IM→APM→IM
  where
    abstract
      APM→IM→APM : (APM : AtkeyParameterizedMonad C (Disc I))
                 → IndexedMonad→AtkeyParameterizedMonad (AtkeyParameterizedMonad→IndexedMonad APM) ≡ APM
      APM→IM→APM APM = atkey-parameterized-monad-eq T-eq hrefl hrefl
        where
          abstract
            T-eq : AtkeyParameterizedMonad.T (IndexedMonad→AtkeyParameterizedMonad (AtkeyParameterizedMonad→IndexedMonad APM))
                 ≡ AtkeyParameterizedMonad.T APM
            T-eq = functor-eq refl $ het-implicit-fun-ext hrefl
                 $ λ { (i ,' j ,' a) → het-implicit-fun-ext hrefl
                 $ λ { (k ,' l ,' b) → het-fun-ext hrefl 
                 $ λ { (refl ,' refl ,' f) → hrefl } } }

    abstract
      IM→APM→IM : (IM : Σ ({i j : I} → Hom (Codisc I) i j → Functor C C) (IndexedMonad (Codisc I)))
                → AtkeyParameterizedMonad→IndexedMonad (IndexedMonad→AtkeyParameterizedMonad IM)
                ≡ IM
      IM→APM→IM (F , IM) = Σ-eq F-eq IM-eq
        where
          abstract
            F-eq : (λ {i j} → proj₁ (AtkeyParameterizedMonad→IndexedMonad (IndexedMonad→AtkeyParameterizedMonad (F , IM))) {i} {j}) ≡ F
            F-eq = implicit-fun-ext $ λ i → implicit-fun-ext $ λ j → fun-ext $ λ { (codisc .i .j) → functor-eq refl hrefl }

          abstract
            IM-eq : proj₂ (AtkeyParameterizedMonad→IndexedMonad (IndexedMonad→AtkeyParameterizedMonad (F , IM))) ≅ IM
            IM-eq = het-indexed-monad-eq F-eq η-eq μ-eq
              where
                abstract
                  η-eq : IndexedMonad.η (proj₂ (AtkeyParameterizedMonad→IndexedMonad (IndexedMonad→AtkeyParameterizedMonad (F , IM))))
                       ≅ IndexedMonad.η IM
                  η-eq = het-fun-ext (hcong (λ X → (λ z → NaturalTransformation Id[ C ] (X (id (Codisc I) {z})))) (≡-to-≅ F-eq))
                       $ λ i → het-natural-transformation-eq refl (cong (λ X → X (id (Codisc I))) F-eq) hrefl
                
                abstract
                  μ-eq : (λ {i j k} → IndexedMonad.μ (proj₂ (AtkeyParameterizedMonad→IndexedMonad (IndexedMonad→AtkeyParameterizedMonad (F , IM)))) {i} {j} {k})
                       ≅ (λ {i j k} → IndexedMonad.μ IM {i} {j} {k})
                  μ-eq = het-implicit-fun-ext (hcong (λ X → (λ z → {a b : I} (f : CodiscreteArrow z a) (g : Hom (Codisc I) a b) → NaturalTransformation [ X g ]∘[ X f ] (X (g ∘I f))))
                                                     (≡-to-≅ F-eq))
                       $ λ i → het-implicit-fun-ext (hcong (λ X → (λ z → {a : I} (f : CodiscreteArrow i z) (g : Hom (Codisc I) z a) → NaturalTransformation [ X g ]∘[ X f ] (X (g ∘I f))))
                                                           (≡-to-≅ F-eq))
                       $ λ j → het-implicit-fun-ext (hcong (λ X → (λ z → (a : CodiscreteArrow i j) (g : Hom (Codisc I) j z) → NaturalTransformation [ X g ]∘[ X a ] (X (g ∘I a))))
                                                           (≡-to-≅ F-eq))
                       $ λ k → het-fun-ext (hcong (λ X → (λ z → (g : Hom (Codisc I) j k) → NaturalTransformation [ X g ]∘[ X z ] (X (g ∘I z)))) (≡-to-≅ F-eq))
                       $ λ { (codisc ._ .j) → het-fun-ext (hcong (λ X → (λ z → NaturalTransformation [ X z ]∘[ X (codisc i j) ] (X (z ∘I codisc i j)))) (≡-to-≅ F-eq))
                       $ λ { (codisc .j ._) → het-natural-transformation-eq
                                                  (cong (λ X → [ X (codisc j k) ]∘[ X (codisc i j) ]) F-eq)
                                                  (cong (λ X → X (codisc j k ∘I codisc i j)) F-eq)
                                                  hrefl } }

AtkeyParameterizedMonad↔IndexedMonad
  : AtkeyParameterizedMonad C (Disc I)
  ↔ (Σ ({i j : I} → Hom (Codisc I) i j → Functor C C) (IndexedMonad (Codisc I))) 
AtkeyParameterizedMonad↔IndexedMonad = bsym IndexedMonad↔AtkeyParameterizedMonad
