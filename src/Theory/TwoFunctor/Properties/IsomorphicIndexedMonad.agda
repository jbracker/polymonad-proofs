
-- Stdlib
open import Level
open import Function renaming ( _∘_ to _∘F_ )

open import Data.Unit
open import Data.Product

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( cong to hcong ; cong₂ to hcong₂ ; refl to hrefl ; sym to hsym ; trans to htrans )
open ≡-Reasoning

-- Local
open import Bijection hiding ( refl ; sym )
open import Extensionality
open import Equality
open import Theory.Haskell.Parameterized.Indexed.Monad
open import Theory.Haskell.Parameterized.Indexed.Monad.Equality
open import Theory.Category.Definition
open import Theory.Category.Examples.Codiscrete
open import Theory.Functor.Definition
open import Theory.Functor.Properties.IsomorphicHaskellFunctor
open import Theory.Natural.Transformation
open import Theory.TwoCategory.Definition
open import Theory.TwoCategory.Examples.Functor
open import Theory.TwoCategory.Examples.DiscreteHomCat
open import Theory.TwoFunctor.Definition
open import Theory.TwoFunctor.ConstZeroCell
open import Theory.TwoFunctor.ConstZeroCell.Equality
open import Theory.TwoFunctor.Properties.FromIndexedMonad
open import Theory.TwoFunctor.Properties.ToIndexedMonad

module Theory.TwoFunctor.Properties.IsomorphicIndexedMonad where

open StrictTwoCategory

IndexedMonad↔LaxTwoFunctor : {ℓIxs ℓC₀ ℓC₁ : Level}
                           → {C : Category {ℓC₀} {ℓC₁}}
                           → {Ixs : Set ℓIxs}
                           → (Σ (Ixs → Ixs → Functor C C) (IndexedMonad Ixs))
                           ↔ (ConstLaxTwoFunctor (discreteHomCatTwoCategory (codiscreteCategory Ixs)) (Cat {ℓC₀} {ℓC₁}) C)
IndexedMonad↔LaxTwoFunctor {ℓIxs} {ℓC₀} {ℓC₁} {C} {Ixs} = bijection l→r r→l l→r→l r→l→r 
  where
    Cat' = Cat {ℓC₀} {ℓC₁}
    
    l→r : (Σ (Ixs → Ixs → Functor C C) (IndexedMonad Ixs))
        → (ConstLaxTwoFunctor (discreteHomCatTwoCategory (codiscreteCategory Ixs)) Cat' C)
    l→r (M , monad) = IndexedMonad→LaxTwoFunctor monad

    r→l : (ConstLaxTwoFunctor (discreteHomCatTwoCategory (codiscreteCategory Ixs)) Cat' C)
        → (Σ (Ixs → Ixs → Functor C C) (IndexedMonad Ixs))
    r→l F = (λ i j → [ ConstLaxTwoFunctor.P₁ F {i} {j} ]₀ (codisc i j)) , LaxTwoFunctor→IndexedMonad F
    
    abstract
      l→r→l : (x : ConstLaxTwoFunctor (discreteHomCatTwoCategory (codiscreteCategory Ixs)) Cat' C)
            → l→r (r→l x) ≡ x
      l→r→l F = const-lax-two-functor-eq P-eq (≡-to-≅ η-eq) μ-eq -- (≡-to-≅ η-eq) (≡-to-≅ μ-eq)
        where
          P₁ = ConstLaxTwoFunctor.P₁ (l→r (r→l F))
          M : Ixs → Ixs → Functor C C
          M i j = Functor.F₀ (P₁ {i} {j}) (codisc i j)
          
          I = discreteHomCatTwoCategory (codiscreteCategory Ixs)
          _∘I_ = _∘_ I
          
          abstract
            P₀-eq : {x y : Ixs} 
                  → Functor.F₀ (ConstLaxTwoFunctor.P₁ (l→r (r→l F)) {x} {y})
                  ≡ Functor.F₀ (ConstLaxTwoFunctor.P₁ F {x} {y})
            P₀-eq {x} {y} = fun-ext $ λ { (codisc .x .y) → refl }
            
          abstract
            P-eq : (λ {i j} → ConstLaxTwoFunctor.P₁ (l→r (r→l F)) {i} {j}) ≡ (λ {i j} → ConstLaxTwoFunctor.P₁ F {i} {j})
            P-eq = implicit-fun-ext 
                 $ λ (i : Ixs) → implicit-fun-ext 
                 $ λ (j : Ixs) → functor-eq (fun-ext $ λ { (codisc .i .j) → refl }) 
                 $ het-implicit-fun-ext (het-fun-ext hrefl $ λ { (codisc .i .j) → hcong (λ X → ({b : CodiscreteArrow i j} → codisc i j ≡ b → Category.Hom (HomCat Cat' C C) (X (codisc i j)) (X b))) 
                                                                                        (≡-to-≅ P₀-eq)}) 
                 $ λ { (codisc .i .j) → het-implicit-fun-ext (het-fun-ext hrefl $ λ { (codisc .i .j) → hcong (λ X → (codisc i j ≡ codisc i j → NaturalTransformation (X (codisc i j)) (X (codisc i j)))) 
                                                                                                             (≡-to-≅ P₀-eq) }) 
                 $ λ { (codisc .i .j) → ≡-to-≅ $ fun-ext $ λ { refl → sym (Functor.id (ConstLaxTwoFunctor.P₁ F)) } } }
          
          abstract
            η-eq : (λ {x} → ConstLaxTwoFunctor.η (l→r (r→l F)) {x}) ≡ (λ {x} → ConstLaxTwoFunctor.η F {x})
            η-eq = implicit-fun-ext $ λ x → natural-transformation-eq refl
          
          abstract
            μ-eq : (λ {x} {y} {z} {f} {g} → ConstLaxTwoFunctor.μ (l→r (r→l F)) {x} {y} {z} {f} {g})
                 ≅ (λ {x} {y} {z} {f} {g} → ConstLaxTwoFunctor.μ F {x} {y} {z} {f} {g})
            μ-eq = het-implicit-fun-ext (het-fun-ext hrefl $ λ (x : Ixs) → hcong (λ X → ({y z : Ixs} {f : CodiscreteArrow x y} {g : CodiscreteArrow y z} 
                                                                                      → NaturalTransformation ((Cat' ∘ [ X {y} {z} ]₀ g) ([ X {x} {y} ]₀ f))
                                                                                                              ([ X {x} {z} ]₀ (g ∘I f)))) 
                                                                                 (≡-to-≅ P-eq)) 
                 $ λ (x : Ixs) → het-implicit-fun-ext (het-fun-ext hrefl $ λ (y : Ixs) → hcong (λ X → ({z : Ixs} {f : CodiscreteArrow x y} {g : CodiscreteArrow y z} 
                                                                                                    → NaturalTransformation ((Cat' ∘ [ X {y} {z} ]₀ g) ([ X {x} {y} ]₀ f))
                                                                                                                                   ([ X {x} {z} ]₀ (g ∘I f)))) 
                                                                                               (≡-to-≅ P-eq))
                 $ λ (y : Ixs) → het-implicit-fun-ext (het-fun-ext hrefl $ λ (z : Ixs) → hcong (λ X → ({f : CodiscreteArrow x y} {g : CodiscreteArrow y z} 
                                                                                                    → NaturalTransformation ((Cat' ∘ [ X {y} {z} ]₀ g) ([ X {x} {y} ]₀ f)) 
                                                                                                                            ([ X {x} {z} ]₀ (g ∘I f))))
                                                                                               (≡-to-≅ P-eq))
                 $ λ (z : Ixs) → het-implicit-fun-ext (het-fun-ext hrefl $ (λ { (codisc .x .y) → hcong (λ X → ({g : CodiscreteArrow y z} 
                                                                                                            → NaturalTransformation ((Cat' ∘ [ X {y} {z} ]₀ g) ([ X {x} {y} ]₀ (codisc x y)))
                                                                                                                                    ([ X {x} {z} ]₀ (g ∘I (codisc x y))))) 
                                                                                                       (≡-to-≅ P-eq) }))
                 $ λ { (codisc .x .y) → het-implicit-fun-ext (het-fun-ext hrefl $ (λ { (codisc .y .z) → 
                                                                          hcong (λ X → NaturalTransformation ((Cat' ∘ [ X {y} {z} ]₀ (codisc y z)) ([ X {x} {y} ]₀ (codisc x y))) 
                                                                                                                ([ X {x} {z} ]₀ ((codisc y z) ∘I (codisc x y))) ) 
                                                                                (≡-to-≅ P-eq) }))
                 $ λ { (codisc .y .z) → ≡-to-≅ (natural-transformation-eq $ fun-ext 
                 $ λ (c : Category.Obj C) → refl) } }
    
    abstract
      r→l→r : (x : Σ (Ixs → Ixs → Functor C C) (IndexedMonad Ixs))
            → r→l (l→r x) ≡ x
      r→l→r (M , monad) = Σ-eq refl $ ≡-to-≅ $ indexed-monad-eq refl 
                        $ implicit-fun-ext $ λ i → implicit-fun-ext $ λ j → implicit-fun-ext $ λ k → refl


LaxTwoFunctor↔IndexedMonad : {ℓIxs ℓC₀ ℓC₁ : Level}
                           → {C : Category {ℓC₀} {ℓC₁}}
                           → {Ixs : Set ℓIxs}
                           → (ConstLaxTwoFunctor (discreteHomCatTwoCategory (codiscreteCategory Ixs)) (Cat {ℓC₀} {ℓC₁}) C)
                           ↔ (Σ (Ixs → Ixs → Functor C C) (IndexedMonad Ixs))
LaxTwoFunctor↔IndexedMonad {C = C} {Ixs} = Bijection.sym $ IndexedMonad↔LaxTwoFunctor {C = C} {Ixs}

