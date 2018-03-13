
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
open Category

IndexedMonad↔LaxTwoFunctor : {ℓI₀ ℓI₁ ℓC₀ ℓC₁ : Level}
                           → {I : Category {ℓI₀} {ℓI₁}}
                           → {C : Category {ℓC₀} {ℓC₁}}
                           → (Σ ({i j : Obj I} → Hom I i j → Functor C C) (IndexedMonad I))
                           ↔ (ConstLaxTwoFunctor (discreteHomCatTwoCategory I) (Cat {ℓC₀} {ℓC₁}) C)
IndexedMonad↔LaxTwoFunctor {ℓI₀} {ℓI₁} {ℓC₀} {ℓC₁} {I} {C} = bijection l→r r→l l→r→l r→l→r 
  where
    Cat' = Cat {ℓC₀} {ℓC₁}
    
    l→r : (Σ ({i j : Obj I} → Hom I i j → Functor C C) (IndexedMonad I))
        → (ConstLaxTwoFunctor (discreteHomCatTwoCategory I) Cat' C)
    l→r (M , monad) = IndexedMonad→LaxTwoFunctor monad

    r→l : (ConstLaxTwoFunctor (discreteHomCatTwoCategory I) Cat' C)
        → (Σ ({i j : Obj I} → Hom I i j → Functor C C) (IndexedMonad I))
    r→l F = (λ {i} {j} f → [ ConstLaxTwoFunctor.P₁ F {i} {j} ]₀ f) , LaxTwoFunctor→IndexedMonad F
    
    abstract
      l→r→l : (x : ConstLaxTwoFunctor (discreteHomCatTwoCategory I) Cat' C)
            → l→r (r→l x) ≡ x
      l→r→l F = const-lax-two-functor-eq P-eq (≡-to-≅ η-eq) μ-eq 
        where
          P₁ = ConstLaxTwoFunctor.P₁ (l→r (r→l F))
          
          I₂ = discreteHomCatTwoCategory I
          _∘I_ = Category._∘_ I
          
          abstract
            P₀-eq : {x y : Obj I} 
                  → Functor.F₀ (ConstLaxTwoFunctor.P₁ (l→r (r→l F)) {x} {y})
                  ≡ Functor.F₀ (ConstLaxTwoFunctor.P₁ F {x} {y})
            P₀-eq {x} {y} = fun-ext $ λ f → refl
            
          abstract
            P-eq : (λ {i j} → ConstLaxTwoFunctor.P₁ (l→r (r→l F)) {i} {j}) ≡ (λ {i j} → ConstLaxTwoFunctor.P₁ F {i} {j})
            P-eq = implicit-fun-ext 
                 $ λ (i : Obj I) → implicit-fun-ext 
                 $ λ (j : Obj I) → functor-eq (fun-ext $ λ f → refl) 
                 $ het-implicit-fun-ext (het-fun-ext hrefl $ λ f → hcong (λ X → ({b : Hom I i j} → f ≡ b → Category.Hom (HomCat Cat' C C) (X f) (X b))) 
                                                                         (≡-to-≅ P₀-eq)) 
                 $ λ (f : Hom I i j) → het-implicit-fun-ext (het-fun-ext hrefl $ λ x → hrefl) 
                 $ λ (g : Hom I i j) → ≡-to-≅ $ fun-ext 
                 $ λ { refl → sym (Functor.id (ConstLaxTwoFunctor.P₁ F)) }
          
          abstract
            η-eq : (λ {x} → ConstLaxTwoFunctor.η (l→r (r→l F)) {x}) ≡ (λ {x} → ConstLaxTwoFunctor.η F {x})
            η-eq = implicit-fun-ext $ λ x → natural-transformation-eq refl
          
          abstract
            μ-eq : (λ {x} {y} {z} {f} {g} → ConstLaxTwoFunctor.μ (l→r (r→l F)) {x} {y} {z} {f} {g})
                 ≅ (λ {x} {y} {z} {f} {g} → ConstLaxTwoFunctor.μ F {x} {y} {z} {f} {g})
            μ-eq = het-implicit-fun-ext (het-fun-ext hrefl $ λ (x : Obj I) → hrefl) 
                 $ λ (x : Obj I) → het-implicit-fun-ext (het-fun-ext hrefl $ λ (y : Obj I) → hrefl)
                 $ λ (y : Obj I) → het-implicit-fun-ext (het-fun-ext hrefl $ λ (z : Obj I) → hrefl)
                 $ λ (z : Obj I) → het-implicit-fun-ext (het-fun-ext hrefl $ λ (f : Hom I x y) → hrefl)
                 $ λ (f : Hom I x y) → het-implicit-fun-ext (het-fun-ext hrefl $ λ (g : Hom I y z) → hrefl)
                 $ λ (g : Hom I y z) → ≡-to-≅ (natural-transformation-eq $ fun-ext 
                 $ λ (c : Category.Obj C) → refl)
    
    abstract
      r→l→r : (x : Σ ({i j : Obj I} → Hom I i j → Functor C C) (IndexedMonad I))
            → r→l (l→r x) ≡ x
      r→l→r (M , monad) = Σ-eq refl $ ≡-to-≅ $ indexed-monad-eq refl 
                        $ implicit-fun-ext $ λ i → implicit-fun-ext $ λ j → implicit-fun-ext $ λ k → refl

LaxTwoFunctor↔IndexedMonad : {ℓI₀ ℓI₁ ℓC₀ ℓC₁ : Level}
                           → {I : Category {ℓI₀} {ℓI₁}}
                           → {C : Category {ℓC₀} {ℓC₁}}
                           → (ConstLaxTwoFunctor (discreteHomCatTwoCategory I) (Cat {ℓC₀} {ℓC₁}) C)
                           ↔ (Σ ({i j : Obj I} → Hom I i j → Functor C C) (IndexedMonad I))
LaxTwoFunctor↔IndexedMonad {I = I} {C} = Bijection.sym $ IndexedMonad↔LaxTwoFunctor {I = I} {C}

