
-- Stdlib
open import Level
open import Function renaming ( _∘_ to _∘F_ )

open import Data.Unit
open import Data.Product

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( cong to hcong ; refl to hrefl ; sym to hsym )
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
    r→l F = (λ i j → [ ConstLaxTwoFunctor.P₁ F {i} {j} ]₀ (lift tt)) , LaxTwoFunctor→IndexedMonad F
    
    abstract
      l→r→l : (x : ConstLaxTwoFunctor (discreteHomCatTwoCategory (codiscreteCategory Ixs)) Cat' C)
            → l→r (r→l x) ≡ x
      l→r→l F = const-lax-two-functor-eq P-eq (≡-to-≅ η-eq) (≡-to-≅ μ-eq)
        where
          P₁ = ConstLaxTwoFunctor.P₁ (l→r (r→l F))
          M : Ixs → Ixs → Functor C C
          M i j = Functor.F₀ (P₁ {i} {j}) (lift tt) 
          
          abstract
            P₁-eq : {x y : Ixs} 
                  → (λ {a b} → Functor.F₁ (ConstLaxTwoFunctor.P₁ (l→r (r→l F)) {x} {y}) {a} {b}) 
                  ≡ (λ {a b} → Functor.F₁ (ConstLaxTwoFunctor.P₁ F {x} {y}) {a} {b})
            P₁-eq {x} {y} = implicit-fun-ext $ λ {(lift tt) → implicit-fun-ext $ λ {(lift tt) → fun-ext $ λ f → eq' x y f}}
              where
                eq' : (i j : Ixs)
                    → (f : Category.Hom (HomCat (discreteHomCatTwoCategory (codiscreteCategory Ixs)) i j) (lift tt) (lift tt))
                    → Functor.F₁ (ConstLaxTwoFunctor.P₁ (l→r (r→l F)) {i} {j}) {lift tt} {lift tt} f
                    ≡ Functor.F₁ (ConstLaxTwoFunctor.P₁ F {i} {j}) {lift tt} {lift tt} f
                eq' i j refl = natural-transformation-eq $ fun-ext $ λ c → begin
                  Category.id C
                    ≡⟨ refl ⟩
                  NaturalTransformation.η Id⟨ M i j ⟩ c
                    ≡⟨ cong (λ X → NaturalTransformation.η X c) (sym $ Functor.id $ ConstLaxTwoFunctor.P₁ F) ⟩
                  NaturalTransformation.η (Functor.F₁ (ConstLaxTwoFunctor.P₁ F) refl) c ∎ 
        
          abstract
            P-eq : (λ {i j} → ConstLaxTwoFunctor.P₁ (l→r (r→l F)) {i} {j}) ≡ (λ {i j} → ConstLaxTwoFunctor.P₁ F {i} {j})
            P-eq = implicit-fun-ext $ λ i → implicit-fun-ext $ λ j → functor-eq refl $ ≡-to-≅ $ P₁-eq {i} {j} -- P₁-eq {x} {y}
          
          abstract
            η-eq : (λ {x} → ConstLaxTwoFunctor.η (l→r (r→l F)) {x}) ≡ (λ {x} → ConstLaxTwoFunctor.η F {x})
            η-eq = implicit-fun-ext $ λ x → natural-transformation-eq refl
          
          abstract
            μ-eq : (λ {x y z} {f} {g} → ConstLaxTwoFunctor.μ (l→r (r→l F)) {x} {y} {z} {f} {g}) 
                 ≡ (λ {x y z} {f} {g} → ConstLaxTwoFunctor.μ F {x} {y} {z} {f} {g})
            μ-eq = implicit-fun-ext 
                 $ λ x → implicit-fun-ext 
                 $ λ y → implicit-fun-ext 
                 $ λ z → implicit-fun-ext 
                 $ λ f → implicit-fun-ext 
                 $ λ g → natural-transformation-eq $ fun-ext 
                 $ λ (c : Category.Obj C) → refl
    
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

