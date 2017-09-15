
-- Stdlib
open import Level
open import Function renaming ( _∘_ to _∘F_ )

open import Data.Unit
open import Data.Product

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( cong to hcong ; refl to hrefl ; sym to hsym )
open ≡-Reasoning hiding ( _≅⟨_⟩_ )
open ≅-Reasoning hiding ( _≡⟨_⟩_ ; _≡⟨⟩_ ) renaming ( begin_ to hbegin_ ; _∎ to _∎h )

-- Local
open import Bijection hiding ( refl ; sym )
open import Extensionality
open import Equality

open import Theory.Monoid
open import Theory.Category.Definition
open import Theory.Category.Examples.Monoid
open import Theory.Functor.Definition
open import Theory.Functor.Properties.IsomorphicHaskellFunctor
open import Theory.Natural.Transformation
open import Theory.TwoCategory.Definition
open import Theory.TwoCategory.Examples.Functor
open import Theory.TwoCategory.Examples.Monoid
open import Theory.TwoFunctor.Definition
open import Theory.TwoFunctor.ConstZeroCell
open import Theory.TwoFunctor.ConstZeroCell.Equality
open import Theory.TwoFunctor.Properties.FromGradedMonad
open import Theory.TwoFunctor.Properties.ToGradedMonad
open import Theory.Haskell.Parameterized.Graded.Monad
open import Theory.Haskell.Parameterized.Graded.Monad.Equality

module Theory.TwoFunctor.Properties.IsomorphicGradedMonad where

open StrictTwoCategory hiding ( right-id ; left-id ; assoc )

GradedMonad↔ConstLaxTwoFunctor : {ℓMon ℓC₀ ℓC₁ : Level}
                          → {Mon : Set ℓMon}
                          → (C : Category {ℓC₀} {ℓC₁})
                          → (monoid : Monoid Mon)
                          → (Σ (Mon → Functor C C) (GradedMonad monoid))
                          ↔ (ConstLaxTwoFunctor (monoidTwoCategory monoid) Cat C)
GradedMonad↔ConstLaxTwoFunctor {ℓMon} {ℓC₀} {ℓC₁} {Mon} C monoid = bijection l→r r→l l→r→l r→l→r
  where
    Cat' = Cat {ℓC₀} {ℓC₁}
    MonCat₂ = monoidTwoCategory monoid
    
    l→r : Σ (Mon → Functor C C) (GradedMonad monoid) → ConstLaxTwoFunctor MonCat₂ Cat' C
    l→r (M , monad) = GradedMonad→LaxTwoFunctor monad

    r→l : ConstLaxTwoFunctor MonCat₂ Cat' C → Σ (Mon → Functor C C) (GradedMonad monoid)
    r→l F = (λ i → [ ConstLaxTwoFunctor.P₁ F {tt} {tt} ]₀ i) , LaxTwoFunctor→GradedMonad F
    
    abstract
      l→r→l : (F : ConstLaxTwoFunctor MonCat₂ Cat' C) → l→r (r→l F) ≡ F
      l→r→l F = const-lax-two-functor-eq P-eq hrefl hrefl
        where
          P₁ = ConstLaxTwoFunctor.P₁ (l→r (r→l F))
          
          M : Mon → Functor C C
          M i = Functor.F₀ P₁ i
          
          abstract
            Cell₂-eq : {i j : Mon} → (f : Category.Hom (HomCat MonCat₂ tt tt) i j) 
                     → Functor.F₁ (ConstLaxTwoFunctor.P₁ (l→r (r→l F))) f ≡ Functor.F₁ (ConstLaxTwoFunctor.P₁ F) f
            Cell₂-eq {i} {.i} refl = natural-transformation-eq $ fun-ext $ λ (c : Category.Obj C) → begin
              Category.id C {[ M i ]₀ c}
                ≡⟨ refl ⟩
              NaturalTransformation.η (Id⟨ M i ⟩) c
                ≡⟨ cong (λ X → NaturalTransformation.η X c) (sym (Functor.id (ConstLaxTwoFunctor.P₁ F))) ⟩
              NaturalTransformation.η (Functor.F₁ (ConstLaxTwoFunctor.P₁ F) refl) c ∎
          
          abstract
            P₁-eq : (λ {a b} → Functor.F₁ (ConstLaxTwoFunctor.P₁ (l→r (r→l F))) {a} {b}) 
                  ≡ (λ {a b} → Functor.F₁ (ConstLaxTwoFunctor.P₁ F) {a} {b})
            P₁-eq = implicit-fun-ext $ λ a → implicit-fun-ext $ λ b → fun-ext $ Cell₂-eq
          
          abstract
            P-eq : (λ {x y} → ConstLaxTwoFunctor.P₁ (l→r (r→l F)) {x} {y}) ≡ (λ {x y} → ConstLaxTwoFunctor.P₁ F {x} {y})
            P-eq = implicit-fun-ext $ λ x → implicit-fun-ext $ λ y → functor-eq refl $ ≡-to-≅ $ P₁-eq
    
    abstract
      r→l→r : (x : Σ (Mon → Functor C C) (GradedMonad monoid)) → r→l (l→r x) ≡ x
      r→l→r (M , monad) = Σ-eq refl $ ≡-to-≅ $ graded-monad-eq refl refl


ConstLaxTwoFunctor↔GradedMonad : {ℓMon ℓC₀ ℓC₁ : Level}
                               → {Mon : Set ℓMon}
                               → (C : Category {ℓC₀} {ℓC₁})
                               → (monoid : Monoid Mon)
                               → (ConstLaxTwoFunctor (monoidTwoCategory monoid) Cat C)
                               ↔ (Σ (Mon → Functor C C) (GradedMonad monoid))
ConstLaxTwoFunctor↔GradedMonad C monoid = Bijection.sym $ GradedMonad↔ConstLaxTwoFunctor C monoid

