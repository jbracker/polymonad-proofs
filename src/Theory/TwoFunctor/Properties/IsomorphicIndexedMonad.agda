
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
open import Haskell
open import Haskell.Parameterized.Indexed.Monad
open import Haskell.Functor renaming ( Functor to HaskellFunctor ; functor-eq to haskell-functor-eq )
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

IndexedMonad↔LaxTwoFunctor : {ℓ : Level}
                           → (Σ (Set ℓ) (λ Ixs → Σ (Ixs → Ixs → TyCon) (IxMonad Ixs)))
                           ↔ (Σ (Set ℓ) (λ Ixs → ConstLaxTwoFunctor (discreteHomCatTwoCategory (codiscreteCategory Ixs)) (Cat {suc zero} {zero}) (Hask {zero})))
IndexedMonad↔LaxTwoFunctor {ℓ} = bijection l→r r→l l→r→l r→l→r
  where
    Cat' = Cat {suc zero} {zero}
    Hask' = Hask {zero}
    
    l→r : Σ (Set ℓ) (λ Ixs → Σ (Ixs → Ixs → TyCon) (IxMonad Ixs))
        → Σ (Set ℓ) (λ Ixs → ConstLaxTwoFunctor (discreteHomCatTwoCategory (codiscreteCategory Ixs)) Cat' Hask')
    l→r (Ixs , M , monad) = Ixs , IndexedMonad→LaxTwoFunctor Ixs M monad

    r→l : Σ (Set ℓ) (λ Ixs → ConstLaxTwoFunctor (discreteHomCatTwoCategory (codiscreteCategory Ixs)) Cat' Hask')
        → Σ (Set ℓ) (λ Ixs → Σ (Ixs → Ixs → TyCon) (IxMonad Ixs))
    r→l (Ixs , F) = Ixs , LaxTwoFunctor→IxMonadTyCon Ixs F , LaxTwoFunctor→IndexedMonad Ixs F
    
    abstract
      l→r→l : (x : Σ (Set ℓ) (λ Ixs → ConstLaxTwoFunctor (discreteHomCatTwoCategory (codiscreteCategory Ixs)) Cat' Hask'))
            → l→r (r→l x) ≡ x
      l→r→l (Ixs , F) = Σ-eq refl $ ≡-to-≅ $ const-lax-two-functor-eq P-eq (≡-to-≅ η-eq) (≡-to-≅ μ-eq)
        where
          P₁ = ConstLaxTwoFunctor.P₁ (proj₂ (l→r (r→l (Ixs , F))))
          M : Ixs → Ixs → TyCon
          M i j α = [ Functor.F₀ (ConstLaxTwoFunctor.P₁ (proj₂ (l→r (r→l (Ixs , F)))) {i} {j}) (lift tt) ]₀ α
          
          abstract
            Cell₂-eq : {α : Type} → (i j : Ixs) → (ma : M i j α) 
                     → ma ≡ NaturalTransformation.η (Functor.F₁ (ConstLaxTwoFunctor.P₁ F) refl) α ma
            Cell₂-eq {α} i j ma = begin
              ma
                ≡⟨⟩ 
              NaturalTransformation.η (Id⟨ Functor.F₀ (ConstLaxTwoFunctor.P₁ F) (lift tt) ⟩) α ma
                ≡⟨ cong (λ X → NaturalTransformation.η X α ma) (sym (Functor.id (ConstLaxTwoFunctor.P₁ F))) ⟩ 
              NaturalTransformation.η (Functor.F₁ (ConstLaxTwoFunctor.P₁ F) refl) α ma ∎
        
          abstract
            P₁-eq : {x y : Ixs} 
                  → (λ {a b} → Functor.F₁ (ConstLaxTwoFunctor.P₁ (proj₂ (l→r (r→l (Ixs , F)))) {x} {y}) {a} {b}) 
                  ≡ (λ {a b} → Functor.F₁ (ConstLaxTwoFunctor.P₁ F {x} {y}) {a} {b})
            P₁-eq {x} {y} = implicit-fun-ext $ λ {(lift tt) → implicit-fun-ext $ λ {(lift tt) → fun-ext $ λ f → eq' x y f}}
              where
                eq' : (x y : Ixs)
                    → (f : Category.Hom (HomCat (discreteHomCatTwoCategory (codiscreteCategory (proj₁ (l→r (r→l (Ixs , F)))))) x y) (lift tt) (lift tt))
                    → Functor.F₁ (ConstLaxTwoFunctor.P₁ (proj₂ (l→r (r→l (Ixs , F)))) {x} {y}) {lift tt} {lift tt} f
                    ≡ Functor.F₁ (ConstLaxTwoFunctor.P₁ F {x} {y}) {lift tt} {lift tt} f
                eq' x y refl = natural-transformation-eq $ fun-ext $ λ α → fun-ext $ λ ma → Cell₂-eq {α} x y ma
                    
        
          abstract
            -- Id⟨ HaskellFunctor→Functor (functor j i) ⟩
            P-eq : (λ {x y} → ConstLaxTwoFunctor.P₁ (proj₂ (l→r (r→l (Ixs , F)))) {x} {y}) ≡ (λ {x y} → ConstLaxTwoFunctor.P₁ F {x} {y})
            P-eq = implicit-fun-ext $ λ x → implicit-fun-ext $ λ y → functor-eq refl $ ≡-to-≅ $ P₁-eq {x} {y}
          
          abstract
            η-eq : (λ {x} → ConstLaxTwoFunctor.η (proj₂ (l→r (r→l (Ixs , F)))) {x}) ≡ (λ {x} → ConstLaxTwoFunctor.η F {x})
            η-eq = implicit-fun-ext $ λ x → natural-transformation-eq refl
          
          abstract
            μ-eq : (λ {x y z} {f} {g} → ConstLaxTwoFunctor.μ (proj₂ (l→r (r→l (Ixs , F)))) {x} {y} {z} {f} {g}) 
                 ≡ (λ {x y z} {f} {g} → ConstLaxTwoFunctor.μ F {x} {y} {z} {f} {g})
            μ-eq = implicit-fun-ext $ λ x → implicit-fun-ext $ λ y → implicit-fun-ext $ λ z → implicit-fun-ext 
                 $ λ f → implicit-fun-ext $ λ g → natural-transformation-eq $ fun-ext 
                 $ λ (α : Type) → fun-ext $ λ mma → begin
                   NaturalTransformation.η (ConstLaxTwoFunctor.μ (proj₂ (l→r (r→l (Ixs , F))))) α mma
                     ≡⟨⟩
                   IxMonad._>>=_ (proj₂ (proj₂ (r→l (Ixs , F)))) mma (λ x → x)
                     ≡⟨⟩
                   NaturalTransformation.η (ConstLaxTwoFunctor.μ F) α ([ [ P₁ {y} {z} ]₀ (lift tt) ]₁ (λ x → x) mma)
                     ≡⟨ cong (λ X → NaturalTransformation.η (ConstLaxTwoFunctor.μ F) α X) (cong (λ X → X mma) (Functor.id ([ P₁ {y} {z} ]₀ (lift tt)))) ⟩
                   NaturalTransformation.η (ConstLaxTwoFunctor.μ F) α mma ∎
    
    abstract
      r→l→r : (x : Σ (Set ℓ) (λ Ixs → Σ (Ixs → Ixs → TyCon) (IxMonad Ixs)))
            → r→l (l→r x) ≡ x
      r→l→r (Ixs , M , monad) = Σ-eq refl $ het-Σ-eq refl $ ≡-to-≅ $ indexed-monad-eq bind-eq refl refl
        where
          open IxMonad monad
          
          abstract
            bind-eq : (λ {α β : Type} {i j k : Ixs} → IxMonad._>>=_ (proj₂ (proj₂ (r→l (l→r (Ixs , M , monad))))) {α} {β} {i} {j} {k})
                    ≡ (λ {α β : Type} {i j k : Ixs} → IxMonad._>>=_ monad {α} {β} {i} {j} {k})
            bind-eq = implicit-fun-ext
                    $ λ α → implicit-fun-ext $ λ β → implicit-fun-ext
                    $ λ i → implicit-fun-ext $ λ j → implicit-fun-ext $ λ k → fun-ext
                    $ λ ma → fun-ext $ λ f → begin
                      IxMonad._>>=_ (proj₂ (proj₂ (r→l (l→r (Ixs , M , monad))))) ma f
                        ≡⟨⟩
                      fmap f ma >>= (λ x → x)
                        ≡⟨ cong (λ X → X >>= (λ x → x)) (sym (law-monad-fmap f ma)) ⟩
                      (ma >>= (return ∘F f)) >>= (λ x → x)
                        ≡⟨ sym (law-assoc ma (return ∘F f) (λ x → x)) ⟩
                      ma >>= (λ a → return (f a) >>= (λ x → x))
                        ≡⟨ cong (λ X → _>>=_ ma X) (fun-ext (λ a → law-right-id (f a) (λ x → x))) ⟩
                      ma >>= f ∎

LaxTwoFunctor↔IndexedMonad : {ℓ : Level}
                           → (Σ (Set ℓ) (λ Ixs → ConstLaxTwoFunctor (discreteHomCatTwoCategory (codiscreteCategory Ixs)) (Cat {suc zero} {zero}) (Hask {zero})))
                           ↔ (Σ (Set ℓ) (λ Ixs → Σ (Ixs → Ixs → TyCon) (IxMonad Ixs)))
LaxTwoFunctor↔IndexedMonad {ℓ} = Bijection.sym $ IndexedMonad↔LaxTwoFunctor {ℓ}
