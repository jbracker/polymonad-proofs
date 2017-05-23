
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
open import Haskell
open import Haskell.Parameterized.EffectMonad
open import Haskell.Functor renaming ( Functor to HaskellFunctor ; functor-eq to haskell-functor-eq )

open import Theory.Monoid
open import Theory.Category
open import Theory.Category.Examples
open import Theory.Functor
open import Theory.Functor.Properties.IsomorphicHaskellFunctor
open import Theory.Natural.Transformation
open import Theory.TwoCategory
open import Theory.TwoCategory.Examples
open import Theory.TwoCategory.Examples.DiscreteHomCat
open import Theory.TwoFunctor
open import Theory.TwoFunctor.ConstZeroCell
open import Theory.TwoFunctor.Properties.FromEffectMonad
open import Theory.TwoFunctor.Properties.ToEffectMonad

module Theory.TwoFunctor.Properties.IsomorphicEffectMonad where

open StrictTwoCategory

private
  Cat' = Cat {suc zero} {zero}
  Hask' = Hask {zero}

EffectMonad↔LaxTwoFunctor : {ℓ : Level}
                          → {Eff : Set ℓ}
                          → (mon : Monoid Eff)
                          → (Σ (Eff → TyCon) (EffectMonad mon))
                          ↔ (ConstLaxTwoFunctor (discreteHomCatTwoCategory (monoidCategory mon)) Cat' Hask')
EffectMonad↔LaxTwoFunctor {ℓ} {Eff} mon = bijection l→r r→l l→r→l r→l→r
  where
    MonCat₂ = discreteHomCatTwoCategory (monoidCategory mon)
    
    l→r : Σ (Eff → TyCon) (EffectMonad mon) → ConstLaxTwoFunctor MonCat₂ Cat' Hask'
    l→r (M , monad) = EffectMonad→LaxTwoFunctor M monad

    r→l : ConstLaxTwoFunctor MonCat₂ Cat' Hask' → Σ (Eff → TyCon) (EffectMonad mon)
    r→l F = LaxTwoFunctor→EffectMonadTyCon mon F , LaxTwoFunctor→EffectMonad mon F
    
    l→r→l : (F : ConstLaxTwoFunctor MonCat₂ Cat' Hask') → l→r (r→l F) ≡ F
    l→r→l F = const-lax-two-functor-eq P-eq (≡-to-≅ η-eq) (≡-to-≅ μ-eq)
      where
        P₁ = ConstLaxTwoFunctor.P₁ (l→r (r→l F))
        
        M : Eff → TyCon
        M i α = [ Functor.F₀ P₁ i ]₀ α
        
        Cell₂-eq : {i j : Eff} → (f : Category.Hom (HomCat MonCat₂ (lift tt) (lift tt)) i j) 
                 → Functor.F₁ (ConstLaxTwoFunctor.P₁ (l→r (r→l F))) f ≡ Functor.F₁ (ConstLaxTwoFunctor.P₁ F) f
        Cell₂-eq {i} {.i} refl = natural-transformation-eq $ fun-ext $ λ α → fun-ext $ λ (ma : M i α) → begin
          ma
            ≡⟨⟩ 
          NaturalTransformation.η (Id⟨ Functor.F₀ (ConstLaxTwoFunctor.P₁ F) i ⟩) α ma
            ≡⟨ cong (λ X → NaturalTransformation.η X α ma) (sym (Functor.id (ConstLaxTwoFunctor.P₁ F))) ⟩ 
          NaturalTransformation.η (Functor.F₁ (ConstLaxTwoFunctor.P₁ F) refl) α ma ∎
        
        P₁-eq : (λ {a b} → Functor.F₁ (ConstLaxTwoFunctor.P₁ (l→r (r→l F))) {a} {b}) 
              ≡ (λ {a b} → Functor.F₁ (ConstLaxTwoFunctor.P₁ F) {a} {b})
        P₁-eq = implicit-fun-ext $ λ a → implicit-fun-ext $ λ b → fun-ext $ Cell₂-eq
        
        P-eq : (λ {x y} → ConstLaxTwoFunctor.P₁ (l→r (r→l F)) {x} {y}) ≡ (λ {x y} → ConstLaxTwoFunctor.P₁ F {x} {y})
        P-eq = implicit-fun-ext $ λ x → implicit-fun-ext $ λ y → functor-eq refl $ ≡-to-≅ $ P₁-eq
        
        η-eq : (λ {x} → ConstLaxTwoFunctor.η (l→r (r→l F)) {x}) ≡ (λ {x} → ConstLaxTwoFunctor.η F {x})
        η-eq = implicit-fun-ext $ λ x → natural-transformation-eq refl
        
        μ-eq : (λ {x y z} {f} {g} → ConstLaxTwoFunctor.μ (l→r (r→l F)) {x} {y} {z} {f} {g}) 
             ≡ (λ {x y z} {f} {g} → ConstLaxTwoFunctor.μ F {x} {y} {z} {f} {g})
        μ-eq = implicit-fun-ext $ λ x → implicit-fun-ext $ λ y → implicit-fun-ext $ λ z → implicit-fun-ext 
             $ λ f → implicit-fun-ext $ λ g → natural-transformation-eq $ fun-ext 
             $ λ (α : Type) → fun-ext $ λ mma → begin
               NaturalTransformation.η (ConstLaxTwoFunctor.μ (l→r (r→l F))) α mma
                 ≡⟨⟩
               EffectMonad._>>=_ (proj₂ (r→l F)) mma (λ x → x)
                 ≡⟨⟩
               NaturalTransformation.η (ConstLaxTwoFunctor.μ F) α ([ [ P₁ ]₀ g ]₁ (λ x → x) mma)
                 ≡⟨ cong (λ X → NaturalTransformation.η (ConstLaxTwoFunctor.μ F) α X) (cong (λ X → X mma) (Functor.id ([ P₁ ]₀ g))) ⟩
               NaturalTransformation.η (ConstLaxTwoFunctor.μ F) α mma ∎
    
    r→l→r : (x : Σ (Eff → TyCon) (EffectMonad mon)) → r→l (l→r x) ≡ x
    r→l→r (M , monad) = Σ-eq refl $ ≡-to-≅ $ effect-monad-eq bind-eq refl refl
      where
        open EffectMonad monad
        open Monoid mon
               
        bind-eq : (λ {α β : Type} {i j : Eff} → EffectMonad._>>=_ (proj₂ (r→l (l→r (M , monad)))) {α} {β} {i} {j})
                ≡ (λ {α β : Type} {i j : Eff} → EffectMonad._>>=_ monad {α} {β} {i} {j})
        bind-eq = implicit-fun-ext
                $ λ α → implicit-fun-ext $ λ β → implicit-fun-ext
                $ λ i → implicit-fun-ext $ λ j → fun-ext
                $ λ ma → fun-ext $ λ f → ≅-to-≡ $ hbegin
                  EffectMonad._>>=_ (proj₂ (r→l (l→r (M , monad)))) ma f
                    ≅⟨ hrefl ⟩
                  fmap f ma >>= (λ x → x)
                    ≅⟨ bind-arg₁ (sym right-id) (fmap f ma) (ma >>= (return ∘F f)) (hsym (law-monad-fmap f ma)) (λ x → x) ⟩ 
                  (ma >>= (return ∘F f)) >>= (λ x → x)
                    ≅⟨ hsym (law-assoc ma (return ∘F f) (λ x → x)) ⟩
                  ma >>= (λ a → return (f a) >>= (λ x → x))
                    ≅⟨ bind-arg₂ left-id ma (λ a → return (f a) >>= (λ x → x)) f (het-fun-ext (het-fun-ext hrefl (λ _ → hsym Mi≅Mεi)) (λ a → law-left-id (f a) (λ x → x))) ⟩
                  ma >>= f ∎h


LaxTwoFunctor↔EffectMonad : {ℓ : Level}
                          → {Eff : Set ℓ}
                          → (mon : Monoid Eff)
                          → (ConstLaxTwoFunctor (discreteHomCatTwoCategory (monoidCategory mon)) Cat' Hask')
                          ↔ (Σ (Eff → TyCon) (EffectMonad mon))
LaxTwoFunctor↔EffectMonad {ℓ} {Eff} mon = Bijection.sym $ EffectMonad↔LaxTwoFunctor {ℓ} {Eff} mon

