
-- Stdlib
open import Level
open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Data.Product
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Relation.Binary.HeterogeneousEquality using ( ≡-to-≅ )

-- Local
open import Extensionality
open import Equality
open import Bijection hiding ( refl ; sym )
open import Haskell
open import Haskell.Functor using ( functor-eq )
open import Haskell.Applicative hiding ( applicative )
open import Haskell.Monad hiding ( monad ) renaming ( Monad to HaskellMonad )

open import Theory.Functor.Definition
open import Theory.Functor.Composition
open import Theory.Functor.Properties.IsomorphicHaskellFunctor
open import Theory.Monad.Definition hiding ( monad )
open import Theory.Monad.Properties.FromHaskellMonad
open import Theory.Monad.Properties.ToHaskellMonad
open import Theory.Natural.Transformation

module Theory.Monad.Properties.IsomorphicHaskellMonad where

Monad↔HaskellMonad : (Σ (Functor (Hask {zero}) (Hask {zero})) Monad) ↔ (Σ TyCon HaskellMonad)
Monad↔HaskellMonad = bijection
  (λ FM → [ proj₁ FM  ]₀ , Monad→HaskellMonad (proj₂ FM))
  (λ FM → (HaskellFunctor→Functor (HaskellMonad.functor (proj₂ FM))) , (HaskellMonad→Monad (proj₂ FM)))
  id₁ id₂
  where  
    id₁ : (m : Σ TyCon HaskellMonad)
        → ([ HaskellFunctor→Functor (HaskellMonad.functor (proj₂ m)) ]₀ , Monad→HaskellMonad (HaskellMonad→Monad (proj₂ m)))
        ≡ m
    id₁ (M , haskMonad) = Σ-eq refl $ ≡-to-≅ $ Haskell.Monad.monad-eq bind-eq (applicative-eq return-pure-eq ap-eq (Haskell.Functor.functor-eq refl))
      where
        bind-eq : (λ {α β} → HaskellMonad._>>=_ (Monad→HaskellMonad (HaskellMonad→Monad haskMonad)) {α} {β}) ≡ HaskellMonad._>>=_ haskMonad
        bind-eq = implicit-fun-ext $ λ α → implicit-fun-ext $ λ β → fun-ext $ λ ma → fun-ext $ λ f → begin
          (Monad→HaskellMonad (HaskellMonad→Monad haskMonad) HaskellMonad.>>= ma) f
            ≡⟨⟩
          HaskellMonad.join haskMonad (HaskellMonad.fmap haskMonad f ma)
            ≡⟨⟩
          HaskellMonad._>>=_ haskMonad (HaskellMonad.fmap haskMonad f ma) (λ x → x)
            ≡⟨ cong (λ X → HaskellMonad._>>=_ haskMonad X (λ x → x)) (HaskellMonad.law-monad-fmap haskMonad f ma) ⟩
          HaskellMonad._>>=_ haskMonad (HaskellMonad._>>=_ haskMonad ma (HaskellMonad.return haskMonad ∘F f)) (λ x → x)
            ≡⟨ sym (HaskellMonad.law-assoc haskMonad ma (HaskellMonad.return haskMonad ∘F f) (λ x → x)) ⟩
          HaskellMonad._>>=_ haskMonad ma (λ x → HaskellMonad._>>=_ haskMonad (HaskellMonad.return haskMonad (f x)) (λ x → x))
            ≡⟨ cong (λ X → HaskellMonad._>>=_ haskMonad ma X) (fun-ext (λ x → HaskellMonad.law-left-id haskMonad (f x) (λ x → x))) ⟩
          HaskellMonad._>>=_ haskMonad ma f ∎
        
        return-pure-eq : (λ {α} → HaskellMonad.return (Monad→HaskellMonad (HaskellMonad→Monad haskMonad)) {α}) ≡ Applicative.pure (HaskellMonad.applicative haskMonad)
        return-pure-eq = implicit-fun-ext $ λ α → fun-ext $ λ a → refl
        
        ap-eq : (λ {α β} → HaskellMonad._<*>_ (Monad→HaskellMonad (HaskellMonad→Monad haskMonad)) {α} {β}) ≡ Applicative._<*>_ (HaskellMonad.applicative haskMonad)
        ap-eq = implicit-fun-ext $ λ α → implicit-fun-ext $ λ β → fun-ext $ λ f → fun-ext $ λ a → begin
          (HaskellMonad.applicative (Monad→HaskellMonad (HaskellMonad→Monad haskMonad)) Applicative.<*> f) a
            ≡⟨⟩
          HaskellMonad.join haskMonad (HaskellMonad.fmap haskMonad (λ f → HaskellMonad.fmap haskMonad f a) f)
            ≡⟨⟩
          HaskellMonad._>>=_ haskMonad (HaskellMonad.fmap haskMonad (λ f → HaskellMonad.fmap haskMonad f a) f) (λ x → x)
            ≡⟨ cong (λ X → HaskellMonad._>>=_ haskMonad X (λ x → x)) (HaskellMonad.law-monad-fmap haskMonad (λ f → HaskellMonad.fmap haskMonad f a) f) ⟩
          HaskellMonad._>>=_ haskMonad (HaskellMonad._>>=_ haskMonad f (HaskellMonad.return haskMonad ∘F (λ f → HaskellMonad.fmap haskMonad f a))) (λ x → x)
            ≡⟨ sym (HaskellMonad.law-assoc haskMonad f (HaskellMonad.return haskMonad ∘F (λ f → HaskellMonad.fmap haskMonad f a)) (λ x → x)) ⟩
          HaskellMonad._>>=_ haskMonad f (λ x → HaskellMonad._>>=_ haskMonad (HaskellMonad.return haskMonad (HaskellMonad.fmap haskMonad x a)) (λ x → x))
            ≡⟨ cong (λ X → HaskellMonad._>>=_ haskMonad f X) (fun-ext (λ x → HaskellMonad.law-left-id haskMonad (HaskellMonad.fmap haskMonad x a) (λ x → x))) ⟩
          HaskellMonad._>>=_ haskMonad f (λ f → HaskellMonad.fmap haskMonad f a)
            ≡⟨ sym (HaskellMonad.law-monad-ap haskMonad f a) ⟩
          Applicative._<*>_ (HaskellMonad.applicative haskMonad) f a ∎

    open Theory.Monad.Definition.Monad

    id₂ : (m : Σ (Functor Hask Hask) Monad)
        → ((HaskellFunctor→Functor (HaskellMonad.functor (Monad→HaskellMonad (proj₂ m)))) , HaskellMonad→Monad (Monad→HaskellMonad (proj₂ m)))
        ≡ m
    id₂ (F , monad) = Σ-eq refl $ ≡-to-≅ $ Theory.Monad.Definition.monad-eq (natural-transformation-eq refl)
                    $ natural-transformation-eq $ fun-ext $ λ (A : Type) → fun-ext $ λ x → begin
      HaskellMonad.join (Monad→HaskellMonad monad) x
        ≡⟨⟩
      NaturalTransformation.η (μ monad) A ([ F ]₁ (λ x → x) x)
        ≡⟨ cong (λ X → NaturalTransformation.η (μ monad) A X) (cong (λ X → X x) (Functor.id F)) ⟩
      NaturalTransformation.η (μ monad) A x ∎
