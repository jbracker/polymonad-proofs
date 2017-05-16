
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

open import Theory.Functor
open import Theory.Functor.Composition
open import Theory.Functor.IsomorphicHaskellFunctor
open import Theory.Monad hiding ( monad )
open import Theory.Monad.Properties.FromHaskellMonad
open import Theory.Monad.Properties.ToHaskellMonad
open import Theory.Natural.Transformation

module Theory.Monad.Properties.IsomorphicHaskellMonad where

Monad↔HaskellMonad : (Σ (Functor (Hask {zero}) (Hask {zero})) Monad) ↔ (Σ TyCon HaskellMonad)
Monad↔HaskellMonad = bijection
  (λ FM → [ proj₁ FM  ]₀ , Monad→HaskellMonad (proj₂ FM))
  (λ FM → (HaskellFunctor→Functor (Monad.functor (proj₂ FM))) , (HaskellMonad→Monad (proj₂ FM)))
  id₁ id₂
  where  
    id₁ : (m : Σ TyCon HaskellMonad)
        → ([ HaskellFunctor→Functor (Monad.functor (proj₂ m)) ]₀ , Monad→HaskellMonad (HaskellMonad→Monad (proj₂ m)))
        ≡ m
    id₁ (M , haskMonad) = Σ-eq refl $ ≡-to-≅ $ Haskell.Monad.monad-eq bind-eq (applicative-eq return-pure-eq ap-eq (Haskell.Functor.functor-eq refl))
      where
        bind-eq : (λ {α β} → Monad._>>=_ (Monad→HaskellMonad (HaskellMonad→Monad haskMonad)) {α} {β}) ≡ Monad._>>=_ haskMonad
        bind-eq = implicit-fun-ext $ λ α → implicit-fun-ext $ λ β → fun-ext $ λ ma → fun-ext $ λ f → begin
          (Monad→HaskellMonad (HaskellMonad→Monad haskMonad) Monad.>>= ma) f
            ≡⟨⟩
          Monad.join haskMonad (Monad.fmap haskMonad f ma)
            ≡⟨⟩
          Monad._>>=_ haskMonad (Monad.fmap haskMonad f ma) (λ x → x)
            ≡⟨ cong (λ X → Monad._>>=_ haskMonad X (λ x → x)) (Monad.law-monad-fmap haskMonad f ma) ⟩
          Monad._>>=_ haskMonad (Monad._>>=_ haskMonad ma (Monad.return haskMonad ∘F f)) (λ x → x)
            ≡⟨ sym (Monad.law-assoc haskMonad ma (Monad.return haskMonad ∘F f) (λ x → x)) ⟩
          Monad._>>=_ haskMonad ma (λ x → Monad._>>=_ haskMonad (Monad.return haskMonad (f x)) (λ x → x))
            ≡⟨ cong (λ X → Monad._>>=_ haskMonad ma X) (fun-ext (λ x → Monad.law-left-id haskMonad (f x) (λ x → x))) ⟩
          Monad._>>=_ haskMonad ma f ∎
        
        return-pure-eq : (λ {α} → Monad.return (Monad→HaskellMonad (HaskellMonad→Monad haskMonad)) {α}) ≡ Applicative.pure (Monad.applicative haskMonad)
        return-pure-eq = implicit-fun-ext $ λ α → fun-ext $ λ a → refl
        
        ap-eq : (λ {α β} → Monad._<*>_ (Monad→HaskellMonad (HaskellMonad→Monad haskMonad)) {α} {β}) ≡ Applicative._<*>_ (Monad.applicative haskMonad)
        ap-eq = implicit-fun-ext $ λ α → implicit-fun-ext $ λ β → fun-ext $ λ f → fun-ext $ λ a → begin
          (Monad.applicative (Monad→HaskellMonad (HaskellMonad→Monad haskMonad)) Applicative.<*> f) a
            ≡⟨⟩
          Monad.join haskMonad (Monad.fmap haskMonad (λ f → Monad.fmap haskMonad f a) f)
            ≡⟨⟩
          Monad._>>=_ haskMonad (Monad.fmap haskMonad (λ f → Monad.fmap haskMonad f a) f) (λ x → x)
            ≡⟨ cong (λ X → Monad._>>=_ haskMonad X (λ x → x)) (Monad.law-monad-fmap haskMonad (λ f → Monad.fmap haskMonad f a) f) ⟩
          Monad._>>=_ haskMonad (Monad._>>=_ haskMonad f (Monad.return haskMonad ∘F (λ f → Monad.fmap haskMonad f a))) (λ x → x)
            ≡⟨ sym (Monad.law-assoc haskMonad f (Monad.return haskMonad ∘F (λ f → Monad.fmap haskMonad f a)) (λ x → x)) ⟩
          Monad._>>=_ haskMonad f (λ x → Monad._>>=_ haskMonad (Monad.return haskMonad (Monad.fmap haskMonad x a)) (λ x → x))
            ≡⟨ cong (λ X → Monad._>>=_ haskMonad f X) (fun-ext (λ x → Monad.law-left-id haskMonad (Monad.fmap haskMonad x a) (λ x → x))) ⟩
          Monad._>>=_ haskMonad f (λ f → Monad.fmap haskMonad f a)
            ≡⟨ sym (Monad.law-monad-ap haskMonad f a) ⟩
          Applicative._<*>_ (Monad.applicative haskMonad) f a ∎

    open Theory.Monad.Monad

    id₂ : (m : Σ (Functor Hask Hask) Monad)
        → (HaskellFunctor→Functor (Monad.functor (Monad→HaskellMonad (proj₂ m)))) , HaskellMonad→Monad (Monad→HaskellMonad (proj₂ m))
        ≡ m
    id₂ (F , monad) = Σ-eq refl $ ≡-to-≅ $ Theory.Monad.monad-eq (natural-transformation-eq refl)
                    $ natural-transformation-eq $ fun-ext $ λ (A : Type) → fun-ext $ λ x → begin
      Monad.join (Monad→HaskellMonad monad) x
        ≡⟨⟩
      NaturalTransformation.η (μ monad) A ([ F ]₁ (λ x → x) x)
        ≡⟨ cong (λ X → NaturalTransformation.η (μ monad) A X) (cong (λ X → X x) (Functor.id F)) ⟩
      NaturalTransformation.η (μ monad) A x ∎
