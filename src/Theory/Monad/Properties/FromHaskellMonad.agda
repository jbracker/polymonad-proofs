
-- Stdlib
open import Level
open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Data.Product
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Local
open import Extensionality
open import Haskell
open import Haskell.Monad renaming ( Monad to HaskellMonad )
open import Haskell.Functor renaming ( Functor to HaskellFunctor )
open import Theory.Functor
open import Theory.Functor.Composition
open import Theory.Natural.Transformation renaming ( NaturalTransformation to NatTrans )
open import Theory.Monad hiding ( monad )
open import Theory.Functor.IsomorphicHaskellFunctor

module Theory.Monad.Properties.FromHaskellMonad where

HaskellMonad→Monad : {M : TyCon}
                   → (haskMonad : HaskellMonad M)
                   → Monad (HaskellFunctor→Functor (Monad.functor haskMonad))
HaskellMonad→Monad {M} haskMonad = Monad.monad η μ μ-coher η-left-coher η-right-coher
  where
    F = HaskellFunctor→Functor (Monad.functor haskMonad)

    open Haskell.Monad.Monad haskMonad
    
    η : NatTrans Id[ Hask ] F
    η = naturalTransformation (λ A → return) $ λ {A B : Type} {f : A → B} → fun-ext $ λ (x : A) → begin
      ([ F ]₁ f ∘F return) x
        ≡⟨⟩
      fmap f (return x)
        ≡⟨ law-monad-fmap f (return x) ⟩
      return x >>= (return ∘F f)
        ≡⟨ law-left-id x (return ∘F f) ⟩
      return (f x)
        ≡⟨⟩
      (return ∘F [ Id[ Hask ] ]₁ f) x ∎

    μ : NatTrans [ F ]∘[ F ] F
    μ = naturalTransformation (λ A → join) $ λ {A B : Type} {f : A → B} → fun-ext $ λ (x : M (M A)) → begin
      ([ F ]₁ f ∘F join) x
        ≡⟨⟩
      fmap f (x >>= (λ x → x))
        ≡⟨ law-monad-fmap f (join x) ⟩
      (x >>= (λ x → x)) >>= (return ∘F f)
        ≡⟨ sym (law-assoc x (λ x → x) (return ∘F f)) ⟩
      x >>= (λ x → x >>= (return ∘F f))
        ≡⟨ cong (λ X → x >>= X) (fun-ext (λ x → sym (law-left-id (x >>= (return ∘F f)) (λ x → x)))) ⟩
      x >>= (λ x → return (x >>= (return ∘F f)) >>= (λ x → x))
        ≡⟨ law-assoc x (return ∘F (λ x → x >>= (return ∘F f))) (λ x → x) ⟩
      (x >>= (return ∘F (λ x → x >>= (return ∘F f)))) >>= (λ x → x)
        ≡⟨ cong (λ X → X >>= (λ x → x)) (sym (law-monad-fmap (λ x → x >>= (return ∘F f)) x)) ⟩
      (fmap (λ x → x >>= (return ∘F f)) x) >>= (λ x → x)
        ≡⟨ cong (λ X → (fmap X x) >>= (λ x → x)) (sym (fun-ext (law-monad-fmap f))) ⟩
      (fmap (fmap f) x) >>= (λ x → x)
        ≡⟨⟩
      (join ∘F [ [ F ]∘[ F ] ]₁ f) x ∎

    μ-coher : {A : Type}
            → (η⟨ μ ⟩ A) ∘F ([ F ]₁ (η⟨ μ ⟩ A)) ≡ (η⟨ μ ⟩ A) ∘F (η⟨ μ ⟩ [ F ]₀ A)
    μ-coher {A} = fun-ext $ λ (x : M (M (M A))) → begin
      join (fmap join x)
        ≡⟨⟩
      (fmap (λ ma → ma >>= (λ x → x)) x) >>= (λ x → x)
        ≡⟨ cong (λ X → _>>=_ X (λ x → x)) (law-monad-fmap (λ ma → ma >>= (λ x → x)) x) ⟩
      (x >>= (return ∘F (λ ma → ma >>= (λ x → x)))) >>= (λ x → x)
        ≡⟨ sym (law-assoc x (return ∘F (λ ma → ma >>= (λ x → x))) (λ x → x)) ⟩
      x >>= (λ x → return (x >>= (λ x → x)) >>= (λ x → x))
        ≡⟨ cong (λ X → x >>= X) (fun-ext (λ x → law-left-id (x >>= (λ x → x)) (λ x → x))) ⟩
      x >>= (λ x → x >>= (λ x → x))
        ≡⟨ law-assoc x (λ x → x) (λ x → x) ⟩
      (x >>= (λ x → x)) >>= (λ x → x)
        ≡⟨⟩
      join (join x) ∎

    η-left-coher : {A : Type} → η⟨ μ ⟩ A ∘F ([ F ]₁ (η⟨ η ⟩ A)) ≡ η⟨ Id⟨ F ⟩ ⟩ A
    η-left-coher {A} = fun-ext $ λ (x : M A) → begin
      join (fmap return x)
        ≡⟨⟩
      fmap return x >>= (λ x → x)
        ≡⟨ cong (λ X → _>>=_ X (λ x → x)) (law-monad-fmap return x) ⟩
      (x >>= (return ∘F return)) >>= (λ x → x)
        ≡⟨ sym (law-assoc x (return ∘F return) (λ x → x)) ⟩
      x >>= (λ x → return (return x) >>= (λ x → x))
        ≡⟨ cong (λ X → x >>= X) (fun-ext (λ y → law-left-id (return y) (λ x → x))) ⟩
      x >>= return
        ≡⟨ law-right-id x ⟩
      x ∎

    η-right-coher : {A : Type} → η⟨ μ ⟩ A ∘F η⟨ η ⟩ ([ F ]₀ A) ≡ η⟨ Id⟨ F ⟩ ⟩ A
    η-right-coher {A} = fun-ext $ λ (x : M A) → begin
      join (return x)
        ≡⟨⟩
      return x >>= (λ x → x)
        ≡⟨ law-left-id x (λ x → x) ⟩
      x ∎
