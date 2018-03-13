
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
open import Theory.Functor.Definition
open import Theory.Functor.Composition
open import Theory.Natural.Transformation renaming ( NaturalTransformation to NatTrans )
open import Theory.Monad.Definition hiding ( monad )
open import Theory.Functor.Properties.IsomorphicHaskellFunctor

module Theory.Monad.Properties.FromHaskellMonad where

HaskellMonad→Monad : {M : TyCon}
                   → (haskMonad : HaskellMonad M)
                   → Monad (HaskellFunctor→Functor (HaskellMonad.functor haskMonad))
HaskellMonad→Monad {M} haskMonad = Monad.monad η μ μ-coher η-left-coher η-right-coher
  where
    F = HaskellFunctor→Functor (HaskellMonad.functor haskMonad)
    
    open NatTrans renaming ( η to nat-η )
    open Haskell.Monad.Monad haskMonad
    
    η : NatTrans Id[ Hask ] F
    η = naturalTransformation (λ A → return) nat
      where
        abstract 
          nat : {A B : Type} {f : A → B} → ([ F ]₁ f ∘F return) ≡ (return ∘F [ Id[ Hask ] ]₁ f)
          nat {A} {B} {f} = fun-ext $ λ (x : A) → begin
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
    μ = naturalTransformation (λ A → join) nat
      where
        abstract
          nat : {A B : Type} {f : A → B} → ([ F ]₁ f ∘F join) ≡ (join ∘F [ [ F ]∘[ F ] ]₁ f)
          nat {A} {B} {f} = fun-ext $ λ (x : M (M A)) → begin
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

    abstract
      μ-coher : {A : Type}
              → (nat-η μ A) ∘F ([ F ]₁ (nat-η μ A)) ≡ (nat-η μ A) ∘F (nat-η μ ([ F ]₀ A))
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

    abstract
      η-left-coher : {A : Type} → nat-η μ A ∘F ([ F ]₁ (nat-η η A)) ≡ nat-η Id⟨ F ⟩ A
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
    
    abstract
      η-right-coher : {A : Type} → nat-η μ A ∘F nat-η η ([ F ]₀ A) ≡ nat-η Id⟨ F ⟩ A
      η-right-coher {A} = fun-ext $ λ (x : M A) → begin
        join (return x)
          ≡⟨⟩
        return x >>= (λ x → x)
          ≡⟨ law-left-id x (λ x → x) ⟩
        x ∎
