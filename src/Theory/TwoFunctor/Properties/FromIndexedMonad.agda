
-- Stdlib
open import Level
open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Data.Unit
open import Data.Product renaming ( _,_ to _,'_ )
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality 
  renaming ( refl to hrefl; sym to hsym ; trans to htrans ; cong to hcong ; cong₂ to hcong₂ ; subst to hsubst ; subst₂ to hsubst₂ ; proof-irrelevance to hproof-irrelevance )
open ≡-Reasoning hiding ( _≅⟨_⟩_ )
open ≅-Reasoning hiding ( _≡⟨_⟩_ ; _≡⟨⟩_ ) renaming ( begin_ to hbegin_ ; _∎ to _∎h)

-- Local
open import Extensionality
open import Utilities
open import Haskell
open import Haskell.Functor hiding ( functor ) renaming ( Functor to HaskellFunctor )
open import Haskell.Parameterized.Indexed.Monad
open import Theory.Triple
open import Theory.Category.Definition
open import Theory.Category.Examples
open import Theory.Functor.Definition hiding ( functor )
open import Theory.Functor.Composition
open import Theory.Functor.Properties.IsomorphicHaskellFunctor
open import Theory.Natural.Transformation
open import Theory.Natural.Transformation.Examples
open import Theory.TwoCategory.Definition
open import Theory.TwoCategory.Examples
open import Theory.TwoCategory.Examples.CodiscreteHomCat
open import Theory.TwoCategory.ExampleProperties
open import Theory.TwoFunctor.ConstZeroCell

open Category
open StrictTwoCategory

module Theory.TwoFunctor.Properties.FromIndexedMonad where

IndexedMonad→LaxTwoFunctor
  : {ℓ : Level}
  → (Ixs : Set ℓ)
  → (M : Ixs → Ixs → TyCon)
  → (monad : IxMonad Ixs M)
  → ConstLaxTwoFunctor (codiscreteHomCatTwoCategory (codiscreteCategory Ixs)) (Cat {suc zero} {zero}) (Hask {zero})
IndexedMonad→LaxTwoFunctor {ℓ} Ixs M monad = record
  { P₁ = λ {i} {j} → P {i} {j}
  ; η = λ {i} → η {i}
  ; μ = λ {i} {j} {k} {_} {_} → μ {i} {j} {k}
  ; laxFunId₁ = λ {i} {j} {_} → lawFunId₁ {i} {j}
  ; laxFunId₂ = λ {i} {j} {_} → lawFunId₂ {i} {j}
  ; laxFunAssoc = λ {i} {j} {k} {l} {_} {_} {_} → lawFunAssoc {i} {j} {k} {l}
  }
  where
    Ixs₁ = codiscreteCategory Ixs
    Ixs₂ = codiscreteHomCatTwoCategory Ixs₁
    Cat' = Cat {suc zero} {zero}
    Hask' = Hask {zero}

    _∘Ixs_ = Category._∘_ Ixs₁

    open IxMonad monad
    open NaturalTransformation renaming ( η to nat-η ; natural to nat-natural )
    
    P : {i j : Ixs} → Functor (HomCat Ixs₂ i j) (HomCat Cat' Hask Hask)
    P {i} {j} = Functor.functor P₀ P₁ refl refl
      where
        P₀ : Obj (HomCat Ixs₂ i j) → Obj (HomCat Cat' Hask Hask)
        P₀ (lift tt) = HaskellFunctor→Functor (functor j i)
        
        P₁ : {a b : Obj (HomCat Ixs₂ i j)} → Hom (HomCat Ixs₂ i j) a b → Hom (HomCat Cat' Hask Hask) (P₀ a) (P₀ b)
        P₁ {lift tt} {lift tt} (lift tt) = Id⟨ P₀ (lift tt) ⟩
    
    η : {i : Ixs} → NaturalTransformation Id[ Hask' ] ([ P {i} {i} ]₀ (lift tt))
    η {i} = naturalTransformation (λ α x → return {α} {i} x) $ fun-ext $ λ a → natural a
      where
        natural : {α β : Type} {f : α → β} → (a : α)
                → fmap {i = i} f (return a) ≡ return (f a)
        natural {α} {β} {f} a = begin
          fmap f (return a) 
            ≡⟨ sym (law-monad-fmap f (return a)) ⟩
          return a >>= (return ∘F f)
            ≡⟨ law-right-id a (return ∘F f) ⟩
          return (f a) ∎
    
    μ : {i j k : Ixs} → NaturalTransformation ([ [ P {j} {k} ]₀ (lift tt) ]∘[ [ P {i} {j} ]₀ (lift tt) ]) ([ P {i} {k} ]₀ (lift tt))
    μ {i} {j} {k} = naturalTransformation (λ α mma → join {α} {k} {j} {i} mma) $ λ {α β} {f} → fun-ext $ λ mma → natural {α} {β} {f} mma 
      where
        natural : {α β : Type} {f : α → β} → (mma : M k j (M j i α)) → fmap {α} {β} {k} {i} f (join {α} {k} {j} {i} mma) ≡ join (fmap (fmap f) mma)
        natural {α} {β} {f} mma = begin
          fmap f (mma >>= (λ x → x)) 
            ≡⟨ sym (law-monad-fmap f (mma >>= (λ x → x))) ⟩
          (mma >>= (λ x → x)) >>= (return ∘F f)
            ≡⟨ sym (law-assoc mma (λ z → z) (return ∘F f)) ⟩
          mma >>= (λ ma → ma >>= (return ∘F f))
            ≡⟨ cong (λ X → mma >>= X) (fun-ext (λ ma → law-monad-fmap f ma)) ⟩
          mma >>= fmap f
            ≡⟨ cong (λ X → mma >>= X) (fun-ext (λ ma → sym (law-right-id (fmap f ma) (λ x → x)))) ⟩
          mma >>= (λ ma → return (fmap f ma) >>= (λ x → x))
            ≡⟨ law-assoc mma (return ∘F fmap f) (λ x → x) ⟩
          (mma >>= (return ∘F fmap f)) >>= (λ x → x)
            ≡⟨ cong (λ X → _>>=_ X (λ x → x)) (law-monad-fmap (fmap f) mma) ⟩
          fmap (fmap f) mma >>= (λ x → x) ∎
    
    lawFunId₁ : {i j : Ixs}
              → ⟨ Id⟨ [ P {i} {j} ]₀ (lift tt) ⟩ ⟩∘ᵥ⟨ ⟨ μ {i} {i} {j} ⟩∘ᵥ⟨ ⟨ Id⟨ [ P {i} {j} ]₀ (lift tt) ⟩ ⟩∘ₕ⟨ η {i} ⟩ ⟩ ⟩ ≡ Id⟨ [ P {i} {j} ]₀ (lift tt) ⟩
    lawFunId₁ {i} {j} = natural-transformation-eq $ fun-ext $ λ (α : Type) → fun-ext $ λ (ma : M j i α) → begin
      join (fmap return ma)
        ≡⟨⟩
      fmap return ma >>= (λ x → x)
        ≡⟨ cong (λ X → X >>= (λ x → x)) (sym (law-monad-fmap return ma)) ⟩
      (ma >>= (return ∘F return)) >>= (λ x → x)
        ≡⟨ sym (law-assoc ma (return ∘F return) (λ x → x)) ⟩
      ma >>= (λ ma' → return (return ma') >>= (λ x → x))
        ≡⟨ cong (λ X → ma >>= X) (fun-ext (λ ma' → law-right-id (return ma') (λ x → x))) ⟩
      ma >>= return
        ≡⟨ law-left-id ma ⟩
      ma ∎
    
    lawFunId₂ : {i j : Ixs}-- tt =  ρ Ixs₂ (lift tt)
              → ⟨ Id⟨ [ P {i} {j} ]₀ (lift tt) ⟩ ⟩∘ᵥ⟨ ⟨ μ {i} {j} {j} ⟩∘ᵥ⟨ ⟨ η {j} ⟩∘ₕ⟨ Id⟨ [ P {i} {j} ]₀ (lift tt) ⟩ ⟩ ⟩ ⟩ ≡ ρ Cat' ([ P {i} {j} ]₀ (lift tt))
    lawFunId₂ {i} {j} = natural-transformation-eq $ fun-ext $ λ (α : Type) → fun-ext $ λ (ma : M j i α) → begin
      join (return ma)
        ≡⟨⟩
      return ma >>= (λ x → x)
        ≡⟨ law-right-id ma (λ x → x) ⟩
      ma
        ≡⟨ sym (≅-to-≡ (het-cat-ρ-id {F = [ P {i} {j} ]₀ (lift tt)} α ma)) ⟩
      (nat-η (ρ Cat' ([ P {i} {j} ]₀ (lift tt))) α) ma ∎

    lawFunAssoc : {i j k l : Ixs}
                → ⟨ Id⟨ [ P {i} {l} ]₀ (lift tt) ⟩ ⟩∘ᵥ⟨ ⟨ μ {i} {k} {l} ⟩∘ᵥ⟨ ⟨ Id⟨ [ P {k} {l} ]₀ (lift tt) ⟩ ⟩∘ₕ⟨ μ {i} {j} {k} ⟩ ⟩ ⟩
                ≡ ⟨ μ {i} {j} {l} ⟩∘ᵥ⟨ ⟨ ⟨ μ {j} {k} {l} ⟩∘ₕ⟨ Id⟨ [ P {i} {j} ]₀ (lift tt) ⟩ ⟩ ⟩∘ᵥ⟨ α Cat' ([ P {i} {j} ]₀ (lift tt)) ([ P {j} {k} ]₀ (lift tt)) ([ P {k} {l} ]₀ (lift tt)) ⟩ ⟩
    lawFunAssoc {i} {j} {k} {l} = natural-transformation-eq $ fun-ext $ λ (A : Type) → fun-ext $ λ (ma : M l k (M k j (M j i A))) → begin
      join {A} {l} {k} {i} (fmap (join {A} {k} {j} {i}) ma)
        ≡⟨⟩
      fmap (join {A} {k} {j} {i}) ma >>= (λ x → x)
        ≡⟨ cong (λ X → X >>= (λ x → x)) (sym (law-monad-fmap join ma)) ⟩
      (ma >>= (return ∘F join {A} {k} {j} {i})) >>= (λ x → x)
        ≡⟨ sym (law-assoc ma (return ∘F join) (λ x → x)) ⟩
      ma >>= (λ mma → return (join {A} {k} {j} {i} mma) >>= (λ x → x))
        ≡⟨ cong (λ X → ma >>= X) (fun-ext (λ mma → law-right-id (join mma) (λ x → x))) ⟩
      ma >>= (λ mma → mma >>= (λ x → x))
        ≡⟨ cong (λ X → X ma >>= (λ mma → mma >>= (λ x → x))) (sym (HaskellFunctor.law-id (functor l k))) ⟩
      fmap (λ x → x) ma >>= (λ ma → ma >>= (λ x → x))
        ≡⟨ cong (λ X → fmap X ma >>= (λ mma → mma >>= (λ x → x))) (sym (HaskellFunctor.law-id (functor k j))) ⟩
      fmap (fmap (λ x → x)) ma >>= (λ ma → ma >>= (λ x → x))
        ≡⟨ law-assoc (fmap (fmap (λ x → x)) ma) (λ x → x) (λ x → x) ⟩
      (fmap (fmap (λ x → x)) ma >>= (λ x → x)) >>= (λ x → x)
        ≡⟨⟩
      join {A} {l} {j} {i} (join {M j i A} {l} {k} {j} (fmap (fmap (λ x → x)) ma))
        ≡⟨ cong (λ X → join {A} {l} {j} {i} (join {M j i A} {l} {k} {j} (fmap (fmap (λ x → x)) X))) (sym (≅-to-≡ (het-cat-α-id {F = [ P {i} {j} ]₀ (lift tt)} {[ P {j} {k} ]₀ (lift tt)} {[ P {k} {l} ]₀ (lift tt)} A ma))) ⟩
      join {A} {l} {j} {i} (join {M j i A} {l} {k} {j} (fmap (fmap (λ x → x)) ((nat-η (α Cat' ([ P {i} {j} ]₀ (lift tt)) ([ P {j} {k} ]₀ (lift tt)) ([ P {k} {l} ]₀ (lift tt))) A) ma))) ∎
