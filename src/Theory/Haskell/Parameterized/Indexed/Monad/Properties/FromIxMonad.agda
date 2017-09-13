
open import Level
open import Function hiding ( id ; _∘_ )

open import Data.Product

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Extensionality
open import Haskell hiding ( Hask )
open import Haskell.Parameterized.Indexed.Monad
open import Theory.Category.Definition
open import Theory.Category.Examples.SetCat
open import Theory.Functor.Definition hiding ( functor )
open import Theory.Functor.Composition
open import Theory.Functor.Properties.IsomorphicHaskellFunctor
open import Theory.Natural.Transformation
open import Theory.Haskell.Parameterized.Indexed.Monad

module Theory.Haskell.Parameterized.Indexed.Monad.Properties.FromIxMonad where

private
  Hask = setCategory {zero}

IxMonad→IndexedMonad : {ℓIxs : Level} {Ixs : Set ℓIxs} 
                     → (Σ (Ixs → Ixs → TyCon) (IxMonad Ixs))
                     → (Σ (Ixs → Ixs → Functor Hask Hask) (IndexedMonad Ixs))
IxMonad→IndexedMonad {ℓIxs} {Ixs} (M , monad) 
  = F , indexed-monad η μ μ-coher η-left-coher η-right-coher
  where
    open IxMonad monad
    open Category Hask
    open NaturalTransformation renaming ( η to nat-η )
    
    F : Ixs → Ixs → Functor Hask Hask
    F i j = HaskellFunctor→Functor (functor j i)
    
    η : {i : Ixs} → NaturalTransformation Id[ Hask ] (F i i)
    η {i} = naturalTransformation (λ α → return {α} {i}) $ λ {α β} {f} → begin
      fmap f ∘ return 
        ≡⟨ fun-ext (λ ma → sym (law-monad-fmap f (return ma))) ⟩
      (λ ma → (return ma) >>= (return ∘ f)) 
        ≡⟨ fun-ext (λ ma → law-right-id ma (return ∘ f)) ⟩
      return ∘ f ∎
    
    μ : {i j k : Ixs} → NaturalTransformation [ F j k ]∘[ F i j ] (F i k)
    μ {i} {j} {k} = naturalTransformation (λ α → join {α} {k} {j} {i}) $ λ {α β} {f} → begin
      fmap f ∘ join 
        ≡⟨ refl ⟩
      (λ ma → fmap f (ma >>= id))
        ≡⟨ fun-ext (λ ma → sym (law-monad-fmap f (ma >>= id))) ⟩
      (λ ma → (ma >>= id) >>= (return ∘ f))
        ≡⟨ fun-ext (λ ma → sym (law-assoc ma id (return ∘ f))) ⟩
      (λ ma → ma >>= (λ x → x >>= (return ∘ f)))
        ≡⟨ fun-ext (λ ma → cong (λ X → ma >>= X) (fun-ext (λ x → sym (law-right-id (x >>= (return ∘ f)) id)))) ⟩
      (λ ma → ma >>= (λ x → return (x >>= (return ∘ f)) >>= id))
        ≡⟨ fun-ext (λ ma → law-assoc ma (λ a → return (a >>= (return ∘ f))) id) ⟩
      (λ ma → (ma >>= (λ a → return (a >>= (return ∘ f)))) >>= id)
        ≡⟨ fun-ext (λ ma → cong (λ X → (ma >>= (return ∘ X)) >>= id) (fun-ext (λ x → law-monad-fmap f x))) ⟩
      (λ ma → (ma >>= (return ∘ (fmap f))) >>= id)
        ≡⟨ fun-ext (λ ma → cong (λ X → X >>= id) (law-monad-fmap (fmap f) ma)) ⟩
      (λ ma → (fmap (fmap f) ma) >>= id)
        ≡⟨ refl ⟩
      join ∘ fmap (fmap f) ∎
    
    μ-coher : {i j k l : Ixs} {x : Type}
            → nat-η (μ {i} {k} {l}) x ∘ [ F k l ]₁ (nat-η (μ {i} {j} {k}) x) 
            ≡ nat-η (μ {i} {j} {l}) x ∘ nat-η (μ {j} {k} {l}) ([ F i j ]₀ x)
    μ-coher {i} {j} {k} {l} {α} = begin
      join ∘ fmap join
        ≡⟨ refl ⟩
      (λ ma → (fmap (λ a → a >>= id) ma) >>= id)
        ≡⟨ fun-ext (λ ma → cong (λ X → X >>= id) (sym (law-monad-fmap (λ a → a >>= id) ma))) ⟩
      (λ ma → (ma >>= (return ∘ (λ a → a >>= id))) >>= id)
        ≡⟨ fun-ext (λ ma → sym (law-assoc ma (return ∘ (λ a → a >>= id)) id)) ⟩
      (λ ma → ma >>= (λ x → return (x >>= id) >>= id))
        ≡⟨ fun-ext (λ ma → cong (λ X → ma >>= X) (fun-ext (λ x → law-right-id (x >>= id) id))) ⟩
      (λ ma → ma >>= (λ x → x >>= id))
        ≡⟨ fun-ext (λ ma → law-assoc ma id id) ⟩
      (λ ma → (ma >>= id) >>= id)
        ≡⟨ refl ⟩
      join ∘ join ∎
    
    η-left-coher : {i j : Ixs} {x : Type}
                 → nat-η (μ {i} {i} {j}) x ∘ [ F i j ]₁ (nat-η η x) ≡ nat-η (Id⟨ F i j ⟩) x
    η-left-coher {i} {j} {α} = begin
      join ∘ fmap return
        ≡⟨ refl ⟩
      (λ ma → fmap return ma >>= id)
        ≡⟨ fun-ext (λ ma → cong (λ X → X >>= id) (sym $ law-monad-fmap return ma )) ⟩
      (λ ma → (ma >>= (return ∘ return)) >>= id)
        ≡⟨ fun-ext (λ ma → sym (law-assoc ma (return ∘ return) id)) ⟩
      (λ ma → ma >>= (λ x → return (return x) >>= id))
        ≡⟨ fun-ext (λ ma → cong (λ X → ma >>= X) (fun-ext (λ x → law-right-id (return x) id))) ⟩
      (λ ma → ma >>= return)
        ≡⟨ fun-ext (λ ma → law-left-id ma) ⟩
      id ∎
    
    η-right-coher : {i j : Ixs} {x : Type}
                  → nat-η (μ {i} {j} {j}) x ∘ nat-η (η {j}) ([ F i j ]₀ x) ≡ nat-η (Id⟨ F i j ⟩) x
    η-right-coher {i} {j} {α} = begin
      join ∘ return
        ≡⟨ refl ⟩
      (λ ma → return ma >>= id)
        ≡⟨ fun-ext (λ ma → law-right-id ma id) ⟩
      id ∎

