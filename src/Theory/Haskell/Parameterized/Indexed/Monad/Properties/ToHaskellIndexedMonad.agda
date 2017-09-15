
open import Level
open import Function hiding ( id ; _∘_ )

open import Data.Product

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Haskell hiding ( Hask )
open import Haskell.Parameterized.Indexed.Monad
open import Haskell.Functor renaming ( Functor to HaskellFunctor ) hiding ( functor-eq ; functor )
open import Theory.Category.Definition
open import Theory.Category.Examples.SetCat
open import Theory.Functor.Definition hiding ( functor )
open import Theory.Functor.Composition
open import Theory.Functor.Properties.IsomorphicHaskellFunctor
open import Theory.Natural.Transformation
open import Theory.Haskell.Parameterized.Indexed.Monad

module Theory.Haskell.Parameterized.Indexed.Monad.Properties.ToHaskellIndexedMonad where

private
  Hask = setCategory {zero}

IndexedMonad→HaskellIndexedMonad : {ℓIxs : Level} {Ixs : Set ℓIxs} 
                                 → (Σ (Ixs → Ixs → Functor Hask Hask) (IndexedMonad Ixs))
                                 → (Σ (Ixs → Ixs → TyCon) (IxMonad Ixs))
IndexedMonad→HaskellIndexedMonad {ℓIxs} {Ixs} (F , monad) 
  = M , indexed-monad _>>=_ return functor law-right-id law-left-id law-assoc law-monad-fmap
  where
    open Category Hask
    open IndexedMonad monad
    open NaturalTransformation renaming ( η to nat-η )
    
    M : Ixs → Ixs → TyCon
    M i j α = [ F j i ]₀ α
    
    functor : (i j : Ixs) → HaskellFunctor (M i j)
    functor i j = Functor→HaskellFunctor (F j i)
    
    _>>=_ : {α β : Type} {i j k : Ixs} → M i j α → (α → M j k β) → M i k β
    _>>=_ {α} {β} {i} {j} {k} ma f = nat-η (μ {k} {j} {i}) β ([ F j i ]₁ f ma)
    
    return : {α : Type} {i : Ixs} → α → M i i α
    return {α} {i} = nat-η η α
    
    abstract
      law-right-id : {α β : Type} {i j : Ixs} (a : α) (k : α → M i j β)
                   → (return a >>= k) ≡ k a
      law-right-id {α} {β} {i} {j} a k = begin
        ((nat-η (μ {j} {i} {i}) β) ∘ (([ F i i ]₁ k) ∘ (nat-η η α))) a 
          ≡⟨ cong (λ X → ((nat-η (μ {j} {i} {i}) β) ∘ X) a ) (natural η) ⟩
        ((nat-η (μ {j} {i} {i}) β) ∘ ((nat-η η ([ F j i ]₀ β)) ∘ k)) a 
          ≡⟨ cong (λ X → X (k a)) η-right-coher ⟩
        k a ∎
    
    abstract
      law-left-id : {α : Type} {i j : Ixs} (m : M i j α) 
                  → (m >>= return) ≡ m
      law-left-id {α} {i} {j} m = begin
        nat-η (μ {j} {j} {i}) α ([ F j i ]₁ (nat-η η α) m)
          ≡⟨ refl ⟩
        ((nat-η (μ {j} {j} {i}) α) ∘ ([ F j i ]₁ (nat-η η α))) m
          ≡⟨ cong (λ X → X m) η-left-coher ⟩
        m ∎

    abstract
      law-assoc : {α β γ : Type} {i j k l : Ixs}
                → (m : M i j α) (f : α → M j k β) (g : β → M k l γ) 
                → (m >>= (λ x → f x >>= g)) ≡ ((m >>= f) >>= g)
      law-assoc {α} {β} {γ} {i} {j} {k} {l} m f g = begin
        nat-η (μ {l} {j} {i}) γ ([ F j i ]₁ (λ x → f x >>= g) m)
          ≡⟨ refl ⟩
        ((nat-η (μ {l} {j} {i}) γ) ∘ ([ F j i ]₁ ( (nat-η (μ {l} {k} {j}) γ) ∘ (([ F k j ]₁ g) ∘ f) ))) m
          ≡⟨ cong (λ X → ((nat-η (μ {l} {j} {i}) γ) ∘ X) m) (Functor.compose (F j i)) ⟩
        ((nat-η (μ {l} {j} {i}) γ) ∘ ([ F j i ]₁ (nat-η (μ {l} {k} {j}) γ) ∘ [ F j i ]₁ (([ F k j ]₁ g) ∘ f) ) ) m
          ≡⟨ refl ⟩
        (((nat-η (μ {l} {j} {i}) γ) ∘ [ F j i ]₁ (nat-η (μ {l} {k} {j}) γ)) ∘ [ F j i ]₁ (([ F k j ]₁ g) ∘ f) ) m
          ≡⟨ cong (λ X → (X ∘ [ F j i ]₁ (([ F k j ]₁ g) ∘ f) ) m) μ-coher ⟩
        (nat-η (μ {l} {k} {i}) γ ∘ nat-η (μ {k} {j} {i}) ([ F l k ]₀ γ)) ([ F j i ]₁ ([ F k j ]₁ g ∘ f) m)
          ≡⟨ cong (λ X → (nat-η (μ {l} {k} {i}) γ ∘ nat-η (μ {k} {j} {i}) ([ F l k ]₀ γ)) (X m)) (Functor.compose (F j i)) ⟩
        (nat-η (μ {l} {k} {i}) γ ∘ nat-η (μ {k} {j} {i}) ([ F l k ]₀ γ)) ([ [ F j i ]∘[ F k j ] ]₁ g ([ F j i ]₁ f m))
          ≡⟨ refl ⟩
        ((nat-η (μ {l} {k} {i}) γ) ∘ ((nat-η (μ {k} {j} {i}) ([ F l k ]₀ γ)) ∘ ([ [ F j i ]∘[ F k j ] ]₁ g))) ([ F j i ]₁ f m)
          ≡⟨ cong (λ X → ((nat-η (μ {l} {k} {i}) γ) ∘ X) ([ F j i ]₁ f m)) (sym $ natural (μ {k} {j} {i})) ⟩
        ((nat-η (μ {l} {k} {i}) γ) ∘ (([ F k i ]₁ g) ∘ (nat-η (μ {k} {j} {i}) β))) ([ F j i ]₁ f m)
          ≡⟨ refl ⟩
        nat-η (μ {l} {k} {i}) γ ([ F k i ]₁ g (m >>= f)) ∎
    
    abstract
      law-monad-fmap : {α β : Type} {i j : Ixs} (f : α → β) (ma : M i j α)
                     → (ma >>= (return ∘ f)) ≡ [ F j i ]₁ f ma
      law-monad-fmap {α} {β} {i} {j} f ma = begin
        nat-η (μ {j} {j} {i}) β ([ F j i ]₁ (nat-η η β ∘ f) ma)
          ≡⟨ refl ⟩
        ((nat-η (μ {j} {j} {i}) β) ∘ ([ F j i ]₁ (nat-η η β ∘ f))) ma
          ≡⟨ cong (λ X → ((nat-η (μ {j} {j} {i}) β) ∘ X) ma) (Functor.compose (F j i)) ⟩
        ((nat-η (μ {j} {j} {i}) β) ∘ ([ F j i ]₁ (nat-η η β) ∘ [ F j i ]₁ f)) ma
          ≡⟨ cong (λ X → (X ∘ [ F j i ]₁ f) ma) η-left-coher ⟩
        [ F j i ]₁ f ma ∎
