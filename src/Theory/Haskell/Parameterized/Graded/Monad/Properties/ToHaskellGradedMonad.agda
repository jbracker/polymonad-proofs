
open import Level
open import Function hiding ( id ; _∘_ )

open import Data.Product

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( refl to hrefl ; sym to hsym ; cong to hcong ; cong₂ to hcong₂ )
open ≡-Reasoning hiding ( _≅⟨_⟩_ )
open ≅-Reasoning renaming ( begin_ to hbegin_ ; _∎ to _∎h ) hiding ( _≡⟨⟩_ ; _≡⟨_⟩_ )

open import Extensionality
open import Haskell hiding ( Hask )
open import Haskell.Functor renaming ( Functor to HaskellFunctor ) hiding ( functor )
open import Haskell.Parameterized.Graded.Monad renaming ( GradedMonad to HaskellGradedMonad ; graded-monad to haskell-graded-monad )
open import Theory.Monoid
open import Theory.Category.Definition
open import Theory.Category.Examples.SetCat
open import Theory.Functor.Definition hiding ( functor )
open import Theory.Functor.Composition
open import Theory.Functor.Properties.IsomorphicHaskellFunctor
open import Theory.Natural.Transformation
open import Theory.Haskell.Parameterized.Graded.Monad

module Theory.Haskell.Parameterized.Graded.Monad.Properties.ToHaskellGradedMonad where

private
  Hask = setCategory {zero}

GradedMonad→HaskellGradedMonad : {ℓMon : Level} {Mon : Set ℓMon} {monoid : Monoid Mon}
                               → (Σ (Mon → Functor Hask Hask) (GradedMonad monoid))
                               → (Σ (Mon → TyCon) (HaskellGradedMonad monoid))
GradedMonad→HaskellGradedMonad {ℓMon} {Mon} {monoid} (F , monad) 
  = M , haskell-graded-monad _>>=_ return functor law-right-id law-left-id law-assoc law-monad-fmap
  where
    open Monoid monoid
    open Category Hask hiding ( left-id ; right-id ; assoc )
    open GradedMonad monad
    open NaturalTransformation renaming ( η to nat-η )
    
    M : Mon → TyCon
    M i α = [ F i ]₀ α
    
    functor : (i : Mon) → HaskellFunctor (M i)
    functor i = Functor→HaskellFunctor (F i)
    
    _>>=_ : {α β : Type} {i j : Mon} → M i α → (α → M j β) → M (i ∙ j) β
    _>>=_ {α} {β} {i} {j} ma f = nat-η (μ {i} {j} ) β ([ F i ]₁ f ma)
    
    return : {α : Type} → α → M ε α
    return {α} = nat-η η α
    
    law-right-id : {α β : Type} {i : Mon} (a : α) (k : α → M i β)
                 → (return a >>= k) ≅ k a
    law-right-id {α} {β} {i} a k = hbegin
      (M (ε ∙ i) β ∋ (nat-η (μ {ε} {i}) β ∘ ([ F ε ]₁ k ∘ nat-η η α)) a)
        ≅⟨ hcong (λ X → ((nat-η (μ {ε} {i}) β) ∘ X) a ) (≡-to-≅ $ natural η) ⟩
      (M (ε ∙ i) β ∋ (nat-η (μ {ε} {i}) β ∘ (nat-η η ([ F i ]₀ β) ∘ k)) a)
        ≅⟨ hrefl ⟩
      (M (ε ∙ i) β ∋ ((nat-η (μ {ε} {i}) β ∘ nat-η η ([ F i ]₀ β)) ∘ k) a)
        ≅⟨ hcong₂ (λ X Y → M X β ∋ ((M i β → M X β) ∋ Y) (k a)) (≡-to-≅ left-id) η-right-coher ⟩
      (M i β ∋ id (k a)) ∎h
    
    law-left-id : {α : Type} {i : Mon} (m : M i α) 
                → (m >>= return) ≅ m
    law-left-id {α} {i} m = hbegin
      nat-η (μ {i} {ε}) α ([ F i ]₁ (nat-η η α) m)
        ≅⟨ hrefl ⟩
      ((nat-η (μ {i} {ε}) α) ∘ ([ F i ]₁ (nat-η η α))) m
        ≅⟨ hcong₂ (λ X Y → M X α ∋ ((M i α → M X α) ∋ Y) m) (≡-to-≅ right-id) η-left-coher ⟩
      (M i α ∋ m) ∎h

    law-assoc : {α β γ : Type} {i j k : Mon}
              → (m : M i α) (f : α → M j β) (g : β → M k γ) 
              → (m >>= (λ x → f x >>= g)) ≅ ((m >>= f) >>= g)
    law-assoc {α} {β} {γ} {i} {j} {k} m f g = hbegin
      (M (i ∙ (j ∙ k)) γ ∋ nat-η (μ {i} {j ∙ k}) γ ([ F i ]₁ (λ x → f x >>= g) m))
        ≅⟨ hrefl ⟩
      (M (i ∙ (j ∙ k)) γ ∋ ((nat-η (μ {i} {j ∙ k}) γ) ∘ ([ F i ]₁ ( (nat-η (μ {j} {k}) γ) ∘ (([ F j ]₁ g) ∘ f) ))) m)
        ≅⟨ hcong (λ X → ((nat-η (μ {i} {j ∙ k}) γ) ∘ X) m) (≡-to-≅ $ Functor.compose (F i)) ⟩
      (M (i ∙ (j ∙ k)) γ ∋ ((nat-η (μ {i} {j ∙ k}) γ) ∘ ([ F i ]₁ (nat-η (μ {j} {k}) γ) ∘ [ F i ]₁ (([ F j ]₁ g) ∘ f) ) ) m)
        ≅⟨ hrefl ⟩
      (M (i ∙ (j ∙ k)) γ ∋ (((nat-η (μ {i} {j ∙ k}) γ) ∘ [ F i ]₁ (nat-η (μ {j} {k}) γ)) ∘ [ F i ]₁ (([ F j ]₁ g) ∘ f) ) m)
        ≅⟨ hcong₂ (λ X Y → M X γ ∋ (Y ∘ [ F i ]₁ (([ F j ]₁ g) ∘ f) ) m) (≡-to-≅ assoc) μ-coher ⟩
      (M ((i ∙ j) ∙ k) γ ∋ (nat-η (μ {i ∙ j} {k}) γ ∘ nat-η (μ {i} {j}) ([ F k ]₀ γ)) ([ F i ]₁ ([ F j ]₁ g ∘ f) m))
        ≅⟨ hcong (λ X → (nat-η (μ {i ∙ j} {k}) γ ∘ nat-η (μ {i} {j}) ([ F k ]₀ γ)) (X m)) (≡-to-≅ $ Functor.compose (F i)) ⟩
      (M ((i ∙ j) ∙ k) γ ∋ (nat-η (μ {i ∙ j} {k}) γ ∘ nat-η (μ {i} {j}) ([ F k ]₀ γ)) ([ [ F i ]∘[ F j ] ]₁ g ([ F i ]₁ f m)))
        ≅⟨ hrefl ⟩
      (M ((i ∙ j) ∙ k) γ ∋ ((nat-η (μ {i ∙ j} {k}) γ) ∘ ((nat-η (μ {i} {j}) ([ F k ]₀ γ)) ∘ ([ [ F i ]∘[ F j ] ]₁ g))) ([ F i ]₁ f m))
        ≅⟨ hcong (λ X → ((nat-η (μ {i ∙ j} {k}) γ) ∘ X) ([ F i ]₁ f m)) (hsym $ ≡-to-≅ $ natural (μ {i} {j})) ⟩
      (M ((i ∙ j) ∙ k) γ ∋ ((nat-η (μ {i ∙ j} {k}) γ) ∘ (([ F (i ∙ j) ]₁ g) ∘ (nat-η (μ {i} {j}) β))) ([ F i ]₁ f m))
        ≅⟨ hrefl ⟩
      (M ((i ∙ j) ∙ k) γ ∋ nat-η (μ {i ∙ j} {k}) γ ([ F (i ∙ j) ]₁ g (m >>= f))) ∎h
    
    law-monad-fmap : {α β : Type} {i : Mon} (f : α → β) (ma : M i α)
                   → (ma >>= (return ∘ f)) ≅ [ F i ]₁ f ma
    law-monad-fmap {α} {β} {i} f ma = hbegin
      nat-η (μ {i} {ε}) β ([ F i ]₁ (nat-η η β ∘ f) ma)
        ≅⟨ hrefl ⟩
      ((nat-η (μ {i} {ε}) β) ∘ ([ F i ]₁ (nat-η η β ∘ f))) ma
        ≅⟨ hcong (λ X → ((nat-η (μ {i} {ε}) β) ∘ X) ma) (≡-to-≅ $ Functor.compose (F i)) ⟩
      ((nat-η (μ {i} {ε}) β) ∘ ([ F i ]₁ (nat-η η β) ∘ [ F i ]₁ f)) ma
        ≅⟨ hcong₂ (λ X Y → M X β ∋ ((M i β → M X β) ∋ Y) ([ F i ]₁ f ma)) (≡-to-≅ right-id) η-left-coher ⟩
      (M i β ∋ [ F i ]₁ f ma) ∎h

