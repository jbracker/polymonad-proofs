
open import Level
open import Function renaming ( _∘_ to _∘F_ )

open import Data.Product

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( refl to hrefl ; sym to hsym ; trans to htrans ; cong to hcong ; cong₂ to hcong₂ )
open ≡-Reasoning

open import Haskell hiding ( Hask )
open import Haskell.Parameterized.Indexed.Monad
open import Haskell.Functor renaming ( Functor to HaskellFunctor ) hiding ( functor-eq ; functor )
open import Theory.Category.Definition
open import Theory.Category.Examples.SetCat
open import Theory.Category.Examples.Codiscrete renaming ( codiscreteCategory to Codisc )
open import Theory.Functor.Definition hiding ( functor )
open import Theory.Functor.Composition
open import Theory.Functor.Properties.IsomorphicHaskellFunctor
open import Theory.Natural.Transformation
open import Theory.Haskell.Parameterized.Indexed.Monad

module Theory.Haskell.Parameterized.Indexed.Monad.Properties.ToHaskellIndexedMonad where

open Category renaming ( id to cat-id )

private
  SetCat' = setCategory {zero}

IndexedMonad→HaskellIndexedMonad : {ℓIxs : Level} {Ixs : Set ℓIxs} 
                                 → (Σ ({i j : Obj (Codisc Ixs)} → Hom (Codisc Ixs) i j → Functor SetCat' SetCat') (IndexedMonad (Codisc Ixs)))
                                 → (Σ (Ixs → Ixs → TyCon) (IxMonad Ixs))
IndexedMonad→HaskellIndexedMonad {ℓIxs} {Ixs} (F , monad) 
  = M , indexed-monad _>>=_ return functor law-right-id law-left-id law-assoc law-monad-fmap
  where
    open IndexedMonad monad renaming ( functor to ix-functor )
    open NaturalTransformation renaming ( η to nat-η )
    
    I = Codisc Ixs
    
    M : Ixs → Ixs → TyCon
    M i j α = [ F (codisc j i) ]₀ α
    
    functor : (i j : Ixs) → HaskellFunctor (M i j)
    functor i j = Functor→HaskellFunctor (F (codisc j i))
    
    _>>=_ : {α β : Type} {i j k : Ixs} → M i j α → (α → M j k β) → M i k β
    _>>=_ {α} {β} {i} {j} {k} ma f = nat-η (μ (codisc k j) (codisc j i)) β ([ F (codisc j i) ]₁ f ma)
    
    return : {α : Type} {i : Ixs} → α → M i i α
    return {α} {i} = nat-η (η i) α
    
    abstract
      law-right-id : {α β : Type} {i j : Ixs} (a : α) (k : α → M i j β)
                   → (return a >>= k) ≡ k a
      law-right-id {α} {β} {i} {j} a k = begin
        ((nat-η (μ (codisc j i) (codisc i i)) β) ∘F (([ F (codisc i i) ]₁ k) ∘F (nat-η (η i) α))) a 
          ≡⟨ cong (λ X → ((nat-η (μ (codisc j i) (codisc i i)) β) ∘F X) a ) (natural (η i)) ⟩
        ((nat-η (μ (codisc j i) (codisc i i)) β) ∘F ((nat-η (η i) ([ F (codisc j i) ]₀ β)) ∘F k)) a 
          ≡⟨ cong (λ X → X (k a)) $ ≅-to-≡ $ η-right-coher ⟩
        k a ∎
    
    abstract
      law-left-id : {α : Type} {i j : Ixs} (m : M i j α) 
                  → (m >>= return) ≡ m
      law-left-id {α} {i} {j} m = begin
        nat-η (μ (codisc j j) (codisc j i)) α ([ F (codisc j i) ]₁ (nat-η (η j) α) m)
          ≡⟨ refl ⟩
        ((nat-η (μ (codisc j j) (codisc j i)) α) ∘F ([ F (codisc j i) ]₁ (nat-η (η j) α))) m
          ≡⟨ cong (λ X → X m) $ ≅-to-≡ $ η-left-coher ⟩
        m ∎

    abstract
      law-assoc : {α β γ : Type} {i j k l : Ixs}
                → (m : M i j α) (f : α → M j k β) (g : β → M k l γ) 
                → (m >>= (λ x → f x >>= g)) ≡ ((m >>= f) >>= g)
      law-assoc {α} {β} {γ} {i} {j} {k} {l} m f g = begin
        nat-η (μ (codisc l j) (codisc j i)) γ ([ F (codisc j i) ]₁ (λ x → f x >>= g) m)
          ≡⟨ refl ⟩
        ((nat-η (μ (codisc l j) (codisc j i)) γ) ∘F ([ F (codisc j i) ]₁ ( (nat-η (μ (codisc l k) (codisc k j)) γ) ∘F (([ F (codisc k j) ]₁ g) ∘F f) ))) m
          ≡⟨ cong (λ X → ((nat-η (μ (codisc l j) (codisc j i)) γ) ∘F X) m) (Functor.compose (F (codisc j i))) ⟩
        ((nat-η (μ (codisc l j) (codisc j i)) γ) ∘F ([ F (codisc j i) ]₁ (nat-η (μ (codisc l k) (codisc k j)) γ) ∘F [ F (codisc j i) ]₁ (([ F (codisc k j) ]₁ g) ∘F f) ) ) m
          ≡⟨ refl ⟩
        (((nat-η (μ (codisc l j) (codisc j i)) γ) ∘F [ F (codisc j i) ]₁ (nat-η (μ (codisc l k) (codisc k j)) γ)) ∘F [ F (codisc j i) ]₁ (([ F (codisc k j) ]₁ g) ∘F f) ) m
          ≡⟨ cong (λ X → (X ∘F [ F (codisc j i) ]₁ (([ F (codisc k j) ]₁ g) ∘F f) ) m) $ ≅-to-≡ $ μ-coher ⟩
        (nat-η (μ (codisc l k) (codisc k i)) γ ∘F nat-η (μ (codisc k j) (codisc j i)) ([ F (codisc l k) ]₀ γ)) ([ F (codisc j i) ]₁ ([ F (codisc k j) ]₁ g ∘F f) m)
          ≡⟨ cong (λ X → (nat-η (μ (codisc l k) (codisc k i)) γ ∘F nat-η (μ (codisc k j) (codisc j i)) ([ F (codisc l k) ]₀ γ)) (X m)) (Functor.compose (F (codisc j i))) ⟩
        (nat-η (μ (codisc l k) (codisc k i)) γ ∘F nat-η (μ (codisc k j) (codisc j i)) ([ F (codisc l k) ]₀ γ)) ([ [ F (codisc j i) ]∘[ F (codisc k j) ] ]₁ g ([ F (codisc j i) ]₁ f m))
          ≡⟨ refl ⟩
        ((nat-η (μ (codisc l k) (codisc k i)) γ) ∘F ((nat-η (μ (codisc k j) (codisc j i)) ([ F (codisc l k) ]₀ γ)) ∘F ([ [ F (codisc j i) ]∘[ F (codisc k j) ] ]₁ g))) ([ F (codisc j i) ]₁ f m)
          ≡⟨ cong (λ X → ((nat-η (μ (codisc l k) (codisc k i)) γ) ∘F X) ([ F (codisc j i) ]₁ f m)) (sym $ natural (μ (codisc k j) (codisc j i))) ⟩
        ((nat-η (μ (codisc l k) (codisc k i)) γ) ∘F (([ F (codisc k i) ]₁ g) ∘F (nat-η (μ (codisc k j) (codisc j i)) β))) ([ F (codisc j i) ]₁ f m)
          ≡⟨ refl ⟩
        nat-η (μ (codisc l k) (codisc k i)) γ ([ F (codisc k i) ]₁ g (m >>= f)) ∎
    
    abstract
      law-monad-fmap : {α β : Type} {i j : Ixs} (f : α → β) (ma : M i j α)
                     → (ma >>= (return ∘F f)) ≡ [ F (codisc j i) ]₁ f ma
      law-monad-fmap {α} {β} {i} {j} f ma = begin
        nat-η (μ (codisc j j) (codisc j i)) β ([ F (codisc j i) ]₁ (nat-η (η j) β ∘F f) ma)
          ≡⟨ refl ⟩
        ((nat-η (μ (codisc j j) (codisc j i)) β) ∘F ([ F (codisc j i) ]₁ (nat-η (η j) β ∘F f))) ma
          ≡⟨ cong (λ X → ((nat-η (μ (codisc j j) (codisc j i)) β) ∘F X) ma) (Functor.compose (F (codisc j i))) ⟩
        ((nat-η (μ (codisc j j) (codisc j i)) β) ∘F ([ F (codisc j i) ]₁ (nat-η (η j) β) ∘F [ F (codisc j i) ]₁ f)) ma
          ≡⟨ cong (λ X → (X ∘F [ F (codisc j i) ]₁ f) ma) $ ≅-to-≡ $ η-left-coher ⟩
        [ F (codisc j i) ]₁ f ma ∎

