
open import Level
open import Function hiding ( id ; _∘_ )

open import Data.Product

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality hiding ( sym ; trans ; cong )
open ≡-Reasoning

open import Equality
open import Extensionality
open import Bijection hiding ( refl ; sym ; trans )
open import Haskell hiding ( Hask )
open import Haskell.Functor renaming ( Functor to HaskellFunctor ; functor-eq to hask-functor-eq ) hiding ( functor )
open import Haskell.Parameterized.Indexed.Monad renaming ( indexed-monad-eq to hask-indexed-monad-eq )
open import Theory.Category.Definition
open import Theory.Category.Examples.SetCat
open import Theory.Functor.Definition
open import Theory.Natural.Transformation
open import Theory.Haskell.Parameterized.Indexed.Monad
open import Theory.Haskell.Parameterized.Indexed.Monad.Equality
open import Theory.Haskell.Parameterized.Indexed.Monad.Properties.FromIxMonad
open import Theory.Haskell.Parameterized.Indexed.Monad.Properties.ToIxMonad

module Theory.Haskell.Parameterized.Indexed.Monad.Properties.IsomorphicIxMonad where

private
  Hask = setCategory {zero}

IxMonad↔IndexedMonad : {ℓIxs : Level} {Ixs : Set ℓIxs} 
                     → (Σ (Ixs → Ixs → TyCon) (IxMonad Ixs))
                     ↔ (Σ (Ixs → Ixs → Functor Hask Hask) (IndexedMonad Ixs))
IxMonad↔IndexedMonad {ℓIxs} {Ixs} = bijection IxMonad→IndexedMonad IndexedMonad→IxMonad l→r→l r→l→r
  where
    open NaturalTransformation renaming ( η to nat-η )
    
    abstract
      l→r→l : (b : Σ (Ixs → Ixs → Functor Hask Hask) (IndexedMonad Ixs)) 
            → IxMonad→IndexedMonad (IndexedMonad→IxMonad b) ≡ b
      l→r→l (F , monad) = Σ-eq refl $ ≡-to-≅ 
                        $ indexed-monad-eq (implicit-fun-ext (λ i → natural-transformation-eq (fun-ext (λ α → refl)))) 
                        $ implicit-fun-ext 
                        $ λ i → implicit-fun-ext 
                        $ λ j → implicit-fun-ext 
                        $ λ k → natural-transformation-eq 
                        $ fun-ext $ λ α → begin
                          (nat-η (μ {i} {j} {k}) α ∘ ([ F j k ]₁ id))
                            ≡⟨ cong (λ X → nat-η (μ {i} {j} {k}) α ∘ X) (Functor.id (F j k)) ⟩
                          nat-η (μ {i} {j} {k}) α ∎
        where open IndexedMonad monad
              open Category Hask
      
    abstract
      r→l→r : (a : Σ (Ixs → Ixs → TyCon) (IxMonad Ixs)) 
            → IndexedMonad→IxMonad (IxMonad→IndexedMonad a) ≡ a
      r→l→r (M , monad) = Σ-eq refl $ ≡-to-≅ 
                        $ hask-indexed-monad-eq bind-eq (implicit-fun-ext $ λ α → implicit-fun-ext $ λ i → refl) 
                        $ fun-ext $ λ i → fun-ext $ λ j → hask-functor-eq refl
        where
          _>>=₁_ = IxMonad._>>=_ (proj₂ (IndexedMonad→IxMonad (IxMonad→IndexedMonad (M , monad))))
          _>>=₀_ = IxMonad._>>=_ monad
          
          open IxMonad monad
          open Category Hask
          
          abstract
            bind-eq : (λ {α β} {i j k} → _>>=₁_ {α} {β} {i} {j} {k}) ≡ _>>=₀_
            bind-eq = implicit-fun-ext $ λ α → implicit-fun-ext $ λ β → implicit-fun-ext $ λ i → implicit-fun-ext $ λ j → implicit-fun-ext $ λ k → fun-ext $ λ ma → fun-ext $ λ f → begin
              ((fmap f ma) >>= (λ x → x)) 
                ≡⟨ cong (λ X → X >>= id) (sym (law-monad-fmap f ma)) ⟩
              ((ma >>= (return ∘ f)) >>= id) 
                ≡⟨ sym (law-assoc ma (return ∘ f) id) ⟩
              (ma >>= (λ x → return (f x) >>= id)) 
                ≡⟨ cong (λ X → ma >>= X) (fun-ext (λ x → law-right-id (f x) id)) ⟩
              (ma >>= f) ∎
    
IndexedMonad↔IxMonad : {ℓIxs : Level} {Ixs : Set ℓIxs} 
                     → (Σ (Ixs → Ixs → Functor Hask Hask) (IndexedMonad Ixs))
                     ↔ (Σ (Ixs → Ixs → TyCon) (IxMonad Ixs))
IndexedMonad↔IxMonad = Bijection.sym IxMonad↔IndexedMonad
