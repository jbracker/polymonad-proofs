
module Theory.TwoFunctor.Examples.IsomorphicIndexedMonad where

-- Stdlib
open import Level
open import Function renaming ( _∘_ to _∘F_ )

open import Data.Product

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( cong to hcong ; refl to hrefl ; sym to hsym )
open ≡-Reasoning

-- Local
open import Bijection hiding ( refl ; sym )
open import Extensionality
open import Equality
open import Haskell
open import Haskell.Parameterized.IndexedMonad
open import Haskell.Functor renaming ( Functor to HaskellFunctor )
open import Theory.Functor
open import Theory.Category.Examples
open import Theory.TwoCategory
open import Theory.TwoCategory.Examples
open import Theory.TwoFunctor
open import Theory.TwoFunctor.Examples.ConstZeroCell
open import Theory.TwoFunctor.Examples.FromIndexedMonad
open import Theory.TwoFunctor.Examples.ToIndexedMonad


IndexedMonad↔LaxTwoFunctor : {ℓ : Level}
                           → (Σ (Set ℓ) (λ Ixs → Σ (Ixs → Ixs → TyCon) (IxMonad Ixs)))
                           ↔ (Σ (Set ℓ) (λ Ixs → ConstLaxTwoFunctor (Category→StrictTwoCategory (codiscreteCategory Ixs)) (Cat {suc zero} {zero}) (Hask {zero})))
IndexedMonad↔LaxTwoFunctor {ℓ} = bijection l→r r→l l→r→l r→l→r
  where
    Cat' = Cat {suc zero} {zero}
    Hask' = Hask {zero}
    
    l→r : Σ (Set ℓ) (λ Ixs → Σ (Ixs → Ixs → TyCon) (IxMonad Ixs))
        → Σ (Set ℓ) (λ Ixs → ConstLaxTwoFunctor (Category→StrictTwoCategory (codiscreteCategory Ixs)) Cat' Hask')
    l→r (Ixs , M , monad) = Ixs , IndexedMonad→LaxTwoFunctor Ixs M monad

    r→l : Σ (Set ℓ) (λ Ixs → ConstLaxTwoFunctor (Category→StrictTwoCategory (codiscreteCategory Ixs)) Cat' Hask')
        → Σ (Set ℓ) (λ Ixs → Σ (Ixs → Ixs → TyCon) (IxMonad Ixs))
    r→l (Ixs , F) = Ixs , LaxTwoFunctor→IxMonadTyCon Ixs F , LaxTwoFunctor→IndexedMonad Ixs F

    l→r→l : (x : Σ (Set ℓ) (λ Ixs → ConstLaxTwoFunctor (Category→StrictTwoCategory (codiscreteCategory Ixs)) Cat' Hask'))
          → l→r (r→l x) ≡ x
    l→r→l (Ixs , F) = Σ-eq refl {!lax-two-functor-eq!}

    r→l→r : (x : Σ (Set ℓ) (λ Ixs → Σ (Ixs → Ixs → TyCon) (IxMonad Ixs)))
          → r→l (l→r x) ≡ x
    r→l→r (Ixs , M , monad) = Σ-eq refl $ het-Σ-eq refl $ ≡-to-≅ $ indexed-monad-eq bind-eq refl refl
      where
        open IxMonad monad
        
        bind-eq : (λ {α β : Type} {i j k : Ixs} → IxMonad._>>=_ (proj₂ (proj₂ (r→l (l→r (Ixs , M , monad))))) {α} {β} {i} {j} {k})
                ≡ (λ {α β : Type} {i j k : Ixs} → IxMonad._>>=_ monad {α} {β} {i} {j} {k})
        bind-eq = implicit-fun-ext
                $ λ α → implicit-fun-ext $ λ β → implicit-fun-ext
                $ λ i → implicit-fun-ext $ λ j → implicit-fun-ext $ λ k → fun-ext
                $ λ ma → fun-ext $ λ f → begin
                  IxMonad._>>=_ (proj₂ (proj₂ (r→l (l→r (Ixs , M , monad))))) ma f
                    ≡⟨⟩
                  fmap f ma >>= (λ x → x)
                    ≡⟨ cong (λ X → X >>= (λ x → x)) (sym (law-monad-fmap f ma)) ⟩
                  (ma >>= (return ∘F f)) >>= (λ x → x)
                    ≡⟨ sym (law-assoc ma (return ∘F f) (λ x → x)) ⟩
                  ma >>= (λ a → return (f a) >>= (λ x → x))
                    ≡⟨ cong (λ X → _>>=_ ma X) (fun-ext (λ a → law-right-id (f a) (λ x → x))) ⟩
                  ma >>= f ∎

LaxTwoFunctor↔IndexedMonad : {ℓ : Level}
                           → (Σ (Set ℓ) (λ Ixs → ConstLaxTwoFunctor (Category→StrictTwoCategory (codiscreteCategory Ixs)) (Cat {suc zero} {zero}) (Hask {zero})))
                           ↔ (Σ (Set ℓ) (λ Ixs → Σ (Ixs → Ixs → TyCon) (IxMonad Ixs)))
LaxTwoFunctor↔IndexedMonad {ℓ} = Bijection.sym $ IndexedMonad↔LaxTwoFunctor {ℓ}
