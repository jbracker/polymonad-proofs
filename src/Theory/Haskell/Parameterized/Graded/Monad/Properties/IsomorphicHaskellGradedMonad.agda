
open import Level
open import Function hiding ( id ; _∘_ )

open import Data.Product

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( sym to hsym ; trans to htrans ; cong to hcong ; cong₂ to hcong₂ )
-- open ≡-Reasoning hiding ( _≅⟨_⟩_ )
open ≅-Reasoning hiding ( _≡⟨⟩_ ; _≡⟨_⟩_ ) renaming ( begin_ to hbegin_ ; _∎ to _∎h )

open import Equality
open import Extensionality
open import Bijection hiding ( refl ; sym ; trans )
open import Haskell hiding ( Hask )
open import Haskell.Functor renaming ( Functor to HaskellFunctor ; functor-eq to hask-functor-eq ) hiding ( functor )
open import Haskell.Parameterized.Graded.Monad renaming ( GradedMonad to HaskellGradedMonad ; graded-monad-eq to hask-graded-monad-eq )
open import Theory.Monoid
open import Theory.Category.Definition
open import Theory.Category.Examples.SetCat
open import Theory.Functor.Definition
open import Theory.Natural.Transformation
open import Theory.Haskell.Parameterized.Graded.Monad
open import Theory.Haskell.Parameterized.Graded.Monad.Equality
open import Theory.Haskell.Parameterized.Graded.Monad.Properties.FromHaskellGradedMonad
open import Theory.Haskell.Parameterized.Graded.Monad.Properties.ToHaskellGradedMonad

module Theory.Haskell.Parameterized.Graded.Monad.Properties.IsomorphicHaskellGradedMonad where

private
  Hask = setCategory {zero}

HaskellGradedMonad↔GradedMonad : {ℓMon : Level} {Mon : Set ℓMon} {monoid : Monoid Mon} 
                     → (Σ (Mon → TyCon) (HaskellGradedMonad monoid))
                     ↔ (Σ (Mon → Functor Hask Hask) (GradedMonad monoid))
HaskellGradedMonad↔GradedMonad {ℓMon} {Mon} {monoid} = bijection HaskellGradedMonad→GradedMonad GradedMonad→HaskellGradedMonad l→r→l r→l→r
  where
    open Monoid monoid
    open NaturalTransformation renaming ( η to nat-η )
    
    abstract
      l→r→l : (b : Σ (Mon → Functor Hask Hask) (GradedMonad monoid)) 
            → HaskellGradedMonad→GradedMonad (GradedMonad→HaskellGradedMonad b) ≡ b
      l→r→l (F , monad) = Σ-eq refl $ ≡-to-≅ 
                        $ graded-monad-eq (natural-transformation-eq (fun-ext (λ α → refl)))
                        $ implicit-fun-ext 
                        $ λ i → implicit-fun-ext 
                        $ λ j → natural-transformation-eq 
                        $ fun-ext $ λ α → cong (λ X → nat-η (μ {i} {j}) α ∘ X) (Functor.id (F i))
        where open GradedMonad monad
              open Category Hask
    
    abstract
      r→l→r : (a : Σ (Mon → TyCon) (HaskellGradedMonad monoid)) 
            → GradedMonad→HaskellGradedMonad (HaskellGradedMonad→GradedMonad a) ≡ a
      r→l→r (M , monad) = Σ-eq refl $ ≡-to-≅ 
                        $ hask-graded-monad-eq bind-eq (implicit-fun-ext $ λ α → refl) 
                        $ fun-ext $ λ i → hask-functor-eq refl
        where
          _>>=₁_ = HaskellGradedMonad._>>=_ (proj₂ (GradedMonad→HaskellGradedMonad (HaskellGradedMonad→GradedMonad (M , monad))))
          _>>=₀_ = HaskellGradedMonad._>>=_ monad
          
          open HaskellGradedMonad monad
          open Category Hask hiding ( left-id ; right-id ; assoc )
          
          abstract
            bind-eq : (λ {α β} {i j} → _>>=₁_ {α} {β} {i} {j}) ≡ _>>=₀_
            bind-eq = implicit-fun-ext $ λ α → implicit-fun-ext $ λ β → implicit-fun-ext $ λ i → implicit-fun-ext $ λ j → fun-ext $ λ ma → fun-ext $ λ f → ≅-to-≡ $ hbegin
              ((fmap f ma) >>= id) 
                ≅⟨ hcong₂ (λ X Y → M (X ∙ j) β ∋ Y >>= id) (≡-to-≅ (sym right-id)) (hsym (law-monad-fmap f ma)) ⟩
              ((ma >>= (return ∘ f)) >>= id) 
                ≅⟨ hcong₂ (λ X Y → M X β ∋ Y) (≡-to-≅ (sym assoc)) (hsym (law-assoc ma (return ∘ f) id)) ⟩
              (ma >>= (λ x → return (f x) >>= id)) 
                ≅⟨ hcong₂ (λ X Y → M (i ∙ X) β ∋ ma >>= Y) 
                          (≡-to-≅ left-id) 
                          (het-fun-ext (hcong (λ X → (λ _ → M X β)) (≡-to-≅ left-id)) 
                                       (λ x → hcong₂ (λ X Y → M X β ∋ Y) (≡-to-≅ left-id) (law-left-id (f x) id))) ⟩
              (ma >>= f) ∎h
    
GradedMonad↔HaskellGradedMonad : {ℓMon : Level} {Mon : Set ℓMon} {monoid : Monoid Mon}
                               → (Σ (Mon → Functor Hask Hask) (GradedMonad monoid))
                               ↔ (Σ (Mon → TyCon) (HaskellGradedMonad monoid))
GradedMonad↔HaskellGradedMonad = Bijection.sym HaskellGradedMonad↔GradedMonad
