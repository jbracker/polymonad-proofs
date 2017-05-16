
open import Level
open import Function

open import Data.Unit
open import Data.Product

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality using ( ≅-to-≡ ; ≡-to-≅ )

open import Equality
open import Bijection hiding ( refl ; sym )
open import Theory.Category
open import Theory.Functor hiding ( functor )
open import Theory.Monad hiding ( monad )
open import Theory.TwoCategory
open import Theory.TwoCategory.Examples
open import Theory.TwoFunctor
open import Theory.TwoFunctor.Properties.ToMonad
open import Theory.TwoFunctor.Properties.FromMonad
 
module Theory.TwoFunctor.Properties.IsomorphicMonad where


Monad↔LaxTwoFunctor : {ℓC₀ ℓC₁ : Level} → Σ (Category {ℓC₀} {ℓC₁}) (λ C → Σ (Functor C C) Monad) ↔ LaxTwoFunctor ⊤-TwoCat (Cat {ℓC₀} {ℓC₁})
Monad↔LaxTwoFunctor {ℓC₀} {ℓC₁} = bijection l→r r→l r→l→r l→r→l
  where
    Category' = Category {ℓC₀} {ℓC₁}
    Cat' = Cat {ℓC₀} {ℓC₁}
    
    l→r : Σ Category' (λ C → Σ (Functor C C) Monad) → LaxTwoFunctor ⊤-TwoCat Cat'
    l→r (C , F , monad) = Monad→LaxTwoFunctor {C = C} {M = F} monad
    
    r→l : LaxTwoFunctor ⊤-TwoCat Cat' → Σ Category' (λ C → Σ (Functor C C) Monad)
    r→l F = LaxTwoFunctor.P₀ F tt , Functor.F₀ (LaxTwoFunctor.P₁ F) tt , LaxTwoFunctor→Monad F
    
    r→l→r : (F : LaxTwoFunctor ⊤-TwoCat Cat) → l→r (r→l F) ≡ F
    r→l→r F = {!!}
    
    l→r→l : (M : Σ Category (λ C → Σ (Functor C C) Monad)) → r→l (l→r M) ≡ M
    l→r→l (C , F , monad) = Σ-eq refl (het-Σ-eq refl (≡-to-≅ (monad-eq refl refl)))




LaxTwoFunctor↔Monad : {ℓC₀ ℓC₁ : Level} → LaxTwoFunctor ⊤-TwoCat (Cat {ℓC₀} {ℓC₁}) ↔ Σ (Category {ℓC₀} {ℓC₁}) (λ C → Σ (Functor C C) Monad)
LaxTwoFunctor↔Monad {ℓC₀} {ℓC₁} = Bijection.sym $ Monad↔LaxTwoFunctor {ℓC₀} {ℓC₁}
