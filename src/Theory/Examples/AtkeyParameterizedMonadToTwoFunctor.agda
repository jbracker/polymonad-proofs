
-- Stdlib
open import Level renaming ( suc to lsuc ; zero to lzero )
open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Data.Unit
open import Data.Product renaming ( _,_ to _,'_ )
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality 
  renaming ( sym to hsym ; trans to htrans ; cong to hcong ; cong₂ to hcong₂ ; subst to hsubst ; subst₂ to hsubst₂ )
open ≡-Reasoning hiding ( _≅⟨_⟩_ )
-- open ≅-Reasoning hiding ( _≡⟨_⟩_ ) renaming ( begin_ to hbegin_ ; _∎ to _∎h)

-- Local
open import Extensionality
open import Utilities
open import Haskell
open import Theory.Triple
open import Theory.Category
open import Theory.Functor
open import Theory.Natural.Transformation
open import Theory.Monad.Atkey
open import Theory.TwoCategory
open import Theory.TwoCategory.Examples
open import Theory.TwoFunctor

open Category
open NaturalTransformation
open StrictTwoCategory

module Theory.Examples.AtkeyParameterizedMonadToTwoFunctor where

functor-convert : {ℓ₀ ℓ₁ : Level}
                → {C : Category {ℓ₀} {ℓ₁}} {D : Category {ℓ₀} {ℓ₁}} {E : Category {ℓ₀} {ℓ₁}}
                → D ≡ C → E ≡ C
                → Functor D E → Functor C C
functor-convert refl refl F = F

AtkeyFunctor→LaxTwoFunctor 
  : {ℓC₀ ℓC₁ ℓS₀ ℓS₁ : Level} 
  → {C : Category {ℓC₀} {ℓC₁}}
  → {S : Category {ℓS₀} {ℓS₁}}
  → {T : Functor (S op ×C S ×C C) C}
  → (F : AtkeyParameterizedMonad C S T) 
  → LaxTwoFunctor (Category→StrictTwoCategory S) (functorTwoCategory {ℓC₀} {ℓC₁})
AtkeyFunctor→LaxTwoFunctor {C = C} {S} {T} F = record
  { P₀ = λ _ → C
  ; P₁ = P
  ; η = λ {x} → {!!}
  ; μ = {!!}
  ; laxFunId₁ = {!!}
  ; laxFunId₂ = {!!}
  ; laxFunAssoc = {!!}
  } where
    
    _∘C_ = Category._∘_ C
    
    ApplyT : {x y : Obj S} → Hom S x y → Functor C C
    ApplyT {x} {y} f = functor 
      (λ A → Functor.F₀ T (x , y , A)) 
      (λ f → Functor.F₁ T (id S {x} , id S {y} , f))
      (λ {a} → Functor.id T)
      (λ {a} {b} {c} {f} {g} → trans (cong₂ (λ X Y → Functor.F₁ T (X , Y , (g ∘C f))) (sym (left-id S)) (sym (left-id S))) (Functor.compose T))
  
    stateHomIndep : {x y : Obj S} → (fS : Hom S x y) (gS : Hom S x y)
                  → NaturalTransformation (ApplyT fS) (ApplyT gS)
    stateHomIndep fS gS = naturalTransformation 
      (λ x → id C {[ ApplyT fS ]₀ x}) 
      (λ {a} {b} {f} → trans (left-id C {f = [ ApplyT fS ]₁ f}) (sym (right-id C {f = [ ApplyT fS ]₁ f})))
    
    P : {x y : Cell₀ (Category→StrictTwoCategory S)} 
      → Functor (HomCat (Category→StrictTwoCategory S) x y) (HomCat functorTwoCategory C C)
    P = λ {x} {y} → functor 
       (λ fS → ApplyT fS) 
       (λ {fS} {gS} _ → stateHomIndep fS gS)
       (λ {fS} → refl)
       (λ {fS} {gS} {hS} {_} {_} → natural-transformation-eq (fun-ext (λ x → sym (right-id C))))
