
-- Stdlib
open import Level renaming ( suc to lsuc ; zero to lzero )
open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Data.Unit
open import Data.Product renaming ( _,_ to _,'_ )
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality 
  renaming ( refl to hrefl; sym to hsym ; trans to htrans ; cong to hcong ; cong₂ to hcong₂ ; subst to hsubst ; subst₂ to hsubst₂ ; proof-irrelevance to hproof-irrelevance )
open ≡-Reasoning hiding ( _≅⟨_⟩_ )
-- open ≅-Reasoning hiding ( _≡⟨_⟩_ ) renaming ( begin_ to hbegin_ ; _∎ to _∎h)

-- Local
open import Extensionality
open import Utilities
open import Haskell
open import Theory.Triple
open import Theory.Category
open import Theory.Category.Examples
open import Theory.Functor
open import Theory.Functor.Composition
open import Theory.Natural.Transformation
open import Theory.Natural.Transformation.Examples
open import Theory.Monad.Relative
open import Theory.TwoCategory
open import Theory.TwoCategory.Examples
open import Theory.TwoFunctor

open Category
open NaturalTransformation
open StrictTwoCategory

module Theory.TwoFunctor.Properties.FromRelativeMonad where

-- TODO: This does not seem to work...
RelativeMonad→LaxTwoFunctor 
  : {ℓ₀ ℓ₁ : Level} 
  → {C : Category {ℓ₀} {ℓ₁}}
  → {D : Category {ℓ₀} {ℓ₁}}
  → {T : Obj C → Obj D}
  → {J : Functor C D}
  → RelativeMonad T J 
  → LaxTwoFunctor (Category→StrictTwoCategory binaryCategory) (functorTwoCategory {ℓ₀} {ℓ₁})
RelativeMonad→LaxTwoFunctor {ℓ₀} {ℓ₁} {C} {D} {T} {J} M = record
  { P₀ = P₀
  ; P₁ = λ {x} {y} → P₁ {x} {y}
  ; η = {!!}
  ; μ = {!!}
  ; laxFunId₁ = {!!}
  ; laxFunId₂ = {!!}
  ; laxFunAssoc = {!!}
  } where 
    P₀ : Bool → Category {ℓ₀} {ℓ₁}
    P₀ true = D
    P₀ false = C
    
    P₁ : {x y : Bool} → Functor (HomCat (Category→StrictTwoCategory binaryCategory) x y) (HomCat functorTwoCategory (P₀ x) (P₀ y))
    P₁ {true}  {true}  = functor (λ _ → Id[ D ]) (λ _ → Id⟨ Id[ D ] ⟩) refl (natural-transformation-eq (fun-ext (λ x → sym $ Category.right-id D)))
    P₁ {true}  {false} = functor (λ ()) (λ x → Id⟨ {!!} ⟩) {!!} {!!}
    P₁ {false} {true}  = functor (λ _ → RelativeMonad.FunctorT M) (λ _ → {!!}) {!!} {!!}
    P₁ {false} {false} = functor (λ _ → Id[ C ]) (λ _ → Id⟨ Id[ C ] ⟩) refl (natural-transformation-eq (fun-ext (λ x → sym $ Category.right-id C)))
