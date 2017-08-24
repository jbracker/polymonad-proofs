
open import Level
open import Function hiding ( id ; _∘_ )

open import Data.Product

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning hiding ( _≅⟨_⟩_ )
open import Relation.Binary.HeterogeneousEquality renaming ( sym to hsym ; trans to htrans ; subst to hsubst ; subst₂ to hsubst₂ ; cong to hcong ; cong₂ to hcong₂ )
open ≅-Reasoning renaming ( begin_ to hbegin_ ; _∎ to _∎h ) hiding ( _≡⟨⟩_ ; _≡⟨_⟩_ )

open import Theory.Triple renaming ( _,_,_ to _,'_,'_ )
open import Theory.Category.Definition
open import Theory.Functor.Definition
open import Theory.Natural.Isomorphism
open import Theory.TwoCategory.Definition
open import Theory.TwoCategory.Bicategory



module Theory.TwoCategory.Examples.ToBicategory where

open Category
open Functor hiding ( id )
open NaturalIsomorphism renaming ( η to nat-η )

StrictTwoCategory→Bicategory : {ℓ₀ ℓ₁ ℓ₂ : Level} → StrictTwoCategory {ℓ₀} {ℓ₁} {ℓ₂} → Bicategory {ℓ₀} {ℓ₁} {ℓ₂}
StrictTwoCategory→Bicategory {ℓ₀} {ℓ₁} {ℓ₂} TC = record
  { Cell₀ = Cell₀
  ; HomCat = HomCat
  ; id₁ = λ a → id₁ {a}
  ; comp = comp
  ; left-unitor = left-unitor-iso
  ; right-unitor = right-unitor-iso
  ; associator = associator-iso
  ; triangle-id = triangle-id
  ; pentagon-id = pentagon-id
  } where open StrictTwoCategory TC
