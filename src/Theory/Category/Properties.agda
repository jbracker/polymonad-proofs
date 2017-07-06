
open import Level

open import Data.Product
open import Data.Sum

open import Relation.Binary.HeterogeneousEquality renaming ( cong to hcong ; proof-irrelevance to het-proof-irrelevance )
open import Relation.Binary.PropositionalEquality

--open import Utilities
open import Extensionality
open import Equality
open import Bijection renaming ( refl to brefl )
open import Theory.Category.Definition
open import Theory.Category.Isomorphism
open import Theory.Category.Examples.SetCat

module Theory.Category.Properties where 

SetIsomorphism↔Bijection : {ℓ : Level} {A B : Set ℓ} → (Σ (A → B) (Isomorphism (setCategory {ℓ}))) ↔ (Bijection A B)
SetIsomorphism↔Bijection {ℓ} {A} {B} = bijection Iso→Bij Bij→Iso right-id left-id
  where
    Iso→Bij : Σ (A → B) (Isomorphism setCategory) → Bijection A B
    Iso→Bij (f , iso) = bijection f (Isomorphism.inv iso) (λ x → cong (λ g → g x) (Isomorphism.left-id iso)) (λ x → cong (λ g → g x) (Isomorphism.right-id iso))
    
    Bij→Iso : (bij : Bijection A B) → Σ (A → B) (Isomorphism setCategory)
    Bij→Iso bij = Bijection.f bij ,  isomorphism (Bijection.inv bij) (fun-ext (Bijection.right-id bij)) (fun-ext (Bijection.left-id bij))

    right-id : (b : Bijection A B) → Iso→Bij (Bij→Iso b) ≡ b
    right-id bij = bijection-eq (inj₁ refl)
    
    left-id : (a : Σ (A → B) (Isomorphism setCategory)) → Bij→Iso (Iso→Bij a) ≡ a
    left-id (f , iso) = Σ-eq refl (≡-to-≅ (isomorphism-eq refl))
