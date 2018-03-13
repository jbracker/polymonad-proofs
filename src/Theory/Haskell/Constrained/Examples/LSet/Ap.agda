
open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Level

open import Data.Unit hiding ( _≤_ ; _≟_ ; total )
open import Data.Empty
open import Data.Product
open import Data.List

open import Relation.Nullary
open import Relation.Binary using ( IsDecEquivalence ; IsEquivalence ; IsDecTotalOrder ; IsPreorder ; IsPartialOrder )
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality using ( refl ; ≡-to-≅ )
open ≡-Reasoning

open import Equality
open import Extensionality
open import ProofIrrelevance

open import Theory.Haskell.Constrained.Examples.LSet.Base
open import Theory.Haskell.Constrained.Examples.LSet.Instances
open import Theory.Haskell.Constrained.Examples.LSet.Product
open import Theory.Haskell.Constrained.Examples.LSet.Insert
open import Theory.Haskell.Constrained.Examples.LSet.Map
open import Theory.Haskell.Constrained.Examples.LSet.Union
open import Theory.Haskell.Constrained.Examples.LSet.KleisliExtension

module Theory.Haskell.Constrained.Examples.LSet.Ap {ℓ : Level} where  

ap : {A B : Σ (Set ℓ) (OrdInstance {ℓ} {ℓ} {ℓ})} → LSet A × LSet B → LSet ((proj₁ A × proj₁ B) , (OrdInstance-× (proj₂ A) (proj₂ B)))
ap {A} {B} (sa , sb) = kext (λ a → kext (λ b → singleton ((proj₁ A × proj₁ B) , (OrdInstance-× (proj₂ A) (proj₂ B))) (a , b)) sb) sa
