
open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Level

open import Data.Unit hiding ( _≤_ ; _≟_ ; total )
open import Data.Empty
open import Data.List
open import Data.List.All hiding ( map )
open import Data.Product hiding ( map )
open import Data.Sum hiding ( map )

open import Relation.Nullary
open import Relation.Binary using ( IsDecEquivalence ; IsEquivalence ; IsDecTotalOrder ; IsPreorder ; IsPartialOrder )
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality using ( refl ; ≡-to-≅ )
open ≡-Reasoning

open import Equality
open import Extensionality
open import ProofIrrelevance

open import Theory.Haskell.Constrained.Examples.SetFunctor.Base
open import Theory.Haskell.Constrained.Examples.SetFunctor.Instances
open import Theory.Haskell.Constrained.Examples.SetFunctor.Product
open import Theory.Haskell.Constrained.Examples.SetFunctor.Insert
open import Theory.Haskell.Constrained.Examples.SetFunctor.Map
open import Theory.Haskell.Constrained.Examples.SetFunctor.Union

module Theory.Haskell.Constrained.Examples.SetFunctor.KleisliExtension {A B : Set ℓ} {OrdA : OrdInstance {ℓ} {ℓ} {ℓ} A} {OrdB : OrdInstance {ℓ} {ℓ} {ℓ} B} where
    
    open OrdInstance OrdA renaming ( eqInstance to EqA )
    open OrdInstance OrdB renaming ( eqInstance to EqB )
    
    kext : (A → LSet (B , OrdB)) → LSet (A , OrdA) → LSet (B , OrdB)
    kext f (lset [] _) = lset [] (lift tt)
    kext f (lset (x ∷ xs) (sortedX , sortedXs)) = union (f x) (kext f (lset xs sortedXs))
    
    kext-union-shift : (f : A → LSet (B , OrdB)) → (x : A) → (xs : List A) → (sorted : IsSortedNoDupList OrdA (x ∷ xs)) → (ys : LSet (A , OrdA))
                     → kext f (union (lset (x ∷ xs) sorted) ys) ≡ union (f x) (kext f (union (lset xs (proj₂ sorted)) ys))
    kext-union-shift f x xs sorted ys = {!!}
    
    kext-union-dist : (f : A → LSet (B , OrdB)) 
                    → (xs ys : LSet (A , OrdA))
                    → kext f (union xs ys) ≡ union (kext f xs) (kext f ys)
    kext-union-dist f (lset [] _) ys = refl
    kext-union-dist f (lset (x ∷ xs) (sortedX , sortedXs)) ys = begin
      kext f (insertSet x (union (lset xs sortedXs) ys)) 
        ≡⟨ cong (kext f) (union-insert' x xs ys (sortedX , sortedXs)) ⟩
      kext f (union (lset (x ∷ xs) (sortedX , sortedXs)) ys)
        ≡⟨ kext-union-shift f x xs (sortedX , sortedXs) ys ⟩
      union (f x) (kext f (union (lset xs sortedXs) ys))
        ≡⟨ cong (union (f x)) (kext-union-dist f (lset xs sortedXs) ys) ⟩
      union (f x) (union (kext f (lset xs sortedXs)) (kext f ys))
        ≡⟨ {!!} ⟩
      union (union (f x) (kext f (lset xs sortedXs))) (kext f ys) ∎

{-
    kext-union-dist f (lset [] sorted) _ = refl
    kext-union-dist f (lset (x ∷ xs) sortedXs) (lset [] sortedYs) = begin
      kext f (insertSet x (union (lset xs (proj₂ sortedXs)) (lset [] sortedYs)))
        ≡⟨ cong (kext f ∘F insertSet x) (union-with-empty (lset xs (proj₂ sortedXs))) ⟩
      kext f (insertSet x (lset xs (proj₂ sortedXs)))
        ≡⟨ cong (kext f) (insertSet-adds-in-front x xs sortedXs) ⟩
      kext f (lset (x ∷ xs) sortedXs)
        ≡⟨ refl ⟩
      union (f x) (kext f (lset xs (proj₂ sortedXs)))
        ≡⟨ sym (union-with-empty (union (f x) (kext f (lset xs (proj₂ sortedXs))))) ⟩
      union (union (f x) (kext f (lset xs (proj₂ sortedXs)))) (lset [] (lift tt)) ∎
    kext-union-dist f (lset (x ∷ xs) sortedXs) (lset (y ∷ ys) sortedYs) = begin
      kext f (insertSet x (union (lset xs (proj₂ sortedXs)) (lset (y ∷ ys) sortedYs)))
        ≡⟨ cong (kext f) (union-insert' x xs (lset (y ∷ ys) sortedYs) sortedXs) ⟩
      kext f (union (lset (x ∷ xs) sortedXs) (lset (y ∷ ys) sortedYs))
        ≡⟨ {!!} ⟩
      union (union (f x) (kext f (lset xs (proj₂ sortedXs)))) (union (f y) (kext f (lset ys (proj₂ sortedYs)))) ∎
-} 
