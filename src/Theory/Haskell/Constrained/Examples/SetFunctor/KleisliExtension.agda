
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

module Theory.Haskell.Constrained.Examples.SetFunctor.KleisliExtension {ℓ : Level} {A B : Set ℓ} {OrdA : OrdInstance {ℓ} {ℓ} {ℓ} A} {OrdB : OrdInstance {ℓ} {ℓ} {ℓ} B} where
    
open OrdInstance OrdA renaming ( eqInstance to EqA ; dec-eq to dec-eqA ; dec-ord to dec-ordA ; refl-eq to refl-eqA )
open OrdInstance OrdB renaming ( eqInstance to EqB ; dec-eq to dec-eqB ; dec-ord to dec-ordB ; refl-eq to refl-eqB )

open OrdInstance (OrdLSet {A = B , OrdB}) renaming ( eqInstance to EqLSetB ; dec-eq to dec-eqLSetB ; refl-eq to refl-eqLSetB )

kext : (A → LSet (B , OrdB)) → LSet (A , OrdA) → LSet (B , OrdB)
kext f (lset [] _) = lset [] (lift tt)
kext f (lset (x ∷ xs) (sortedX , sortedXs)) = union (f x) (kext f (lset xs sortedXs))

abstract
  kext-insert-swap : (f : A → LSet (B , OrdB)) → (x : A) → (xs : LSet (A , OrdA))
                   → IsStructuralEquality EqA → IsStructuralEquality EqB
                   → kext f (insertSet x xs) ≡ union (f x) (kext f xs)
  kext-insert-swap f x (lset [] sorted) sEqA sEqB = refl
  kext-insert-swap f z (lset (x ∷ xs) (sortedX , sortedXs)) sEqA sEqB with dec-eqA z x
  kext-insert-swap f z (lset (x ∷ xs) (sortedX , sortedXs)) sEqA sEqB | yes z=x with sEqA z x z=x
  kext-insert-swap f z (lset (.z ∷ xs) (sortedX , sortedXs)) sEqA sEqB | yes z=x | refl = begin
    union (f z) (kext f (lset xs sortedXs))
      ≡⟨ sym (union-elim (f z) (f z) (kext f (lset xs sortedXs)) (refl-eqLSetB {f z}) sEqB) ⟩
    union (f z) (union (f z) (kext f (lset xs sortedXs))) ∎
  kext-insert-swap f z (lset (x ∷ xs) (sortedX , sortedXs)) sEqA sEqB | no ¬z=x with dec-ordA z x
  kext-insert-swap f z (lset (x ∷ xs) (sortedX , sortedXs)) sEqA sEqB | no ¬z=x | yes z≤x = refl
  kext-insert-swap f z (lset (x ∷ xs) (sortedX , sortedXs)) sEqA sEqB | no ¬z=x | no ¬z≤x = begin
    union (f x) (kext f (insertSet z (lset xs sortedXs)) )
      ≡⟨ cong (union (f x)) (kext-insert-swap f z (lset xs sortedXs) sEqA sEqB) ⟩
    union (f x) (union (f z) (kext f (lset xs sortedXs)))
      ≡⟨ union-assoc (f x) (f z) (kext f (lset xs sortedXs)) sEqB ⟩
    union (union (f x) (f z)) (kext f (lset xs sortedXs))
      ≡⟨ cong (λ X → union X (kext f (lset xs sortedXs))) (union-commutative (f x) (f z) sEqB) ⟩
    union (union (f z) (f x)) (kext f (lset xs sortedXs))
      ≡⟨ sym (union-assoc (f z) (f x) (kext f (lset xs sortedXs)) sEqB) ⟩
    union (f z) (union (f x) (kext f (lset xs sortedXs))) ∎

abstract
  kext-union-dist : (f : A → LSet (B , OrdB)) 
                  → (xs ys : LSet (A , OrdA))
                  → IsStructuralEquality EqA → IsStructuralEquality EqB
                  → kext f (union xs ys) ≡ union (kext f xs) (kext f ys)
  kext-union-dist f (lset [] _) ys sEqA sEqB = refl
  kext-union-dist f (lset (x ∷ xs) (sortedX , sortedXs)) ys sEqA sEqB = begin
    kext f (insertSet x (union (lset xs sortedXs) ys))
      ≡⟨ kext-insert-swap f x (union (lset xs sortedXs) ys) sEqA sEqB ⟩
    union (f x) (kext f (union (lset xs sortedXs) ys))
      ≡⟨ cong (union (f x)) (kext-union-dist f (lset xs sortedXs) ys sEqA sEqB) ⟩
    union (f x) (union (kext f (lset xs sortedXs)) (kext f ys))
      ≡⟨ union-assoc (f x) (kext f (lset xs sortedXs)) (kext f ys) sEqB ⟩
    union (union (f x) (kext f (lset xs sortedXs))) (kext f ys) ∎
