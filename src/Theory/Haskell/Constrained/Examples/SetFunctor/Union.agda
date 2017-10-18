
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

module Theory.Haskell.Constrained.Examples.SetFunctor.Union {ℓ : Level} where  

private
  Type = Set ℓ

union : {A : Σ (Set ℓ) (OrdInstance {ℓ} {ℓ} {ℓ})} → LSet A → LSet A → LSet A
union {A , OrdA} (lset [] (lift tt)) sb = sb
union {A , OrdA} (lset (x ∷ xs) sortedXs) sb = insertSet x (union (lset xs (proj₂ sortedXs)) sb)

union-with-empty : {A : Σ (Set ℓ) (OrdInstance {ℓ} {ℓ} {ℓ})} → (as : LSet A) → union as (empty A) ≡ as
union-with-empty {A} (lset [] _) = refl
union-with-empty {A} (lset (x ∷ xs) (sortedX , sortedXs)) = begin
  insertSet x (union (lset xs sortedXs) (empty A)) 
    ≡⟨ cong (λ X → insertSet x X) (union-with-empty (lset xs sortedXs)) ⟩
  insertSet x (lset xs sortedXs) 
    ≡⟨ refl ⟩
  lset (insert x xs) (insert-preserves-IsSortedNoDupList sortedXs) 
    ≡⟨ lset-eq (insert x xs) (x ∷ xs) (insert-preserves-IsSortedNoDupList sortedXs) (sortedX , sortedXs) (insert-adds-in-front sortedX) ⟩
  lset (x ∷ xs) (sortedX , sortedXs) ∎

union-insert-single : {A : Σ (Set ℓ) (OrdInstance {ℓ} {ℓ} {ℓ})}
                    → IsStructuralEquality (OrdInstance.eqInstance (proj₂ A))
                    → (x : proj₁ A) (xs : LSet A) 
                    → union xs (singleton A x) ≡ insertSet x xs
union-insert-single sEq z (lset [] _) = refl
union-insert-single {A} sEq z (lset (x ∷ xs) (sortedX , sortedXs)) with x =A= z
  where _=A=_ = EqInstance.dec-eq (OrdInstance.eqInstance (proj₂ A))
union-insert-single {A} sEq z (lset (x ∷ xs) (sortedX , sortedXs)) | yes x==z = begin
  insertSet x (union (lset xs sortedXs) (singleton A z))
    ≡⟨ cong (insertSet x) (union-insert-single sEq z (lset xs sortedXs)) ⟩
  insertSet x (insertSet z (lset xs sortedXs))
    ≡⟨ lset-eq (insert x (insert z xs)) (insert x xs) 
               (insert-preserves-IsSortedNoDupList (insert-preserves-IsSortedNoDupList sortedXs)) 
               (insert-preserves-IsSortedNoDupList sortedXs) 
               (insert-elim {x = x} {y = z} {zs = xs} x==z) ⟩
  insertSet x (lset xs sortedXs)
    ≡⟨ lset-eq (insert x xs) (insert z (insert x xs)) 
               (insert-preserves-IsSortedNoDupList sortedXs) 
               (insert-preserves-IsSortedNoDupList (insert-preserves-IsSortedNoDupList sortedXs)) 
               (sym (insert-elim' {x = x} {y = z} {zs = xs} sEq x==z)) ⟩
  insertSet z (insertSet x (lset xs sortedXs))
    ≡⟨ cong (insertSet z) (lset-eq (insert x xs) (x ∷ xs) (insert-preserves-IsSortedNoDupList sortedXs) (sortedX , sortedXs) (insert-adds-in-front sortedX)) ⟩
  insertSet z (lset (x ∷ xs) (sortedX , sortedXs)) ∎
union-insert-single {A} sEq z (lset (x ∷ xs) (sortedX , sortedXs)) | no ¬x==z = begin
  insertSet x (union (lset xs sortedXs) (singleton A z))
    ≡⟨ cong (insertSet x) (union-insert-single sEq z (lset xs sortedXs)) ⟩
  insertSet x (insertSet z (lset xs sortedXs))
    ≡⟨ lset-eq (insert x (insert z xs)) (insert z (insert x xs)) 
               (insert-preserves-IsSortedNoDupList (insert-preserves-IsSortedNoDupList sortedXs)) 
               (insert-preserves-IsSortedNoDupList (insert-preserves-IsSortedNoDupList sortedXs)) 
               (insert-commute {xs = xs} ¬x==z) ⟩
  insertSet z (insertSet x (lset xs sortedXs))
    ≡⟨ cong (insertSet z) (lset-eq (insert x xs) (x ∷ xs) (insert-preserves-IsSortedNoDupList sortedXs) (sortedX , sortedXs) (insert-adds-in-front sortedX)) ⟩
  insertSet z (lset (x ∷ xs) (sortedX , sortedXs)) ∎

--  insert-elim : {x y : A} {zs : List A} → x == y → insert x (insert y zs) ≡ insert x zs
--  insert-commute : {x y : A} {xs : List A} → ¬ (x == y) → insert x (insert y xs) ≡ insert y (insert x xs)

union-insert' : {A : Σ (Set ℓ) (OrdInstance {ℓ} {ℓ} {ℓ})} 
              → (x : proj₁ A) (xs ys : LSet A) 
              → insertSet x (union ys xs) ≡ union ys (insertSet x xs)
union-insert' x (lset [] sorted) ys = {!!}
union-insert' x (lset (x₁ ∷ xs) sorted) ys = {!!}

union-commutative : {A : Σ (Set ℓ) (OrdInstance {ℓ} {ℓ} {ℓ})} → (as bs : LSet A) → union as bs ≡ union bs as
union-commutative {A} (lset [] _) bs = sym (union-with-empty bs)
union-commutative {A} (lset (x ∷ xs) (sortedX , sortedXs)) bs = {!!}

unions : {A : Σ (Set ℓ) (OrdInstance {ℓ} {ℓ} {ℓ})} → LSet (LSet A , OrdLSet {ℓ} {A}) → LSet A
unions (lset [] (lift tt)) = lset [] (lift tt)
unions (lset (ys ∷ yss) (sortedYs , sortedYss)) = union ys (unions (lset yss sortedYss))


ap : {A B : Σ (Set ℓ) (OrdInstance {ℓ} {ℓ} {ℓ})} → LSet A × LSet B → LSet ((proj₁ A × proj₁ B) , (OrdInstance-× (proj₂ A) (proj₂ B)))
ap {A} {B} (sa , sb) = unions $ mapSet (λ a → mapSet (λ b → (a , b)) sb) sa

