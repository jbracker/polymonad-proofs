
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

module Theory.Haskell.Constrained.Examples.SetFunctor.Union {ℓ : Level} {A : Set ℓ} {OrdA : OrdInstance {ℓ} {ℓ} {ℓ} A} where  

private
  Type = Set ℓ

open OrdInstance OrdA renaming ( eqInstance to EqA )

union : LSet (A , OrdA) → LSet (A , OrdA) → LSet (A , OrdA)
union (lset [] (lift tt)) sb = sb
union (lset (x ∷ xs) sortedXs) sb = insertSet x (union (lset xs (proj₂ sortedXs)) sb)

union-with-empty : (as : LSet (A , OrdA)) → union as (empty (A , OrdA)) ≡ as
union-with-empty (lset [] _) = refl
union-with-empty (lset (x ∷ xs) (sortedX , sortedXs)) = begin
  insertSet x (union (lset xs sortedXs) (empty (A , OrdA))) 
    ≡⟨ cong (λ X → insertSet x X) (union-with-empty (lset xs sortedXs)) ⟩
  insertSet x (lset xs sortedXs)
    ≡⟨ insertSet-adds-in-front x xs (sortedX , sortedXs) ⟩
  lset (x ∷ xs) (sortedX , sortedXs) ∎
    
union-insert-single : IsStructuralEquality EqA
                    → (x : A) (xs : LSet (A , OrdA)) 
                    → union xs (singleton (A , OrdA) x) ≡ insertSet x xs
union-insert-single sEq z (lset [] _) = refl
union-insert-single sEq z (lset (x ∷ xs) (sortedX , sortedXs)) with x =A= z
  where _=A=_ = EqInstance.dec-eq EqA
union-insert-single sEq z (lset (x ∷ xs) (sortedX , sortedXs)) | yes x==z = begin
  insertSet x (union (lset xs sortedXs) (singleton (A , OrdA) z))
    ≡⟨ cong (insertSet x) (union-insert-single sEq z (lset xs sortedXs)) ⟩
  insertSet x (insertSet z (lset xs sortedXs))
    ≡⟨ insertSet-elim x z (lset xs sortedXs) x==z ⟩
  insertSet x (lset xs sortedXs)
    ≡⟨ sym (insertSet-elim' x z (lset xs sortedXs) sEq x==z) ⟩
  insertSet z (insertSet x (lset xs sortedXs))
    ≡⟨ cong (insertSet z) (lset-eq (insert x xs) (x ∷ xs) (insert-preserves-IsSortedNoDupList sortedXs) (sortedX , sortedXs) (insert-adds-in-front sortedX)) ⟩
  insertSet z (lset (x ∷ xs) (sortedX , sortedXs)) ∎
union-insert-single sEq z (lset (x ∷ xs) (sortedX , sortedXs)) | no ¬x==z = begin
  insertSet x (union (lset xs sortedXs) (singleton (A , OrdA) z))
    ≡⟨ cong (insertSet x) (union-insert-single sEq z (lset xs sortedXs)) ⟩
  insertSet x (insertSet z (lset xs sortedXs))
    ≡⟨ insertSet-commute' x z (lset xs sortedXs) ¬x==z ⟩
  insertSet z (insertSet x (lset xs sortedXs))
    ≡⟨ cong (insertSet z) (insertSet-adds-in-front x xs (sortedX , sortedXs)) ⟩
  insertSet z (lset (x ∷ xs) (sortedX , sortedXs)) ∎

union-insert' : (x : A) → (xs : List A) → (ys : LSet (A , OrdA)) 
              → (sorted : IsSortedNoDupList OrdA (x ∷ xs))
              → insertSet x (union (lset xs (proj₂ sorted)) ys) ≡ union (lset (x ∷ xs) sorted) ys
union-insert' z [] ys sorted = refl
union-insert' z (x ∷ xs) ys (sortedZ , sortedXs) = refl
    
union-insert : (z : A) → (xs ys : LSet (A , OrdA))
             → insertSet z (union xs ys) ≡ union (insertSet z xs) ys
union-insert z (lset [] sortedXs) ys = refl
union-insert z (lset (x ∷ xs) sortedXs) ys = {!!}
{-
insertSet z (insertSet x (union (lset xs (proj₂ sortedXs)) ys))
  ≡ 
union (insertSet z (insertSet x (lset xs (proj₂ sortedXs)))) ys
  ≡ 
union (insertSet z (lset (x ∷ xs) sortedXs)) ys
-}


union-commutative : (as bs : LSet (A , OrdA)) → IsStructuralEquality EqA → union as bs ≡ union bs as
union-commutative (lset [] _) bs sEq = sym (union-with-empty bs)
union-commutative (lset (x ∷ xs) (sortedX , sortedXs)) (lset [] sorted) sEq = begin
  insertSet x (union (lset xs sortedXs) (lset [] sorted))
    ≡⟨ cong (insertSet x) (union-with-empty (lset xs sortedXs)) ⟩
  insertSet x (lset xs sortedXs)
    ≡⟨ insertSet-adds-in-front x xs (sortedX , sortedXs) ⟩
  lset (x ∷ xs) (sortedX , sortedXs) ∎
union-commutative (lset (x ∷ xs) (sortedX , sortedXs)) (lset (y ∷ ys) (sortedY , sortedYs)) sEq = begin
  insertSet x ( union (lset xs sortedXs) (lset (y ∷ ys) (sortedY , sortedYs)) )
    ≡⟨ cong (insertSet x) (union-commutative (lset xs sortedXs) (lset (y ∷ ys) (sortedY , sortedYs)) sEq) ⟩
  insertSet x ( union (lset (y ∷ ys) (sortedY , sortedYs)) (lset xs sortedXs) )
    ≡⟨ cong (insertSet x) (sym (union-insert' y ys (lset xs sortedXs) (sortedY , sortedYs)) ) ⟩
  insertSet x (insertSet y ( union (lset ys sortedYs) (lset xs sortedXs) ) )
    ≡⟨ insertSet-commute x y (union (lset ys sortedYs) (lset xs sortedXs)) sEq ⟩
  insertSet y (insertSet x ( union (lset ys sortedYs) (lset xs sortedXs) ) )
    ≡⟨ cong (insertSet y ∘F insertSet x) (union-commutative (lset ys sortedYs) (lset xs sortedXs) sEq) ⟩
  insertSet y (insertSet x ( union (lset xs sortedXs) (lset ys sortedYs) ) )
    ≡⟨ cong (insertSet y) (union-insert' x xs (lset ys sortedYs) (sortedX , sortedXs)) ⟩
  insertSet y ( union (lset (x ∷ xs) (sortedX , sortedXs)) (lset ys sortedYs) )
    ≡⟨ cong (insertSet y) (union-commutative (lset (x ∷ xs) (sortedX , sortedXs)) (lset ys sortedYs) sEq) ⟩
  insertSet y ( union (lset ys sortedYs) (lset (x ∷ xs) (sortedX , sortedXs)) ) ∎

union-assoc : (xs ys zs : LSet (A , OrdA)) → IsStructuralEquality EqA → union xs (union ys zs) ≡ union (union xs ys) zs
union-assoc (lset [] _) (lset [] _) (lset [] _) sEq = refl
union-assoc (lset [] _) (lset [] _) (lset (z ∷ zs) sortedZs) _sEq = refl
union-assoc (lset [] _) (lset (y ∷ ys) sortedYs) (lset [] _) _sEq = refl
union-assoc (lset [] _) (lset (y ∷ ys) sortedYs) (lset (z ∷ zs) sortedZs) _sEq = refl
union-assoc (lset (x ∷ xs) sortedXs) (lset [] sortedYs) (lset [] sortedZs) _sEq = begin
  insertSet x (union (lset xs (proj₂ sortedXs)) (lset [] (lift tt)))
    ≡⟨ cong (insertSet x) (union-with-empty (lset xs (proj₂ sortedXs))) ⟩
  insertSet x (lset xs (proj₂ sortedXs))
    ≡⟨ cong (insertSet x) (sym $ union-with-empty (lset xs (proj₂ sortedXs))) ⟩
  insertSet x (union (lset xs (proj₂ sortedXs)) (lset [] sortedYs))
    ≡⟨ sym (union-with-empty (insertSet x (union (lset xs (proj₂ sortedXs)) (lset [] sortedYs)))) ⟩
  union (insertSet x (union (lset xs (proj₂ sortedXs)) (lset [] sortedYs))) (lset [] sortedZs) ∎
union-assoc (lset (x ∷ xs) sortedXs) (lset [] sortedYs) (lset (z ∷ zs) sortedZs) _sEq = begin
  insertSet x (union (lset xs (proj₂ sortedXs)) (lset (z ∷ zs) sortedZs))
    ≡⟨ union-insert' x xs (lset (z ∷ zs) sortedZs) sortedXs ⟩
  union (lset (x ∷ xs) sortedXs) (lset (z ∷ zs) sortedZs)
    ≡⟨ cong (λ X → union X (lset (z ∷ zs) sortedZs)) (sym (insertSet-adds-in-front x xs sortedXs)) ⟩
  union (insertSet x (lset xs (proj₂ sortedXs))) (lset (z ∷ zs) sortedZs)
    ≡⟨ cong (λ X → union (insertSet x X) (lset (z ∷ zs) sortedZs)) (sym (union-with-empty (lset xs (proj₂ sortedXs)))) ⟩
  union (insertSet x (union (lset xs (proj₂ sortedXs)) (lset [] sortedYs))) (lset (z ∷ zs) sortedZs) ∎
union-assoc (lset (x ∷ xs) sortedXs) (lset (y ∷ ys) sortedYs) (lset [] sortedZs) _sEq = begin
  insertSet x (union (lset xs (proj₂ sortedXs)) (insertSet y (union (lset ys (proj₂ sortedYs)) (lset [] sortedZs))))
    ≡⟨ cong (λ X → insertSet x (union (lset xs (proj₂ sortedXs)) (insertSet y X))) (union-with-empty (lset ys (proj₂ sortedYs))) ⟩
  insertSet x (union (lset xs (proj₂ sortedXs)) (insertSet y (lset ys (proj₂ sortedYs))))
    ≡⟨ cong (λ X → insertSet x (union (lset xs (proj₂ sortedXs)) X)) (insertSet-adds-in-front y ys sortedYs) ⟩
  insertSet x (union (lset xs (proj₂ sortedXs)) (lset (y ∷ ys) sortedYs))
    ≡⟨ sym (union-with-empty (insertSet x (union (lset xs (proj₂ sortedXs)) (lset (y ∷ ys) sortedYs)))) ⟩
  union (insertSet x (union (lset xs (proj₂ sortedXs)) (lset (y ∷ ys) sortedYs))) (lset [] sortedZs) ∎
union-assoc (lset (x ∷ xs) sortedXs) (lset (y ∷ ys) sortedYs) (lset (z ∷ zs) sortedZs)  sEq = begin
  insertSet x (union (lset xs (proj₂ sortedXs)) (insertSet y (union (lset ys (proj₂ sortedYs)) (lset (z ∷ zs) sortedZs))))
    ≡⟨ cong (insertSet x) (union-commutative (lset xs (proj₂ sortedXs)) (insertSet y (union (lset ys (proj₂ sortedYs)) (lset (z ∷ zs) sortedZs))) sEq) ⟩
  insertSet x (union (insertSet y (union (lset ys (proj₂ sortedYs)) (lset (z ∷ zs) sortedZs))) (lset xs (proj₂ sortedXs)))
    ≡⟨ {!!} ⟩
  insertSet x (insertSet y (union (union (lset ys (proj₂ sortedYs)) (lset (z ∷ zs) sortedZs)) (lset xs (proj₂ sortedXs))))
    ≡⟨ cong (λ X → insertSet x (insertSet y (union (union (lset ys (proj₂ sortedYs)) X) (lset xs (proj₂ sortedXs))))) (sym (insertSet-adds-in-front z zs sortedZs)) ⟩
  insertSet x (insertSet y (union (union (lset ys (proj₂ sortedYs)) (insertSet z (lset zs (proj₂ sortedZs)))) (lset xs (proj₂ sortedXs))))
    ≡⟨ cong (λ X → insertSet x (insertSet y (union X (lset xs (proj₂ sortedXs))))) (union-commutative (lset ys (proj₂ sortedYs)) (insertSet z (lset zs (proj₂ sortedZs))) sEq) ⟩
  insertSet x (insertSet y (union (union (insertSet z (lset zs (proj₂ sortedZs))) (lset ys (proj₂ sortedYs))) (lset xs (proj₂ sortedXs))))
    ≡⟨ {!!} ⟩
  insertSet x (insertSet y (union (insertSet z (union (lset zs (proj₂ sortedZs)) (lset ys (proj₂ sortedYs)))) (lset xs (proj₂ sortedXs))))
    ≡⟨ {!!} ⟩
  insertSet x (insertSet y (insertSet z (union (union (lset zs (proj₂ sortedZs)) (lset ys (proj₂ sortedYs))) (lset xs (proj₂ sortedXs)))))
    ≡⟨ cong (insertSet x ∘F insertSet y ∘F insertSet z) (sym $ union-assoc (lset zs (proj₂ sortedZs)) (lset ys (proj₂ sortedYs)) (lset xs (proj₂ sortedXs)) sEq) ⟩
  insertSet x (insertSet y (insertSet z (union (lset zs (proj₂ sortedZs)) (union (lset ys (proj₂ sortedYs)) (lset xs (proj₂ sortedXs))))))
    ≡⟨ {!!} ⟩
  insertSet x (insertSet y (union (insertSet z (lset zs (proj₂ sortedZs))) (union (lset ys (proj₂ sortedYs)) (lset xs (proj₂ sortedXs)))))
    ≡⟨ cong (λ X → insertSet x (insertSet y (union X (union (lset ys (proj₂ sortedYs)) (lset xs (proj₂ sortedXs)))))) (insertSet-adds-in-front z zs sortedZs) ⟩
  insertSet x (insertSet y (union (lset (z ∷ zs) sortedZs) (union (lset ys (proj₂ sortedYs)) (lset xs (proj₂ sortedXs)))))
    ≡⟨ {!!} ⟩
  insertSet x (union (lset (z ∷ zs) sortedZs) (insertSet y (union (lset ys (proj₂ sortedYs)) (lset xs (proj₂ sortedXs)))))
    ≡⟨ {!!} ⟩
  insertSet x (union (lset (z ∷ zs) sortedZs) (union (insertSet y (lset ys (proj₂ sortedYs))) (lset xs (proj₂ sortedXs))))
    ≡⟨ cong (λ X → insertSet x (union (lset (z ∷ zs) sortedZs) (union X (lset xs (proj₂ sortedXs))))) (insertSet-adds-in-front y ys sortedYs) ⟩
  insertSet x (union (lset (z ∷ zs) sortedZs) (union (lset (y ∷ ys) sortedYs) (lset xs (proj₂ sortedXs))))
    ≡⟨ cong (insertSet x) (union-commutative (lset (z ∷ zs) sortedZs) (union (lset (y ∷ ys) sortedYs) (lset xs (proj₂ sortedXs))) sEq) ⟩
  insertSet x (union (union (lset (y ∷ ys) sortedYs) (lset xs (proj₂ sortedXs))) (lset (z ∷ zs) sortedZs))
    ≡⟨ cong (λ X → insertSet x (union X (lset (z ∷ zs) sortedZs))) (union-commutative (lset (y ∷ ys) sortedYs) (lset xs (proj₂ sortedXs)) sEq) ⟩
  insertSet x (union (union (lset xs (proj₂ sortedXs)) (lset (y ∷ ys) sortedYs)) (lset (z ∷ zs) sortedZs))
    ≡⟨ {!!} ⟩
  union (insertSet x (union (lset xs (proj₂ sortedXs)) (lset (y ∷ ys) sortedYs))) (lset (z ∷ zs) sortedZs) ∎

{-
unions : LSet (LSet (A , OrdA) , OrdLSet {ℓ} {(A , OrdA)}) → LSet (A , OrdA)
unions (lset [] (lift tt)) = lset [] (lift tt)
unions (lset (ys ∷ yss) (sortedYs , sortedYss)) = union ys (unions (lset yss sortedYss))
-}



