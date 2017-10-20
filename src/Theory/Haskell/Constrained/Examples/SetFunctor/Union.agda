
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

private
  module SingleType {A : Set ℓ} {OrdA : OrdInstance {ℓ} {ℓ} {ℓ} A} where
    
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
    
    --  insert-elim : {x y : A} {zs : List A} → x == y → insert x (insert y zs) ≡ insert x zs
    --  insert-commute : {x y : A} {xs : List A} → ¬ (x == y) → insert x (insert y xs) ≡ insert y (insert x xs)
    
    union-insert' : (x : A) → (xs : List A) → (ys : LSet (A , OrdA)) 
                  → (sorted : IsSortedNoDupList OrdA (x ∷ xs))
                  → insertSet x (union (lset xs (proj₂ sorted)) ys) ≡ union (lset (x ∷ xs) sorted) ys
    union-insert' z [] ys sorted = refl
    union-insert' z (x ∷ xs) ys (sortedZ , sortedXs) = refl
    
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
    {-
    union-insert : (x : A) → (xs : List A) → (ys : LSet (A , OrdA)) (sorted : IsSortedNoDupList OrdA (x ∷ xs)) 
                 → insertSet x (union (lset xs (proj₂ sorted)) ys) ≡ union (insertSet x (lset xs (proj₂ sorted))) ys
    union-insert z [] ys _ = refl
    union-insert z (x ∷ xs) ys (sortedZ , sortedX , sortedXs) = {!!}
    -}

open SingleType public

private
  module TwoTypes {A B : Set ℓ} {OrdA : OrdInstance {ℓ} {ℓ} {ℓ} A} {OrdB : OrdInstance {ℓ} {ℓ} {ℓ} B} where
    
    open OrdInstance OrdA renaming ( eqInstance to EqA )
    open OrdInstance OrdB renaming ( eqInstance to EqB )
    
    union-dist : (f : LSet (A , OrdA) → LSet (B , OrdB)) 
               → (xs ys : LSet (A , OrdA))
               → f (union xs ys) ≡ union (f xs) (f ys)
    union-dist f xs ys = {!!}

open TwoTypes public

{-
unions : LSet (LSet (A , OrdA) , OrdLSet {ℓ} {(A , OrdA)}) → LSet (A , OrdA)
unions (lset [] (lift tt)) = lset [] (lift tt)
unions (lset (ys ∷ yss) (sortedYs , sortedYss)) = union ys (unions (lset yss sortedYss))
-}


