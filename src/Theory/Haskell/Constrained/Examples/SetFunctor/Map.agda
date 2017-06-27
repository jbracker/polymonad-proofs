
open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Level

open import Data.Unit hiding ( _≤_ ; _≟_ ; total )
open import Data.Product hiding ( map )
open import Data.List

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Theory.Haskell.Constrained.Examples.SetFunctor.Base
open import Theory.Haskell.Constrained.Examples.SetFunctor.Insert

module Theory.Haskell.Constrained.Examples.SetFunctor.Map {ℓA ℓB ℓEqA ℓEqB ℓOrdA ℓOrdB : Level} {A : Set ℓA} {B : Set ℓB} {OrdA : OrdInstance {ℓA} {ℓEqA} {ℓOrdA} A} {OrdB : OrdInstance {ℓB} {ℓEqB} {ℓOrdB} B} where  

open OrdInstance
open ≡-Reasoning

private
  _=A=_ = _==_ OrdA
  _=B=_ = _==_ OrdB

mapSet : (A → B) → LSet (A , OrdA) → LSet (B , OrdB)
mapSet f (lset [] (lift tt)) = lset [] (lift tt)
mapSet f (lset (x ∷ xs) (allX , sortedX)) = insertSet (f x) (mapSet f (lset xs sortedX))

mapList : (A → B) → List A → List B
mapList f [] = []
mapList f (x ∷ xs) = insert {A = B} {OrdB} (f x) (mapList f xs)

mapList-produces-IsSortedNoDupList : (f : A → B) → (xs : List A) → IsSortedNoDupList OrdB (mapList f xs)
mapList-produces-IsSortedNoDupList f [] = lift tt
mapList-produces-IsSortedNoDupList f (x ∷ xs) = insert-preserves-IsSortedNoDupList (mapList-produces-IsSortedNoDupList f xs)

abstract
  struct-eq-preserves-equality : (f : A → B)
                               → IsStructuralEquality (eqInstance OrdA)
                               → (a b : A) → (a =A= b) → (f a =B= f b)
  struct-eq-preserves-equality f struct-eqX a b a=A=b with struct-eqX a b a=A=b
  struct-eq-preserves-equality f struct-eqX a .a a=A=b | refl = refl-eq OrdB {f a}

abstract
  map-insert-commute : (f : A → B) → (x : A) → (xs : List A) 
                     → IsStructuralEquality (eqInstance OrdA)
                     → IsStructuralEquality (eqInstance OrdB)
                     → mapList f (insert {A = A} {OrdA} x xs) ≡ insert {A = B} {OrdB} (f x) (mapList f xs)
  map-insert-commute f x [] _ _ = refl
  map-insert-commute f x (y  ∷ ys) struct-eqA struct-eqB with dec-eq OrdA x y
  map-insert-commute f x (y  ∷ ys) struct-eqA struct-eqB | yes x=y with struct-eqA x y x=y
  map-insert-commute f x (.x ∷ ys) struct-eqA struct-eqB | yes x=y | refl 
    = sym $ insert-elim {A = B} {OrdB} {f x} {f x} {mapList f ys} (struct-eq-preserves-equality f struct-eqA x x x=y)
  map-insert-commute f x (y ∷ ys) struct-eqA struct-eqB | no ¬x=y with dec-ord OrdA x y
  map-insert-commute f x (y ∷ ys) struct-eqA struct-eqB | no ¬x=y | yes x≤y = refl
  map-insert-commute f x (y ∷ ys) struct-eqA struct-eqB | no ¬x=y | no ¬x≤y with dec-eq OrdB (f x) (f y)
  map-insert-commute f x (y ∷ ys) struct-eqA struct-eqB | no ¬x=y | no ¬x≤y | yes fx=fy = begin
    insert (f y) (mapList f (insert x ys))
      ≡⟨ cong (insert (f y)) (map-insert-commute f x ys struct-eqA struct-eqB) ⟩
    insert (f y) (insert (f x) (mapList f ys))
      ≡⟨ insert-elim {A = B} {OrdB} {f y} {f x} {mapList f ys} (sym-eq OrdB fx=fy) ⟩
    insert (f y) (mapList f ys)
      ≡⟨ cong (λ X → insert X (mapList f ys)) (sym (struct-eqB (f x) (f y) fx=fy)) ⟩
    insert (f x) (mapList f ys)
      ≡⟨ sym (insert-elim {A = B} {OrdB} {f x} {f y} {mapList f ys} fx=fy) ⟩
    insert (f x) (insert (f y) (mapList f ys)) ∎
  map-insert-commute f x (y ∷ ys) struct-eqA struct-eqB | no ¬x=y | no ¬x≤y | no ¬fx=fy = begin
    insert (f y) (mapList f (insert x ys))
      ≡⟨ cong (insert (f y)) (map-insert-commute f x ys struct-eqA struct-eqB) ⟩
    insert (f y) (insert (f x) (mapList f ys))
      ≡⟨ insert-commute {A = B} {OrdB} {f y} {f x} {mapList f ys} (sym-not-eq OrdB ¬fx=fy) ⟩
    insert (f x) (insert (f y) (mapList f ys)) ∎

abstract
  map-structure : (f : A → B) → (set : LSet (A , OrdA)) → LSet.xs (mapSet f set) ≡ mapList f (LSet.xs set)
  map-structure f (lset [] (lift tt)) = refl
  map-structure f (lset (x ∷ xs) (allX , sortedX)) = begin
    LSet.xs (insertSet (f x) (mapSet f (lset xs sortedX))) 
      ≡⟨⟩
    insert (f x) (LSet.xs (mapSet f (lset xs sortedX)))
      ≡⟨ cong (insert (f x)) (map-structure f (lset xs sortedX)) ⟩
    insert (f x) (mapList f xs) ∎
