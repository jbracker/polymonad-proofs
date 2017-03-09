
open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Level renaming ( suc to lsuc ; zero to lzero)
open import Data.Unit hiding ( _≤_ ; _≟_ ; total )
open import Data.Empty
open import Data.Product hiding ( map )
open import Data.List hiding ( map )
open import Data.List.All hiding ( map )
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Haskell

open import Theory.Haskell.Constrained.Examples.SetFunctor.Base
open import Theory.Haskell.Constrained.Examples.SetFunctor.Insert

module Theory.Haskell.Constrained.Examples.SetFunctor.Map {A : Type} {X : Type} {OrdA : OrdInstance {lzero} {lzero} A} {OrdX : OrdInstance {lzero} {lzero} X} where  

open OrdInstance
open ≡-Reasoning

private
  _=A=_ = _==_ OrdA
  _=X=_ = _==_ OrdX

mapSet : (X → A) → LSet (X , OrdX) → LSet (A , OrdA)
mapSet f (lset [] (lift tt)) = lset [] (lift tt)
mapSet f (lset (x ∷ xs) (allX , sortedX)) = insertSet (f x) (mapSet f (lset xs sortedX))
                                                                            
mapList : (X → A) → List X → List A
mapList f [] = []
mapList f (x ∷ xs) = insert {A} {OrdA} (f x) (mapList f xs)
                                          
mapList-produces-IsSortedNoDupList : (f : X → A) → (xs : List X) → IsSortedNoDupList OrdA (mapList f xs)
mapList-produces-IsSortedNoDupList f [] = lift tt
mapList-produces-IsSortedNoDupList f (x ∷ xs) = insert-preserves-IsSortedNoDupList (mapList-produces-IsSortedNoDupList f xs)

struct-eq-preserves-equality : (f : X → A)
                             → IsStructuralEquality OrdX
                             → (a b : X) → (a =X= b) → (f a =A= f b)
struct-eq-preserves-equality f struct-eqX a b a=X=b with struct-eqX a b a=X=b
struct-eq-preserves-equality f struct-eqX a .a a=X=b | refl = refl-eq OrdA {f a}

map-insert-commute : (f : X → A) → (x : X) → (xs : List X) 
                   → IsStructuralEquality OrdX
                   → IsStructuralEquality OrdA
                   → mapList f (insert {X} {OrdX} x xs) ≡ insert {A} {OrdA} (f x) (mapList f xs)
map-insert-commute f x [] _ _ = refl
map-insert-commute f x (y  ∷ ys) struct-eqX struct-eqA with dec-eq OrdX x y
map-insert-commute f x (y  ∷ ys) struct-eqX struct-eqA | yes x=y with struct-eqX x y x=y
map-insert-commute f x (.x ∷ ys) struct-eqX struct-eqA | yes x=y | refl 
  = sym $ insert-elim {A} {OrdA} {f x} {f x} {mapList f ys} (struct-eq-preserves-equality f struct-eqX x x x=y)
map-insert-commute f x (y ∷ ys) struct-eqX struct-eqA | no ¬x=y with dec-ord OrdX x y
map-insert-commute f x (y ∷ ys) struct-eqX struct-eqA | no ¬x=y | yes x≤y = refl
map-insert-commute f x (y ∷ ys) struct-eqX struct-eqA | no ¬x=y | no ¬x≤y with dec-eq OrdA (f x) (f y)
map-insert-commute f x (y ∷ ys) struct-eqX struct-eqA | no ¬x=y | no ¬x≤y | yes fx=fy = begin
  insert (f y) (mapList f (insert x ys))
    ≡⟨ cong (insert (f y)) (map-insert-commute f x ys struct-eqX struct-eqA) ⟩
  insert (f y) (insert (f x) (mapList f ys))
    ≡⟨ insert-elim {A} {OrdA} {f y} {f x} {mapList f ys} (sym-eq OrdA fx=fy) ⟩
  insert (f y) (mapList f ys)
    ≡⟨ cong (λ X → insert X (mapList f ys)) (sym (struct-eqA (f x) (f y) fx=fy)) ⟩
  insert (f x) (mapList f ys)
    ≡⟨ sym (insert-elim {A} {OrdA} {f x} {f y} {mapList f ys} fx=fy) ⟩
  insert (f x) (insert (f y) (mapList f ys)) ∎
map-insert-commute f x (y ∷ ys) struct-eqX struct-eqA | no ¬x=y | no ¬x≤y | no ¬fx=fy = begin
  insert (f y) (mapList f (insert x ys))
    ≡⟨ cong (insert (f y)) (map-insert-commute f x ys struct-eqX struct-eqA) ⟩
  insert (f y) (insert (f x) (mapList f ys))
    ≡⟨ insert-commute {A} {OrdA} {f y} {f x} {mapList f ys} (sym-not-eq OrdA ¬fx=fy) ⟩
  insert (f x) (insert (f y) (mapList f ys)) ∎
    
map-structure : (f : X → A) → (set : LSet (X , OrdX)) → LSet.xs (mapSet f set) ≡ mapList f (LSet.xs set)
map-structure f (lset [] (lift tt)) = refl
map-structure f (lset (x ∷ xs) (allX , sortedX)) = begin
  LSet.xs (insertSet (f x) (mapSet f (lset xs sortedX))) 
    ≡⟨⟩
  insert (f x) (LSet.xs (mapSet f (lset xs sortedX)))
    ≡⟨ cong (insert (f x)) (map-structure f (lset xs sortedX)) ⟩
  insert (f x) (mapList f xs) ∎
