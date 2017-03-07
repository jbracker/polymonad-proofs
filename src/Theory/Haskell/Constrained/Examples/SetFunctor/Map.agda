
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

mapSet : (X → A) → LSet (X , OrdX) → LSet (A , OrdA)
mapSet f (lset [] (lift tt)) = lset [] (lift tt)
mapSet f (lset (x ∷ xs) (allX , sortedX)) = insertSet (f x) (mapSet f (lset xs sortedX))
                                                                            
mapList : (X → A) → List X → List A
mapList f [] = []
mapList f (x ∷ xs) = insert {A} {OrdA} (f x) (mapList f xs)
                                          
mapList-produces-IsSortedNoDupList : (f : X → A) → (xs : List X) → IsSortedNoDupList OrdA (mapList f xs)
mapList-produces-IsSortedNoDupList f [] = lift tt
mapList-produces-IsSortedNoDupList f (x ∷ xs) = insert-preserves-IsSortedNoDupList (mapList-produces-IsSortedNoDupList f xs)

map-insert-commute : (f : X → A) → (x : X) → (xs : List X) 
                       → IsSortedNoDupList OrdX xs
                       → mapList f (insert {X} {OrdX} x xs) ≡ insert {A} {OrdA} (f x) (mapList f xs)
map-insert-commute f x [] (lift tt) = refl
map-insert-commute f x (y ∷ ys) sorted with dec-eq OrdX x y
map-insert-commute f x (y ∷ ys) sorted | yes x=y = begin
   insert (f x) (mapList f ys) 
     ≡⟨ {!!} ⟩
   insert (f x) (insert (f y) (mapList f ys)) ∎
map-insert-commute f x (y ∷ ys) sorted | no ¬x=y with dec-ord OrdX x y
map-insert-commute f x (y ∷ ys) sorted | no ¬x=y | yes x≤y = refl
map-insert-commute f x (y ∷ ys) sorted | no ¬x=y | no ¬x≤y with dec-eq OrdA (f x) (f y)
map-insert-commute f x (y ∷ ys) sorted | no ¬x=y | no ¬x≤y | yes fx=fy = begin
  insert (f y) (mapList f (insert x ys))
    ≡⟨ {!!} ⟩
  insert (f x) (insert (f y) (mapList f ys)) ∎
map-insert-commute f x (y ∷ ys) sorted | no ¬x=y | no ¬x≤y | no ¬fx=fy = begin
  insert (f y) (mapList f (insert x ys))
    ≡⟨ cong (insert (f y)) (map-insert-commute f x ys (proj₂ sorted)) ⟩
  insert (f y) (insert (f x) (mapList f ys))
    ≡⟨ insert-commute (sym-not-eq OrdA ¬fx=fy) (mapList-produces-IsSortedNoDupList f ys) ⟩
  insert (f x) (insert (f y) (mapList f ys)) ∎
    
map-structure : (f : X → A) → (set : LSet (X , OrdX)) → LSet.xs (mapSet f set) ≡ mapList f (LSet.xs set)
map-structure f (lset [] (lift tt)) = refl
map-structure f (lset (x ∷ xs) (allX , sortedX)) = begin
  LSet.xs (insertSet (f x) (mapSet f (lset xs sortedX))) 
    ≡⟨⟩
  insert (f x) (LSet.xs (mapSet f (lset xs sortedX)))
    ≡⟨ cong (insert (f x)) (map-structure f (lset xs sortedX)) ⟩
  insert (f x) (mapList f xs) ∎
