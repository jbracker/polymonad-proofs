
open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Level renaming ( suc to lsuc ; zero to lzero)
open import Data.Unit hiding ( _≤_ ; _≟_ ; total )
open import Data.Empty
open import Data.List
open import Data.List.Any hiding ( map )
open import Data.Product hiding ( map )
open import Data.Sum hiding ( map )
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Haskell
open import ProofIrrelevance 

open import Theory.Examples.Haskell.FunctorSet.Base

module Theory.Examples.Haskell.FunctorSet.Sort {ℓEq ℓOrd : Level} {A : Type} (OrdA : OrdInstance {ℓEq} {ℓOrd} A) where
  
private
  open module LP = ListProperties OrdA
  open OrdInstance OrdA
                   
insert : A → List A → List A
insert x [] = x ∷ []
insert x (y ∷ ys) with dec-ord x y
insert x (y ∷ ys) | yes x≤y = x ∷ y ∷ ys
insert x (y ∷ ys) | no ¬x≤y = y ∷ insert x ys
                                           
insert-preserves-sorted' : (x z : A) → (xs : List A) → x ≤ z
                         → IsSortedList (x ∷ xs) → IsSortedList (x ∷ insert z xs)
insert-preserves-sorted' x z [] x≤z (lift tt) with dec-ord x z 
insert-preserves-sorted' x z [] x≤z (lift tt) | yes _ = x≤z , lift tt
insert-preserves-sorted' x z [] x≤z (lift tt) | no ¬x≤z = ⊥-elim (¬x≤z x≤z)
insert-preserves-sorted' x z (y ∷ xs) x≤z (x≤y , sorted[y∷xs]) with dec-ord x z
insert-preserves-sorted' x z (y ∷ xs) x≤z (x≤y , sorted[y∷xs]) | yes _ with dec-ord z y
insert-preserves-sorted' x z (y ∷ xs) x≤z (x≤y , sorted[y∷xs]) | yes _ | yes z≤y = x≤z , z≤y , sorted[y∷xs]
insert-preserves-sorted' x z (y ∷ xs) x≤z (x≤y , sorted[y∷xs]) | yes _ | no ¬z≤y 
  = x≤y , insert-preserves-sorted' y z xs (excluded-middle-ord ¬z≤y) sorted[y∷xs]
insert-preserves-sorted' x z (y ∷ xs) x≤z (x≤y , sorted[y∷xs]) | no ¬x≤z = ⊥-elim (¬x≤z x≤z)

insert-preserves-sorted : (x : A) → (xs : List A) 
                        → IsSortedList xs → IsSortedList (insert x xs)
insert-preserves-sorted x [] (lift tt) = lift tt
insert-preserves-sorted x (y ∷ []) (lift tt) with dec-ord x y 
insert-preserves-sorted x (y ∷ []) (lift tt) | yes x≤y = x≤y , lift tt
insert-preserves-sorted x (y ∷ []) (lift tt) | no ¬x≤y with total y x
insert-preserves-sorted x (y ∷ []) (lift tt) | no ¬x≤y | inj₁ y≤x = y≤x , lift tt
insert-preserves-sorted x (y ∷ []) (lift tt) | no ¬x≤y | inj₂ x≤y = ⊥-elim (¬x≤y x≤y)
insert-preserves-sorted x (y ∷ z ∷ xs) (y≤z , sorted[z∷xs]) with dec-ord x y
insert-preserves-sorted x (y ∷ z ∷ xs) (y≤z , sorted[z∷xs]) | yes x≤y = x≤y , y≤z , sorted[z∷xs]
insert-preserves-sorted x (y ∷ z ∷ xs) (y≤z , sorted[z∷xs]) | no ¬x≤y with total x y
insert-preserves-sorted x (y ∷ z ∷ xs) (y≤z , sorted[z∷xs]) | no ¬x≤y | inj₁ x≤y = ⊥-elim (¬x≤y x≤y)
insert-preserves-sorted x (y ∷ z ∷ xs) (y≤z , sorted[z∷xs]) | no ¬x≤y | inj₂ y≤x with dec-ord x z
insert-preserves-sorted x (y ∷ z ∷ xs) (y≤z , sorted[z∷xs]) | no ¬x≤y | inj₂ y≤x | yes x≤z = y≤x , x≤z , sorted[z∷xs]
insert-preserves-sorted x (y ∷ z ∷ xs) (y≤z , sorted[z∷xs]) | no ¬x≤y | inj₂ y≤x | no ¬x≤z with insert-preserves-sorted' z x xs (excluded-middle-ord ¬x≤z) sorted[z∷xs]
insert-preserves-sorted x (y ∷ z ∷ xs) (y≤z , sorted[z∷xs]) | no ¬x≤y | inj₂ y≤x | no ¬x≤z | p = y≤z , p

insert-preserves-missing-elem : (x y : A) → (xs : List A) → ¬ (x == y)
                              → ¬ InList x xs → ¬ InList x (insert y xs)
insert-preserves-missing-elem x y [] ¬y==x ¬x∈xs (here y==x) = ¬y==x y==x
insert-preserves-missing-elem x y [] ¬y==x ¬x∈xs (there ())
insert-preserves-missing-elem x y (z ∷ xs) ¬y==x ¬x∈xs x∈insxs with dec-ord y z
insert-preserves-missing-elem x y (z ∷ xs) ¬y==x ¬x∈xs x∈insxs | yes y≤z 
  = ¬x∈xs (InList-forget-elem x y (z ∷ xs) ¬y==x x∈insxs)
insert-preserves-missing-elem x y (z ∷ xs) ¬y==x ¬x∈xs (here x==z) | no ¬y≤z = ¬x∈xs (here x==z)
insert-preserves-missing-elem x y (z ∷ xs) ¬y==x ¬x∈xs (there x∈insxs) | no ¬y≤z 
  = insert-preserves-missing-elem x y xs ¬y==x (¬InList-forget-elem x z xs ¬x∈xs) x∈insxs

insert-smallest-in-front' : (x y : A) → (xs : List A) → x ≤ y
                          → insert x (y ∷ xs) ≡ x ∷ y ∷ xs
insert-smallest-in-front' x y [] x≤y with dec-ord  x y
insert-smallest-in-front' x y [] x≤y | yes _ = refl
insert-smallest-in-front' x y [] x≤y | no ¬x≤y = ⊥-elim (¬x≤y x≤y)
insert-smallest-in-front' x y (z ∷ xs) x≤y with dec-ord  x y 
insert-smallest-in-front' x y (z ∷ xs) x≤y | yes _ = refl
insert-smallest-in-front' x y (z ∷ xs) x≤y | no ¬x≤y = ⊥-elim (¬x≤y x≤y)

insert-smallest-in-front : (x : A) → (xs : List A)
                         → IsSortedList (x ∷ xs)
                         → insert x xs ≡ x ∷ xs
insert-smallest-in-front x [] (lift tt) = refl
insert-smallest-in-front x (y ∷ xs) (x≤y , sorted) = insert-smallest-in-front' x y xs x≤y

insert-shift-elem : (y x : A) → (xs : List A)
                  → x ≤ y → ¬ (y == x)
                  → insert y (x ∷ xs) ≡ x ∷ insert y xs
insert-shift-elem y x [] x≤y ¬y==x with dec-ord  y x
insert-shift-elem y x [] x≤y ¬y==x | yes y≤x = ⊥-elim (¬y==x (antisym-ord y≤x x≤y))
insert-shift-elem y x [] x≤y ¬y==x | no ¬y≤x = refl
insert-shift-elem y x (z ∷ xs) x≤y ¬y==x with dec-ord y x
insert-shift-elem y x (z ∷ xs) x≤y ¬y==x | yes y≤x = ⊥-elim (¬y==x (antisym-ord y≤x x≤y))
insert-shift-elem y x (z ∷ xs) x≤y ¬y==x | no ¬y≤x with dec-ord y z
insert-shift-elem y x (z ∷ xs) x≤y ¬y==x | no ¬y≤x | yes y≤z = refl
insert-shift-elem y x (z ∷ xs) x≤y ¬y==x | no ¬y≤x | no ¬y≤z = refl

insert-interchange : (x y : A) → (xs : List A) 
                   → ¬ (x == y)
                   → insert x (insert  y xs) ≡ insert y (insert x xs)
insert-interchange x y [] ¬x==y with dec-ord x y | dec-ord y x
insert-interchange x y [] ¬x==y | yes x≤y | yes y≤x = ⊥-elim (¬x==y (antisym-ord x≤y y≤x))
insert-interchange x y [] ¬x==y | yes x≤y | no ¬y≤x = refl
insert-interchange x y [] ¬x==y | no ¬x≤y | yes y≤x = refl
insert-interchange x y [] ¬x==y | no ¬x≤y | no ¬y≤x = ⊥-elim (total-contr ¬y≤x ¬x≤y)
insert-interchange x y (z ∷ xs) ¬x==y with dec-ord y z 
insert-interchange x y (z ∷ xs) ¬x==y | yes y≤z with dec-ord x y
insert-interchange x y (z ∷ xs) ¬x==y | yes y≤z | yes x≤y with dec-ord x z
insert-interchange x y (z ∷ xs) ¬x==y | yes y≤z | yes x≤y | yes x≤z with dec-ord y x
insert-interchange x y (z ∷ xs) ¬x==y | yes y≤z | yes x≤y | yes x≤z | yes y≤x = ⊥-elim (¬x==y (antisym-ord x≤y y≤x))
insert-interchange x y (z ∷ xs) ¬x==y | yes y≤z | yes x≤y | yes x≤z | no ¬y≤x with dec-ord y z
insert-interchange x y (z ∷ xs) ¬x==y | yes y≤z | yes x≤y | yes x≤z | no ¬y≤x | yes _ = refl
insert-interchange x y (z ∷ xs) ¬x==y | yes y≤z | yes x≤y | yes x≤z | no ¬y≤x | no ¬y≤z = ⊥-elim (¬y≤z y≤z)
insert-interchange x y (z ∷ xs) ¬x==y | yes y≤z | yes x≤y | no ¬x≤z = ⊥-elim (¬x≤z (trans-ord x≤y y≤z))
insert-interchange x y (z ∷ xs) ¬x==y | yes y≤z | no ¬x≤y with dec-ord x z
insert-interchange x y (z ∷ xs) ¬x==y | yes y≤z | no ¬x≤y | yes x≤z with dec-ord y x
insert-interchange x y (z ∷ xs) ¬x==y | yes y≤z | no ¬x≤y | yes x≤z | yes y≤x = refl
insert-interchange x y (z ∷ xs) ¬x==y | yes y≤z | no ¬x≤y | yes x≤z | no ¬y≤x = ⊥-elim (total-contr ¬x≤y ¬y≤x)
insert-interchange x y (z ∷ xs) ¬x==y | yes y≤z | no ¬x≤y | no ¬x≤z with dec-ord y z
insert-interchange x y (z ∷ xs) ¬x==y | yes y≤z | no ¬x≤y | no ¬x≤z | yes _ = refl
insert-interchange x y (z ∷ xs) ¬x==y | yes y≤z | no ¬x≤y | no ¬x≤z | no ¬y≤z = ⊥-elim (¬y≤z y≤z)
insert-interchange x y (z ∷ xs) ¬x==y | no ¬y≤z with dec-ord x z
insert-interchange x y (z ∷ xs) ¬x==y | no ¬y≤z | yes x≤z with dec-ord y x
insert-interchange x y (z ∷ xs) ¬x==y | no ¬y≤z | yes x≤z | yes y≤x = ⊥-elim (¬y≤z (trans-ord y≤x x≤z))
insert-interchange x y (z ∷ xs) ¬x==y | no ¬y≤z | yes x≤z | no ¬y≤x with dec-ord y z
insert-interchange x y (z ∷ xs) ¬x==y | no ¬y≤z | yes x≤z | no ¬y≤x | yes y≤z = ⊥-elim (¬y≤z y≤z)
insert-interchange x y (z ∷ xs) ¬x==y | no ¬y≤z | yes x≤z | no ¬y≤x | no _ = refl
insert-interchange x y (z ∷ xs) ¬x==y | no ¬y≤z | no ¬x≤z with dec-ord y z
insert-interchange x y (z ∷ xs) ¬x==y | no ¬y≤z | no ¬x≤z | yes y≤z = ⊥-elim (¬y≤z y≤z)
insert-interchange x y (z ∷ xs) ¬x==y | no ¬y≤z | no ¬x≤z | no _ = cong (λ X → z ∷ X) (insert-interchange x y xs ¬x==y)

sort : List A → List A
sort  [] = []
sort  (x ∷ xs) = insert x (sort  xs)

sort-produces-sorted : (xs : List A) → IsSortedList  (sort  xs)
sort-produces-sorted [] = lift tt
sort-produces-sorted (x ∷ []) = lift tt
sort-produces-sorted (x ∷ y ∷ xs) = insert-preserves-sorted x (insert  y (sort xs))
                                  $ insert-preserves-sorted y (sort xs) (sort-produces-sorted xs)

sort-sorting-sorted : (xs : List A) → IsSortedList  xs → sort  xs ≡ xs
sort-sorting-sorted [] sorted = refl
sort-sorting-sorted (y ∷ []) sorted = refl
sort-sorting-sorted (y ∷ x ∷ xs) (y≤x , sorted) with sort-sorting-sorted  (x ∷ xs) sorted
sort-sorting-sorted (y ∷ x ∷ xs) (y≤x , sorted) | p =
  trans (cong (insert  y) p) (insert-smallest-in-front  y (x ∷ xs) (y≤x , sorted))

sort-shrink : (xs : List A) → sort (sort xs) ≡ sort xs
sort-shrink [] = refl
sort-shrink (x ∷ xs) = sort-sorting-sorted (insert x (sort  xs)) (insert-preserves-sorted x (sort  xs) (sort-produces-sorted xs))
  
