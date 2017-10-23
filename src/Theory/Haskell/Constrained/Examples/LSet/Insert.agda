
open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Level

open import Data.Unit hiding ( _≤_ ; _≟_ ; total )
open import Data.Empty
open import Data.List hiding ( map )
open import Data.List.All hiding ( map )
open import Data.Product hiding ( map )

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Extensionality

open import Theory.Haskell.Constrained.Examples.LSet.Base

module Theory.Haskell.Constrained.Examples.LSet.Insert {ℓ ℓEq ℓOrd : Level} {A : Set ℓ} {OrdA : OrdInstance {ℓ} {ℓEq} {ℓOrd} A} where 

open OrdInstance OrdA renaming ( eqInstance to EqA )

private
  Type = Set ℓ

insert : A → List A → List A
insert a [] = a ∷ []
insert a (b ∷ as) with dec-eq a b
insert a (b ∷ as) | yes a==b = a ∷ as
insert a (b ∷ as) | no ¬a==b with dec-ord a b
insert a (b ∷ as) | no ¬a==b | yes a≤b = a ∷ b ∷ as
insert a (b ∷ as) | no ¬a==b | no ¬a≤b = b ∷ insert a as

insert-preserves-IsSortedNoDupList' : {a x : A} {xs : List A}
                                    → ¬ (a ≤ x) → ¬ (a == x) 
                                    → All (λ y → x ≤ y × ¬ x == y) xs → All (λ y → x ≤ y × ¬ x == y) (insert a xs)
insert-preserves-IsSortedNoDupList' {a} {x} {[]} ¬a≤x a≠x [] = (excluded-middle-ord ¬a≤x , sym-not-eq a≠x) ∷ []
insert-preserves-IsSortedNoDupList' {a} {x} {z ∷ zs} ¬a≤x a≠x ((x≤z , x≠z) ∷ allZ) with dec-eq a z
insert-preserves-IsSortedNoDupList' {a} {x} {z ∷ zs} ¬a≤x a≠x ((x≤z , x≠z) ∷ allZ) | yes a=z 
  = (excluded-middle-ord ¬a≤x , sym-not-eq a≠x) ∷ allZ
insert-preserves-IsSortedNoDupList' {a} {x} {z ∷ zs} ¬a≤x a≠x ((x≤z , x≠z) ∷ allZ) | no ¬a=z with dec-ord a z
insert-preserves-IsSortedNoDupList' {a} {x} {z ∷ zs} ¬a≤x a≠x ((x≤z , x≠z) ∷ allZ) | no ¬a=z | yes a≤z 
  = (excluded-middle-ord ¬a≤x , sym-not-eq a≠x) ∷ (x≤z , x≠z) ∷ allZ
insert-preserves-IsSortedNoDupList' {a} {x} {z ∷ zs} ¬a≤x a≠x ((x≤z , x≠z) ∷ allZ) | no ¬a=z | no ¬a≤z
  = (x≤z , x≠z) ∷ insert-preserves-IsSortedNoDupList' ¬a≤x a≠x allZ
    
insert-preserves-IsSortedNoDupList : {a : A} {xs : List A} → IsSortedNoDupList OrdA xs → IsSortedNoDupList OrdA (insert a xs)
insert-preserves-IsSortedNoDupList {a} {[]} (lift tt) = [] , lift tt
insert-preserves-IsSortedNoDupList {a} {x ∷ xs} (allX , sorted) with dec-eq a x
insert-preserves-IsSortedNoDupList {a} {x ∷ xs} (allX , sorted) | yes a=x = IsSortedNoDupList-replace-eq' OrdA (sym-eq a=x) allX , sorted
insert-preserves-IsSortedNoDupList {a} {x ∷ xs} (allX , sorted) | no ¬a=x with dec-ord a x
insert-preserves-IsSortedNoDupList {a} {x ∷ xs} (allX , sorted) | no ¬a=x | yes a≤x = (a≤x , ¬a=x) ∷ IsSortedNoDupList-replace-ord' OrdA a≤x allX , allX , sorted
insert-preserves-IsSortedNoDupList {a} {x ∷ xs} (allX , sorted) | no ¬a=x | no ¬a≤x = insert-preserves-IsSortedNoDupList' ¬a≤x ¬a=x allX , insert-preserves-IsSortedNoDupList sorted

abstract
  insert-adds-in-front : {x : A} {xs : List A} → All (λ y → x ≤ y × ¬ (x == y)) xs → insert x xs ≡ x ∷ xs
  insert-adds-in-front {x} {[]} [] = refl
  insert-adds-in-front {x} {y ∷ ys} allX with dec-eq x y
  insert-adds-in-front {x} {y ∷ xs} ((x≤y , x≠y) ∷ allY) | yes x=y = ⊥-elim (x≠y x=y)
  insert-adds-in-front {x} {y ∷ ys} allX | no ¬x=y with dec-ord x y
  insert-adds-in-front {x} {y ∷ ys} allX | no ¬x=y | yes x≤y = refl
  insert-adds-in-front {x} {y ∷ xs} ((x≤y , x≠y) ∷ allY) | no ¬x=y | no ¬x≤y = ⊥-elim (¬x≤y x≤y)

abstract
  insert-commute : {x y : A} {xs : List A} → ¬ (x == y) → insert x (insert y xs) ≡ insert y (insert x xs)
  insert-commute {x} {y} {[]} x≠y with dec-eq x y
  insert-commute {x} {y} {[]} x≠y | yes x=y = ⊥-elim (x≠y x=y)
  insert-commute {x} {y} {[]} x≠y | no ¬x=y with dec-ord x y
  insert-commute {x} {y} {[]} x≠y | no ¬x=y | yes x≤y with dec-eq y x
  insert-commute {x} {y} {[]} x≠y | no ¬x=y | yes x≤y | yes y=x = ⊥-elim (x≠y (sym-eq y=x))
  insert-commute {x} {y} {[]} x≠y | no ¬x=y | yes x≤y | no ¬y=x with dec-ord y x
  insert-commute {x} {y} {[]} x≠y | no ¬x=y | yes x≤y | no ¬y=x | yes y≤x = ⊥-elim (x≠y (antisym-ord x≤y y≤x))
  insert-commute {x} {y} {[]} x≠y | no ¬x=y | yes x≤y | no ¬y=x | no ¬y≤x = refl
  insert-commute {x} {y} {[]} x≠y | no ¬x=y | no ¬x≤y with dec-eq y x
  insert-commute {x} {y} {[]} x≠y | no ¬x=y | no ¬x≤y | yes y=x = ⊥-elim (x≠y (sym-eq y=x))
  insert-commute {x} {y} {[]} x≠y | no ¬x=y | no ¬x≤y | no ¬y=x with dec-ord y x
  insert-commute {x} {y} {[]} x≠y | no ¬x=y | no ¬x≤y | no ¬y=x | yes y≤x = refl
  insert-commute {x} {y} {[]} x≠y | no ¬x=y | no ¬x≤y | no ¬y=x | no ¬y≤x = ⊥-elim (total-contr ¬x≤y ¬y≤x)
  insert-commute {x} {y} {z ∷ zs} x≠y with dec-eq y z | dec-eq x z 
  insert-commute {x} {y} {z ∷ zs} x≠y | yes y=z | yes x=z = ⊥-elim (x≠y (trans-eq x=z (sym-eq y=z)))
  insert-commute {x} {y} {z ∷ zs} x≠y | yes y=z | no ¬x=z with dec-eq x y
  insert-commute {x} {y} {z ∷ zs} x≠y | yes y=z | no ¬x=z | yes x=y = ⊥-elim (x≠y x=y)
  insert-commute {x} {y} {z ∷ zs} x≠y | yes y=z | no ¬x=z | no ¬x=y with dec-ord x y | dec-ord x z
  insert-commute {x} {y} {z ∷ zs} x≠y | yes y=z | no ¬x=z | no ¬x=y | yes x≤y | yes x≤z with dec-eq y x
  insert-commute {x} {y} {z ∷ zs} x≠y | yes y=z | no ¬x=z | no ¬x=y | yes x≤y | yes x≤z | yes y=x = ⊥-elim (x≠y (sym-eq y=x))
  insert-commute {x} {y} {z ∷ zs} x≠y | yes y=z | no ¬x=z | no ¬x=y | yes x≤y | yes x≤z | no ¬y=x with dec-ord y x
  insert-commute {x} {y} {z ∷ zs} x≠y | yes y=z | no ¬x=z | no ¬x=y | yes x≤y | yes x≤z | no ¬y=x | yes y≤x = ⊥-elim (x≠y (antisym-ord x≤y y≤x))
  insert-commute {x} {y} {z ∷ zs} x≠y | yes y=z | no ¬x=z | no ¬x=y | yes x≤y | yes x≤z | no ¬y=x | no ¬y≤x with dec-eq y z
  insert-commute {x} {y} {z ∷ zs} x≠y | yes y=z | no ¬x=z | no ¬x=y | yes x≤y | yes x≤z | no ¬y=x | no ¬y≤x | yes _ = refl
  insert-commute {x} {y} {z ∷ zs} x≠y | yes y=z | no ¬x=z | no ¬x=y | yes x≤y | yes x≤z | no ¬y=x | no ¬y≤x | no ¬y=z = ⊥-elim (¬y=z y=z)
  insert-commute {x} {y} {z ∷ zs} x≠y | yes y=z | no ¬x=z | no ¬x=y | yes x≤y | no ¬x≤z = ⊥-elim (¬x≤z (trans-ord x≤y (proj₁ (antisym-ord' y=z))))
  insert-commute {x} {y} {z ∷ zs} x≠y | yes y=z | no ¬x=z | no ¬x=y | no ¬x≤y | yes x≤z = ⊥-elim (¬x≤y (ord-eq-comp x≤z (sym-eq y=z)))
  insert-commute {x} {y} {z ∷ zs} x≠y | yes y=z | no ¬x=z | no ¬x=y | no ¬x≤y | no ¬x≤z with dec-eq y z
  insert-commute {x} {y} {z ∷ zs} x≠y | yes y=z | no ¬x=z | no ¬x=y | no ¬x≤y | no ¬x≤z | yes _ = refl
  insert-commute {x} {y} {z ∷ zs} x≠y | yes y=z | no ¬x=z | no ¬x=y | no ¬x≤y | no ¬x≤z | no ¬y=z = ⊥-elim (¬y=z y=z)
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | yes x=z with dec-eq y x
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | yes x=z | yes y=x = ⊥-elim (x≠y (sym-eq y=x))
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | yes x=z | no ¬y=x with dec-ord y z | dec-ord y x
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | yes x=z | no ¬y=x | yes y≤z | yes y≤x with dec-eq x y
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | yes x=z | no ¬y=x | yes y≤z | yes y≤x | yes x=y = ⊥-elim (x≠y x=y)
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | yes x=z | no ¬y=x | yes y≤z | yes y≤x | no ¬x=y with dec-ord x y
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | yes x=z | no ¬y=x | yes y≤z | yes y≤x | no ¬x=y | yes x≤y = ⊥-elim (x≠y (antisym-ord x≤y y≤x))
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | yes x=z | no ¬y=x | yes y≤z | yes y≤x | no ¬x=y | no ¬x≤y with dec-eq x z
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | yes x=z | no ¬y=x | yes y≤z | yes y≤x | no ¬x=y | no ¬x≤y | yes _ with dec-ord x z
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | yes x=z | no ¬y=x | yes y≤z | yes y≤x | no ¬x=y | no ¬x≤y | yes _ | yes x≤z = refl
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | yes x=z | no ¬y=x | yes y≤z | yes y≤x | no ¬x=y | no ¬x≤y | yes _ | no ¬x≤z = refl
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | yes x=z | no ¬y=x | yes y≤z | yes y≤x | no ¬x=y | no ¬x≤y | no ¬x=z = ⊥-elim (¬x=z x=z)
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | yes x=z | no ¬y=x | yes y≤z | no ¬y≤x = ⊥-elim (¬y≤x (ord-eq-comp y≤z (sym-eq x=z)))
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | yes x=z | no ¬y=x | no ¬y≤z | yes y≤x = ⊥-elim (¬y≤z (ord-eq-comp y≤x x=z))
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | yes x=z | no ¬y=x | no ¬y≤z | no ¬y≤x with dec-eq x z
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | yes x=z | no ¬y=x | no ¬y≤z | no ¬y≤x | yes _ = refl
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | yes x=z | no ¬y=x | no ¬y≤z | no ¬y≤x | no ¬x=z = ⊥-elim (¬x=z x=z)
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z with dec-ord y z | dec-ord x z
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | yes y≤z | yes x≤z with dec-eq x y
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | yes y≤z | yes x≤z | yes x=y = ⊥-elim (x≠y x=y)
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | yes y≤z | yes x≤z | no ¬x=y with dec-eq y x
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | yes y≤z | yes x≤z | no ¬x=y | yes y=x = ⊥-elim (¬x=y (sym-eq y=x))
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | yes y≤z | yes x≤z | no ¬x=y | no ¬y=x with dec-ord x y | dec-ord y x
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | yes y≤z | yes x≤z | no ¬x=y | no ¬y=x | yes x≤y | yes y≤x = ⊥-elim (¬x=y (antisym-ord x≤y y≤x))
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | yes y≤z | yes x≤z | no ¬x=y | no ¬y=x | yes x≤y | no ¬y≤x with dec-eq y z
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | yes y≤z | yes x≤z | no ¬x=y | no ¬y=x | yes x≤y | no ¬y≤x | yes y=z = ⊥-elim (¬y=z y=z)
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | yes y≤z | yes x≤z | no ¬x=y | no ¬y=x | yes x≤y | no ¬y≤x | no _ with dec-ord y z 
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | yes y≤z | yes x≤z | no ¬x=y | no ¬y=x | yes x≤y | no ¬y≤x | no _ | yes _ = refl
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | yes y≤z | yes x≤z | no ¬x=y | no ¬y=x | yes x≤y | no ¬y≤x | no _ | no ¬y≤z = ⊥-elim (¬y≤z y≤z)
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | yes y≤z | yes x≤z | no ¬x=y | no ¬y=x | no ¬x≤y | yes y≤x with dec-eq x z
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | yes y≤z | yes x≤z | no ¬x=y | no ¬y=x | no ¬x≤y | yes y≤x | yes x=z = ⊥-elim (¬x=z x=z)
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | yes y≤z | yes x≤z | no ¬x=y | no ¬y=x | no ¬x≤y | yes y≤x | no _ with dec-ord x z 
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | yes y≤z | yes x≤z | no ¬x=y | no ¬y=x | no ¬x≤y | yes y≤x | no _ | yes _ = refl
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | yes y≤z | yes x≤z | no ¬x=y | no ¬y=x | no ¬x≤y | yes y≤x | no _ | no ¬x≤z = ⊥-elim (¬x≤z x≤z)
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | yes y≤z | yes x≤z | no ¬x=y | no ¬y=x | no ¬x≤y | no ¬y≤x = ⊥-elim (total-contr ¬x≤y ¬y≤x)
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | yes y≤z | no ¬x≤z with dec-eq x y
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | yes y≤z | no ¬x≤z | yes x=y = ⊥-elim (x≠y x=y)
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | yes y≤z | no ¬x≤z | no ¬x=y with dec-eq y x
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | yes y≤z | no ¬x≤z | no ¬x=y | yes y=x = ⊥-elim (¬x=y (sym-eq y=x))
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | yes y≤z | no ¬x≤z | no ¬x=y | no ¬y=x with dec-ord x y | dec-ord y x
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | yes y≤z | no ¬x≤z | no ¬x=y | no ¬y=x | yes x≤y | yes y≤x = ⊥-elim (¬x=y (antisym-ord x≤y y≤x))
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | yes y≤z | no ¬x≤z | no ¬x=y | no ¬y=x | yes x≤y | no ¬y≤x = ⊥-elim (excluded-middle-ord' ¬y=z y≤z (trans-ord (excluded-middle-ord ¬x≤z) x≤y))
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | yes y≤z | no ¬x≤z | no ¬x=y | no ¬y=x | no ¬x≤y | yes y≤x with dec-eq x z
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | yes y≤z | no ¬x≤z | no ¬x=y | no ¬y=x | no ¬x≤y | yes y≤x | yes x=z = ⊥-elim (¬x=z x=z)
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | yes y≤z | no ¬x≤z | no ¬x=y | no ¬y=x | no ¬x≤y | yes y≤x | no _ with dec-ord x z
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | yes y≤z | no ¬x≤z | no ¬x=y | no ¬y=x | no ¬x≤y | yes y≤x | no _ | yes x≤z = ⊥-elim (¬x≤z x≤z)
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | yes y≤z | no ¬x≤z | no ¬x=y | no ¬y=x | no ¬x≤y | yes y≤x | no _ | no _ with dec-ord y z
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | yes y≤z | no ¬x≤z | no ¬x=y | no ¬y=x | no ¬x≤y | yes y≤x | no _ | no _ | yes _ with dec-eq y z
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | yes y≤z | no ¬x≤z | no ¬x=y | no ¬y=x | no ¬x≤y | yes y≤x | no _ | no _ | yes _ | yes y=z = ⊥-elim (¬y=z y=z)
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | yes y≤z | no ¬x≤z | no ¬x=y | no ¬y=x | no ¬x≤y | yes y≤x | no _ | no _ | yes _ | no _ with dec-ord y z
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | yes y≤z | no ¬x≤z | no ¬x=y | no ¬y=x | no ¬x≤y | yes y≤x | no _ | no _ | yes _ | no _ | yes _ = refl
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | yes y≤z | no ¬x≤z | no ¬x=y | no ¬y=x | no ¬x≤y | yes y≤x | no _ | no _ | yes _ | no _ | no ¬y≤z = ⊥-elim (¬y≤z y≤z)
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | yes y≤z | no ¬x≤z | no ¬x=y | no ¬y=x | no ¬x≤y | yes y≤x | no _ | no _ | no ¬y≤z = ⊥-elim (¬y≤z y≤z)
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | yes y≤z | no ¬x≤z | no ¬x=y | no ¬y=x | no ¬x≤y | no ¬y≤x = ⊥-elim (total-contr ¬x≤y ¬y≤x)
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | no ¬y≤z | yes x≤z with dec-eq x y
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | no ¬y≤z | yes x≤z | yes x=y = ⊥-elim (x≠y x=y)
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | no ¬y≤z | yes x≤z | no ¬x=y with dec-eq y x
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | no ¬y≤z | yes x≤z | no ¬x=y | yes y=x = ⊥-elim (¬x=y (sym-eq y=x))
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | no ¬y≤z | yes x≤z | no ¬x=y | no ¬y=x with dec-ord x y | dec-ord y x
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | no ¬y≤z | yes x≤z | no ¬x=y | no ¬y=x | yes x≤y | yes y≤x = ⊥-elim (¬x=y (antisym-ord x≤y y≤x))
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | no ¬y≤z | yes x≤z | no ¬x=y | no ¬y=x | yes x≤y | no ¬y≤x with dec-eq y z
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | no ¬y≤z | yes x≤z | no ¬x=y | no ¬y=x | yes x≤y | no ¬y≤x | yes y=z = ⊥-elim (¬y=z y=z)
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | no ¬y≤z | yes x≤z | no ¬x=y | no ¬y=x | yes x≤y | no ¬y≤x | no _ with dec-ord y z 
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | no ¬y≤z | yes x≤z | no ¬x=y | no ¬y=x | yes x≤y | no ¬y≤x | no _ | yes y≤z = ⊥-elim (¬y≤z y≤z)
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | no ¬y≤z | yes x≤z | no ¬x=y | no ¬y=x | yes x≤y | no ¬y≤x | no _ | no _ with dec-eq x z
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | no ¬y≤z | yes x≤z | no ¬x=y | no ¬y=x | yes x≤y | no ¬y≤x | no _ | no _ | yes x=z = ⊥-elim (¬x=z x=z)
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | no ¬y≤z | yes x≤z | no ¬x=y | no ¬y=x | yes x≤y | no ¬y≤x | no _ | no _ | no _ with dec-ord x z
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | no ¬y≤z | yes x≤z | no ¬x=y | no ¬y=x | yes x≤y | no ¬y≤x | no _ | no _ | no _ | yes _ = refl
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | no ¬y≤z | yes x≤z | no ¬x=y | no ¬y=x | yes x≤y | no ¬y≤x | no _ | no _ | no _ | no ¬x≤z = ⊥-elim (¬x≤z x≤z)
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | no ¬y≤z | yes x≤z | no ¬x=y | no ¬y=x | no ¬x≤y | yes y≤x = ⊥-elim (¬x≤y (trans-ord x≤z (excluded-middle-ord ¬y≤z)))
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | no ¬y≤z | yes x≤z | no ¬x=y | no ¬y=x | no ¬x≤y | no ¬y≤x = ⊥-elim (total-contr ¬x≤y ¬y≤x)
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | no ¬y≤z | no ¬x≤z with dec-eq x y
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | no ¬y≤z | no ¬x≤z | yes x=y = ⊥-elim (x≠y x=y)
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | no ¬y≤z | no ¬x≤z | no ¬x=y with dec-eq y x
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | no ¬y≤z | no ¬x≤z | no ¬x=y | yes y=x = ⊥-elim (¬x=y (sym-eq y=x))
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | no ¬y≤z | no ¬x≤z | no ¬x=y | no ¬y=x with dec-ord x y | dec-ord y x
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | no ¬y≤z | no ¬x≤z | no ¬x=y | no ¬y=x | yes x≤y | yes y≤x = ⊥-elim (¬x=y (antisym-ord x≤y y≤x))
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | no ¬y≤z | no ¬x≤z | no ¬x=y | no ¬y=x | yes x≤y | no ¬y≤x with dec-eq y z
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | no ¬y≤z | no ¬x≤z | no ¬x=y | no ¬y=x | yes x≤y | no ¬y≤x | yes y=z = ⊥-elim (¬y=z y=z)
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | no ¬y≤z | no ¬x≤z | no ¬x=y | no ¬y=x | yes x≤y | no ¬y≤x | no _ with dec-ord y z 
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | no ¬y≤z | no ¬x≤z | no ¬x=y | no ¬y=x | yes x≤y | no ¬y≤x | no _ | yes y≤z = ⊥-elim (¬y≤z y≤z)
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | no ¬y≤z | no ¬x≤z | no ¬x=y | no ¬y=x | yes x≤y | no ¬y≤x | no _ | no _ with dec-eq x z
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | no ¬y≤z | no ¬x≤z | no ¬x=y | no ¬y=x | yes x≤y | no ¬y≤x | no _ | no _ | yes x=z = ⊥-elim (¬x=z x=z)
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | no ¬y≤z | no ¬x≤z | no ¬x=y | no ¬y=x | yes x≤y | no ¬y≤x | no _ | no _ | no _ with dec-ord x z
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | no ¬y≤z | no ¬x≤z | no ¬x=y | no ¬y=x | yes x≤y | no ¬y≤x | no _ | no _ | no _ | yes x≤z = ⊥-elim (¬x≤z x≤z)
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | no ¬y≤z | no ¬x≤z | no ¬x=y | no ¬y=x | yes x≤y | no ¬y≤x | no _ | no _ | no _ | no _ = cong (_∷_ z) (insert-commute {x} {y} {zs} x≠y)
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | no ¬y≤z | no ¬x≤z | no ¬x=y | no ¬y=x | no ¬x≤y | yes y≤x with dec-eq x z
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | no ¬y≤z | no ¬x≤z | no ¬x=y | no ¬y=x | no ¬x≤y | yes y≤x | yes x=z = ⊥-elim (¬x=z x=z)
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | no ¬y≤z | no ¬x≤z | no ¬x=y | no ¬y=x | no ¬x≤y | yes y≤x | no _ with dec-eq y z
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | no ¬y≤z | no ¬x≤z | no ¬x=y | no ¬y=x | no ¬x≤y | yes y≤x | no _ | yes y=z = ⊥-elim (¬y=z y=z)
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | no ¬y≤z | no ¬x≤z | no ¬x=y | no ¬y=x | no ¬x≤y | yes y≤x | no _ | no _ with dec-ord y z
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | no ¬y≤z | no ¬x≤z | no ¬x=y | no ¬y=x | no ¬x≤y | yes y≤x | no _ | no _ | yes y≤z = ⊥-elim (¬y≤z y≤z)
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | no ¬y≤z | no ¬x≤z | no ¬x=y | no ¬y=x | no ¬x≤y | yes y≤x | no _ | no _ | no _ with dec-ord x z
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | no ¬y≤z | no ¬x≤z | no ¬x=y | no ¬y=x | no ¬x≤y | yes y≤x | no _ | no _ | no _ | yes x≤z = ⊥-elim (¬x≤z x≤z)
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | no ¬y≤z | no ¬x≤z | no ¬x=y | no ¬y=x | no ¬x≤y | yes y≤x | no _ | no _ | no _ | no _ = cong (_∷_ z) (insert-commute {x} {y} {zs} x≠y)
  insert-commute {x} {y} {z ∷ zs} x≠y | no ¬y=z | no ¬x=z | no ¬y≤z | no ¬x≤z | no ¬x=y | no ¬y=x | no ¬x≤y | no ¬y≤x = ⊥-elim (total-contr ¬x≤y ¬y≤x)

abstract
  insert-elim : {x y : A} {zs : List A} → x == y → insert x (insert y zs) ≡ insert x zs
  insert-elim {x} {y} {[]} x=y with dec-eq x y
  insert-elim {x} {y} {[]} x=y | yes _ = refl
  insert-elim {x} {y} {[]} x=y | no ¬x=y = ⊥-elim (¬x=y x=y)
  insert-elim {x} {y} {z ∷ zs} x=y with dec-eq y z | dec-eq x z
  insert-elim {x} {y} {z ∷ zs} x=y | yes y=z | yes x=z with dec-eq x y
  insert-elim {x} {y} {z ∷ zs} x=y | yes y=z | yes x=z | yes _ = refl
  insert-elim {x} {y} {z ∷ zs} x=y | yes y=z | yes x=z | no ¬x=y = ⊥-elim (¬x=y x=y)
  insert-elim {x} {y} {z ∷ zs} x=y | yes y=z | no ¬x=z = ⊥-elim (¬x=z (trans-eq x=y y=z))
  insert-elim {x} {y} {z ∷ zs} x=y | no ¬y=z | yes x=z = ⊥-elim (¬y=z (trans-eq (sym-eq x=y) x=z))
  insert-elim {x} {y} {z ∷ zs} x=y | no ¬y=z | no ¬x=z with dec-ord y z | dec-ord x z
  insert-elim {x} {y} {z ∷ zs} x=y | no ¬y=z | no ¬x=z | yes y≤z | yes x≤z with dec-eq x y
  insert-elim {x} {y} {z ∷ zs} x=y | no ¬y=z | no ¬x=z | yes y≤z | yes x≤z | yes _ = refl
  insert-elim {x} {y} {z ∷ zs} x=y | no ¬y=z | no ¬x=z | yes y≤z | yes x≤z | no ¬x=y = ⊥-elim (¬x=y x=y)
  insert-elim {x} {y} {z ∷ zs} x=y | no ¬y=z | no ¬x=z | yes y≤z | no ¬x≤z = ⊥-elim (¬x≤z (eq-ord-comp x=y y≤z))
  insert-elim {x} {y} {z ∷ zs} x=y | no ¬y=z | no ¬x=z | no ¬y≤z | yes x≤z = ⊥-elim (¬y≤z (eq-ord-comp (sym-eq x=y) x≤z))
  insert-elim {x} {y} {z ∷ zs} x=y | no ¬y=z | no ¬x=z | no ¬y≤z | no ¬x≤z with dec-eq x y
  insert-elim {x} {y} {z ∷ zs} x=y | no ¬y=z | no ¬x=z | no ¬y≤z | no ¬x≤z | yes _ with dec-eq x z
  insert-elim {x} {y} {z ∷ zs} x=y | no ¬y=z | no ¬x=z | no ¬y≤z | no ¬x≤z | yes _ | yes x=z = ⊥-elim (¬x=z x=z)
  insert-elim {x} {y} {z ∷ zs} x=y | no ¬y=z | no ¬x=z | no ¬y≤z | no ¬x≤z | yes _ | no _ with dec-ord x z
  insert-elim {x} {y} {z ∷ zs} x=y | no ¬y=z | no ¬x=z | no ¬y≤z | no ¬x≤z | yes _ | no _ | yes x≤z = ⊥-elim (¬x≤z x≤z)
  insert-elim {x} {y} {z ∷ zs} x=y | no ¬y=z | no ¬x=z | no ¬y≤z | no ¬x≤z | yes _ | no _ | no _ = cong (_∷_ z) (insert-elim {zs = zs} x=y)
  insert-elim {x} {y} {z ∷ zs} x=y | no ¬y=z | no ¬x=z | no ¬y≤z | no ¬x≤z | no ¬x=y = ⊥-elim (¬x=y x=y)

abstract
  insert-elim' : {x y : A} {zs : List A} → IsStructuralEquality EqA → x == y → insert y (insert x zs) ≡ insert x zs
  insert-elim' {x} {y} {[]} sEq x=y with dec-eq x y
  insert-elim' {x} {y} {[]} sEq x=y | yes _ with dec-eq y x 
  insert-elim' {x} {y} {[]} sEq x=y | yes _ | yes y=x = cong (λ X → X ∷ []) (sym (sEq x y x=y))
  insert-elim' {x} {y} {[]} sEq x=y | yes _ | no ¬y=x = ⊥-elim (¬y=x (sym-eq x=y))
  insert-elim' {x} {y} {[]} sEq x=y | no ¬x=y = ⊥-elim (¬x=y x=y)
  insert-elim' {x} {y} {z ∷ zs} sEq x=y with dec-eq y z | dec-eq x z
  insert-elim' {x} {y} {z ∷ zs} sEq x=y | yes y=z | yes x=z with dec-eq x y
  insert-elim' {x} {y} {z ∷ zs} sEq x=y | yes y=z | yes x=z | yes _ with dec-eq y x
  insert-elim' {x} {y} {z ∷ zs} sEq x=y | yes y=z | yes x=z | yes _ | yes y=x = cong (λ X → X ∷ zs) (sym (sEq x y x=y))
  insert-elim' {x} {y} {z ∷ zs} sEq x=y | yes y=z | yes x=z | yes _ | no ¬y=x = ⊥-elim (¬y=x (sym-eq x=y))
  insert-elim' {x} {y} {z ∷ zs} sEq x=y | yes y=z | yes x=z | no ¬x=y = ⊥-elim (¬x=y x=y)
  insert-elim' {x} {y} {z ∷ zs} sEq x=y | yes y=z | no ¬x=z = ⊥-elim (¬x=z (trans-eq x=y y=z))
  insert-elim' {x} {y} {z ∷ zs} sEq x=y | no ¬y=z | yes x=z = ⊥-elim (¬y=z (trans-eq (sym-eq x=y) x=z))
  insert-elim' {x} {y} {z ∷ zs} sEq x=y | no ¬y=z | no ¬x=z with dec-ord y z | dec-ord x z
  insert-elim' {x} {y} {z ∷ zs} sEq x=y | no ¬y=z | no ¬x=z | yes y≤z | yes x≤z with dec-eq x y
  insert-elim' {x} {y} {z ∷ zs} sEq x=y | no ¬y=z | no ¬x=z | yes y≤z | yes x≤z | yes _ with dec-eq y x
  insert-elim' {x} {y} {z ∷ zs} sEq x=y | no ¬y=z | no ¬x=z | yes y≤z | yes x≤z | yes _ | yes y=x = cong (λ X → X ∷ z ∷ zs) (sym (sEq x y x=y))
  insert-elim' {x} {y} {z ∷ zs} sEq x=y | no ¬y=z | no ¬x=z | yes y≤z | yes x≤z | yes _ | no ¬y=x = ⊥-elim (¬y=x (sym-eq x=y))
  insert-elim' {x} {y} {z ∷ zs} sEq x=y | no ¬y=z | no ¬x=z | yes y≤z | yes x≤z | no ¬x=y = ⊥-elim (¬x=y x=y)
  insert-elim' {x} {y} {z ∷ zs} sEq x=y | no ¬y=z | no ¬x=z | yes y≤z | no ¬x≤z = ⊥-elim (¬x≤z (eq-ord-comp x=y y≤z))
  insert-elim' {x} {y} {z ∷ zs} sEq x=y | no ¬y=z | no ¬x=z | no ¬y≤z | yes x≤z = ⊥-elim (¬y≤z (eq-ord-comp (sym-eq x=y) x≤z))
  insert-elim' {x} {y} {z ∷ zs} sEq x=y | no ¬y=z | no ¬x=z | no ¬y≤z | no ¬x≤z with dec-eq x y
  insert-elim' {x} {y} {z ∷ zs} sEq x=y | no ¬y=z | no ¬x=z | no ¬y≤z | no ¬x≤z | yes _ with dec-eq x z
  insert-elim' {x} {y} {z ∷ zs} sEq x=y | no ¬y=z | no ¬x=z | no ¬y≤z | no ¬x≤z | yes _ | yes x=z = ⊥-elim (¬x=z x=z)
  insert-elim' {x} {y} {z ∷ zs} sEq x=y | no ¬y=z | no ¬x=z | no ¬y≤z | no ¬x≤z | yes _ | no _ with dec-ord x z
  insert-elim' {x} {y} {z ∷ zs} sEq x=y | no ¬y=z | no ¬x=z | no ¬y≤z | no ¬x≤z | yes _ | no _ | yes x≤z = ⊥-elim (¬x≤z x≤z)
  insert-elim' {x} {y} {z ∷ zs} sEq x=y | no ¬y=z | no ¬x=z | no ¬y≤z | no ¬x≤z | yes _ | no _ | no _ with dec-eq y x
  insert-elim' {x} {y} {z ∷ zs} sEq x=y | no ¬y=z | no ¬x=z | no ¬y≤z | no ¬x≤z | yes _ | no _ | no _ | yes y=x with dec-eq y z
  insert-elim' {x} {y} {z ∷ zs} sEq x=y | no ¬y=z | no ¬x=z | no ¬y≤z | no ¬x≤z | yes _ | no _ | no _ | yes y=x | yes y=z = ⊥-elim (¬y=z y=z)
  insert-elim' {x} {y} {z ∷ zs} sEq x=y | no ¬y=z | no ¬x=z | no ¬y≤z | no ¬x≤z | yes _ | no _ | no _ | yes y=x | no _ with dec-ord y z 
  insert-elim' {x} {y} {z ∷ zs} sEq x=y | no ¬y=z | no ¬x=z | no ¬y≤z | no ¬x≤z | yes _ | no _ | no _ | yes y=x | no _ | yes y≤z = ⊥-elim (¬y≤z y≤z)
  insert-elim' {x} {y} {z ∷ zs} sEq x=y | no ¬y=z | no ¬x=z | no ¬y≤z | no ¬x≤z | yes _ | no _ | no _ | yes y=x | no _ | no _ = cong (_∷_ z) (insert-elim' {zs = zs} sEq x=y)
  insert-elim' {x} {y} {z ∷ zs} sEq x=y | no ¬y=z | no ¬x=z | no ¬y≤z | no ¬x≤z | yes _ | no _ | no _ | no ¬y=x = ⊥-elim (¬y=x (sym-eq x=y)) -- 
  insert-elim' {x} {y} {z ∷ zs} sEq x=y | no ¬y=z | no ¬x=z | no ¬y≤z | no ¬x≤z | no ¬x=y = ⊥-elim (¬x=y x=y)


insertSet : (a : A) → LSet (A , OrdA) → LSet (A , OrdA)
insertSet a (lset xs sorted) = lset (insert a xs) (insert-preserves-IsSortedNoDupList sorted)

abstract
  insertSet-adds-in-front : (x : A) (xs : List A) (sorted : IsSortedNoDupList OrdA (x ∷ xs)) → insertSet x (lset xs (proj₂ sorted)) ≡ lset (x ∷ xs) sorted
  insertSet-adds-in-front x xs (sortedX , sortedXs) = lset-eq (insert x xs) (x ∷ xs) (insert-preserves-IsSortedNoDupList sortedXs) (sortedX , sortedXs) (insert-adds-in-front sortedX)

abstract
  insertSet-commute' : (x y : A) → (xs : LSet (A , OrdA)) → ¬ (x == y) → insertSet x (insertSet y xs) ≡ insertSet y (insertSet x xs)
  insertSet-commute' x y (lset xs sortedXs) ¬x==y = lset-eq (insert x (insert y xs)) (insert y (insert x xs)) 
                                                            (insert-preserves-IsSortedNoDupList (insert-preserves-IsSortedNoDupList sortedXs)) 
                                                            (insert-preserves-IsSortedNoDupList (insert-preserves-IsSortedNoDupList sortedXs)) 
                                                            (insert-commute {xs = xs} ¬x==y)

abstract
  insertSet-elim : (x y : A) → (xs : LSet (A , OrdA)) → x == y → insertSet x (insertSet y xs) ≡ insertSet x xs
  insertSet-elim x y (lset xs sortedXs) x==y = lset-eq (insert x (insert y xs)) (insert x xs) 
                                                       (insert-preserves-IsSortedNoDupList (insert-preserves-IsSortedNoDupList sortedXs)) 
                                                       (insert-preserves-IsSortedNoDupList sortedXs) 
                                                       (insert-elim {x = x} {y = y} {zs = xs} x==y) 

abstract
  insertSet-elim' : (x y : A) (xs : LSet (A , OrdA)) → IsStructuralEquality EqA → x == y → insertSet y (insertSet x xs) ≡ insertSet x xs
  insertSet-elim' x z (lset xs sortedXs) sEq x==z = lset-eq (insert z (insert x xs)) (insert x xs)
                                                            (insert-preserves-IsSortedNoDupList (insert-preserves-IsSortedNoDupList sortedXs))
                                                            (insert-preserves-IsSortedNoDupList sortedXs) 
                                                            (insert-elim' {x = x} {y = z} {zs = xs} sEq x==z)
abstract
  insertSet-commute : (x y : A) → (xs : LSet (A , OrdA)) → IsStructuralEquality EqA → insertSet x (insertSet y xs) ≡ insertSet y (insertSet x xs)
  insertSet-commute x y xs sEq with dec-eq x y
  insertSet-commute x y xs sEq | yes x=y = begin
    insertSet x (insertSet y xs) 
      ≡⟨ insertSet-elim x y xs x=y ⟩
    insertSet x xs
      ≡⟨ sym (insertSet-elim' x y xs sEq x=y) ⟩
    insertSet y (insertSet x xs) ∎
  insertSet-commute x y xs sEq | no ¬x=y = insertSet-commute' x y xs ¬x=y
