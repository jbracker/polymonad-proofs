
module Theory.Examples.Haskell.FunctorSet.Sort where 

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

open import Haskell
open import ProofIrrelevance 

open import Theory.Examples.Haskell.FunctorSet.Base


insert : {ℓEq ℓOrd : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} {ℓOrd} A) → A → List A → List A
insert OrdA x [] = x ∷ []
insert OrdA x (y ∷ ys) with OrdInstance.dec-ord OrdA x y
insert OrdA x (y ∷ ys) | yes x≤y = x ∷ y ∷ ys
insert OrdA x (y ∷ ys) | no ¬x≤y = y ∷ insert OrdA x ys

private
  insert-preserves-sorted' : {ℓEq : Level }{A : Type}
                           → (OrdA : OrdInstance {ℓEq} A)
                           → (x z : A) → (xs : List A)
                           → IsSortedList OrdA (x ∷ xs)
                           → (IsSortedList OrdA (x ∷ insert OrdA z xs)) 
                           ⊎ (IsSortedList OrdA (z ∷ x ∷ xs))
  insert-preserves-sorted' OrdA x z [] tt with OrdInstance.dec-ord OrdA x z 
  insert-preserves-sorted' OrdA x z [] tt | yes x≤z = inj₁ $ x≤z , tt
  insert-preserves-sorted' OrdA x z [] tt | no ¬x≤z with OrdInstance.total OrdA x z
  insert-preserves-sorted' OrdA x z [] tt | no ¬x≤z | inj₁ x≤z = ⊥-elim (¬x≤z x≤z)
  insert-preserves-sorted' OrdA x z [] tt | no ¬x≤z | inj₂ z≤x = inj₂ $ z≤x , tt
  insert-preserves-sorted' OrdA x z (y ∷ xs) (x≤y , sorted[y∷xs]) with OrdInstance.dec-ord OrdA x z
  insert-preserves-sorted' OrdA x z (y ∷ xs) (x≤y , sorted[y∷xs]) | yes x≤z with OrdInstance.dec-ord OrdA z y
  insert-preserves-sorted' OrdA x z (y ∷ xs) (x≤y , sorted[y∷xs]) | yes x≤z | yes z≤y = inj₁ $ x≤z , z≤y , sorted[y∷xs]
  insert-preserves-sorted' OrdA x z (y ∷ xs) (x≤y , sorted[y∷xs]) | yes x≤z | no ¬z≤y with insert-preserves-sorted' OrdA y z xs sorted[y∷xs]
  insert-preserves-sorted' OrdA x z (y ∷ xs) (x≤y , sorted[y∷xs]) | yes x≤z | no ¬z≤y | inj₁ p = inj₁ $ x≤y , p
  insert-preserves-sorted' OrdA x z (y ∷ xs) (x≤y , sorted[y∷xs]) | yes x≤z | no ¬z≤y | inj₂ (z≤y , _) = ⊥-elim (¬z≤y z≤y)
  insert-preserves-sorted' OrdA x z (y ∷ xs) (x≤y , sorted[y∷xs]) | no ¬x≤z with OrdInstance.total OrdA x z
  insert-preserves-sorted' OrdA x z (y ∷ xs) (x≤y , sorted[y∷xs]) | no ¬x≤z | inj₁ x≤z = ⊥-elim (¬x≤z x≤z)
  insert-preserves-sorted' OrdA x z (y ∷ xs) (x≤y , sorted[y∷xs]) | no ¬x≤z | inj₂ z≤x = inj₂ $ z≤x , x≤y , sorted[y∷xs]

insert-preserves-sorted : {ℓEq : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} A) → (x : A) → (xs : List A) → IsSortedList OrdA xs → IsSortedList OrdA (insert OrdA x xs)
insert-preserves-sorted OrdA x [] tt = tt
insert-preserves-sorted OrdA x (y ∷ []) tt with OrdInstance.dec-ord OrdA x y 
insert-preserves-sorted OrdA x (y ∷ []) tt | yes x≤y = x≤y , tt
insert-preserves-sorted OrdA x (y ∷ []) tt | no ¬x≤y with OrdInstance.total OrdA y x
insert-preserves-sorted OrdA x (y ∷ []) tt | no ¬x≤y | inj₁ y≤x = y≤x , tt
insert-preserves-sorted OrdA x (y ∷ []) tt | no ¬x≤y | inj₂ x≤y = ⊥-elim (¬x≤y x≤y)
insert-preserves-sorted OrdA x (y ∷ z ∷ xs) (y≤z , sorted[z∷xs]) with OrdInstance.dec-ord OrdA x y
insert-preserves-sorted OrdA x (y ∷ z ∷ xs) (y≤z , sorted[z∷xs]) | yes x≤y = x≤y , y≤z , sorted[z∷xs]
insert-preserves-sorted OrdA x (y ∷ z ∷ xs) (y≤z , sorted[z∷xs]) | no ¬x≤y with OrdInstance.total OrdA x y
insert-preserves-sorted OrdA x (y ∷ z ∷ xs) (y≤z , sorted[z∷xs]) | no ¬x≤y | inj₁ x≤y = ⊥-elim (¬x≤y x≤y)
insert-preserves-sorted OrdA x (y ∷ z ∷ xs) (y≤z , sorted[z∷xs]) | no ¬x≤y | inj₂ y≤x with OrdInstance.dec-ord OrdA x z
insert-preserves-sorted OrdA x (y ∷ z ∷ xs) (y≤z , sorted[z∷xs]) | no ¬x≤y | inj₂ y≤x | yes x≤z = y≤x , x≤z , sorted[z∷xs]
insert-preserves-sorted OrdA x (y ∷ z ∷ xs) (y≤z , sorted[z∷xs]) | no ¬x≤y | inj₂ y≤x | no ¬x≤z with insert-preserves-sorted' OrdA z x xs sorted[z∷xs]
insert-preserves-sorted OrdA x (y ∷ z ∷ xs) (y≤z , sorted[z∷xs]) | no ¬x≤y | inj₂ y≤x | no ¬x≤z | inj₁ p = y≤z , p
insert-preserves-sorted OrdA x (y ∷ z ∷ xs) (y≤z , sorted[z∷xs]) | no ¬x≤y | inj₂ y≤x | no ¬x≤z | inj₂ (x≤z , _) = ⊥-elim (¬x≤z x≤z) 

sort : {ℓEq ℓOrd : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} {ℓOrd} A) → List A → List A
sort OrdA [] = []
sort OrdA (x ∷ xs) = insert OrdA x (sort OrdA xs)

sort-produces-sorted : {ℓEq : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} A) → (xs : List A) → IsSortedList OrdA (sort OrdA xs)
sort-produces-sorted OrdA [] = tt
sort-produces-sorted OrdA (x ∷ []) = tt
sort-produces-sorted OrdA (x ∷ y ∷ xs) = insert-preserves-sorted OrdA x (insert OrdA y (sort OrdA xs))
                                       ( insert-preserves-sorted OrdA y (sort OrdA xs) (sort-produces-sorted OrdA xs))

private
  insert-smaller-in-front : {ℓEq : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} A)
                              → (y x : A) → (xs : List A)
                              → (OrdInstance._≤_ OrdA y x) → IsSortedList OrdA xs
                              → insert OrdA y (x ∷ xs) ≡ y ∷ (x ∷ xs)
  insert-smaller-in-front OrdA y x xs y≤x sorted with OrdInstance.dec-ord OrdA y x
  insert-smaller-in-front OrdA y x xs y≤x sorted | yes y≤x' = refl
  insert-smaller-in-front OrdA y x xs y≤x sorted | no ¬y≤x = ⊥-elim (¬y≤x y≤x)

sort-sorting-sorted : {ℓEq : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} A) → (xs : List A) → IsSortedList OrdA xs → sort OrdA xs ≡ xs
sort-sorting-sorted OrdA [] sorted = refl
sort-sorting-sorted OrdA (y ∷ []) sorted = refl
sort-sorting-sorted OrdA (y ∷ x ∷ xs) (y≤x , sorted) with sort-sorting-sorted OrdA (x ∷ xs) sorted
sort-sorting-sorted OrdA (y ∷ x ∷ xs) (y≤x , sorted) | p =
  trans (cong (insert OrdA y) p) (insert-smaller-in-front OrdA y x xs y≤x (law-IsSortedList-forget-elem OrdA x xs sorted))
