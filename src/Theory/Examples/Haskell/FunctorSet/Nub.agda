
open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Level renaming ( suc to lsuc ; zero to lzero)
open import Data.Unit hiding ( _≤_ ; _≟_ ; total )
open import Data.Empty
open import Data.List renaming ( map to mapList )
open import Data.List.Any hiding ( map )
open import Data.Product hiding ( map )
open import Data.Sum hiding ( map )
open import Relation.Nullary
open import Relation.Binary using ( IsPreorder )
open import Relation.Binary.PropositionalEquality

open import Haskell
open import ProofIrrelevance 

open import Theory.Examples.Haskell.FunctorSet.Base

module Theory.Examples.Haskell.FunctorSet.Nub {ℓEq ℓOrd : Level} {A : Type} (OrdA : OrdInstance {ℓEq} {ℓOrd} A) where

private
  open module LP = ListProperties OrdA
  open OrdInstance OrdA

remove : A → List A → List A
remove y [] = []
remove y (x ∷ xs) with dec-eq y x
remove y (x ∷ xs) | yes y==x = remove y xs
remove y (x ∷ xs) | no ¬y==x = x ∷ remove y xs


remove-produces-missing-elem : (x : A) → (xs : List A) → ¬ (InList x (remove x xs))
remove-produces-missing-elem y [] ()
remove-produces-missing-elem y (x ∷ xs) y∈xs with dec-eq y x
remove-produces-missing-elem y (x ∷ xs) y∈xs | yes y==x = remove-produces-missing-elem y xs y∈xs
remove-produces-missing-elem y (x ∷ xs) (here y==x) | no ¬y==x = ¬y==x y==x
remove-produces-missing-elem y (x ∷ xs) (there y∈xs) | no ¬y==x = remove-produces-missing-elem y xs y∈xs

remove-preserves-existing-elem : (y x : A) → (xs : List A)
                                → InList x (remove y xs) → InList x xs
remove-preserves-existing-elem y x [] ()
remove-preserves-existing-elem y x (z ∷ xs) x∈remxs with dec-eq y z
remove-preserves-existing-elem y x (z ∷ xs) x∈remxs | yes y==z = there (remove-preserves-existing-elem y x xs x∈remxs)
remove-preserves-existing-elem y x (z ∷ xs) (here x==z) | no ¬y==z = here x==z
remove-preserves-existing-elem y x (z ∷ xs) (there x∈remxs) | no ¬y==z = there (remove-preserves-existing-elem y x xs x∈remxs)

remove-preserves-missing-elem : (y x : A) → (xs : List A)
                              → ¬ (InList x xs) → ¬ InList x (remove y xs)
remove-preserves-missing-elem y x [] ¬x∈xs = ¬x∈xs
remove-preserves-missing-elem y x (x' ∷ xs) ¬x∈xs x∈remxs with dec-eq y x' | dec-eq x x'
remove-preserves-missing-elem y x (x' ∷ xs) ¬x∈xs x∈remxs | yes y==x' | yes x==x' = ¬x∈xs (here x==x')
remove-preserves-missing-elem y x (x' ∷ xs) ¬x∈xs x∈remxs | yes y==x' | no ¬x==x' =
  remove-preserves-missing-elem y x xs (¬InList-forget-elem x x' xs ¬x∈xs) x∈remxs
remove-preserves-missing-elem y x (x' ∷ xs) ¬x∈xs x∈remxs | no ¬y==x' | yes x==x' = ¬x∈xs (here x==x')
remove-preserves-missing-elem y x (x' ∷ xs) ¬x∈xs x∈remxs | no ¬y==x' | no ¬x==x' = 
  remove-preserves-missing-elem y x xs (¬InList-forget-elem x x' xs ¬x∈xs) (InList-forget-elem x x' (remove y xs) ¬x==x' x∈remxs)

remove-preserves-missing-elem' : (z y x : A) → (xs : List A)
                                → ¬ (x == z)
                                → ¬ (InList x xs) → ¬ InList x (z ∷ remove y xs)
remove-preserves-missing-elem' z y x [] ¬x==z ¬x∈z∷xs x∈z∷xs = ¬x∈z∷xs (InList-forget-elem x z [] ¬x==z x∈z∷xs)
remove-preserves-missing-elem' z y x (z' ∷ xs) ¬x==z ¬x∈z∷xs x∈xs with dec-eq y z'
remove-preserves-missing-elem' z y x (z' ∷ xs) ¬x==z ¬x∈z∷xs (here x==z) | yes y==z' = ¬x==z x==z
remove-preserves-missing-elem' z y x (z' ∷ xs) ¬x==z ¬x∈z∷xs (there x∈remxs) | yes y==z' 
  = ¬x∈z∷xs (there (remove-preserves-existing-elem y x xs x∈remxs))
remove-preserves-missing-elem' z y x (z' ∷ xs) ¬x==z ¬x∈z∷xs (here x==z) | no ¬y==z' = ¬x==z x==z
remove-preserves-missing-elem' z y x (z' ∷ xs) ¬x==z ¬x∈z∷xs (there x∈xs) | no ¬y==z' with dec-eq x z'
remove-preserves-missing-elem' z y x (z' ∷ xs) ¬x==z ¬x∈z∷xs (there x∈xs) | no ¬y==z' | yes x==z' = ¬x∈z∷xs (here x==z')
remove-preserves-missing-elem' z y x (z' ∷ xs) ¬x==z ¬x∈z∷xs (there x∈xs) | no ¬y==z' | no ¬x==z' 
  = ¬x∈z∷xs (there (remove-preserves-existing-elem y x xs (InList-forget-elem x z' (remove y xs) ¬x==z' x∈xs)))

remove-preserves-no-dup : (x : A) → (xs : List A)
                        → IsNoDupList xs → IsNoDupList (remove x xs)
remove-preserves-no-dup y [] noDup = lift tt
remove-preserves-no-dup y (x ∷ xs) noDup with OrdInstance.dec-eq OrdA y x
remove-preserves-no-dup y (x ∷ xs) noDup | yes y==x = remove-preserves-no-dup y xs (proj₂ noDup)
remove-preserves-no-dup y (x ∷ xs) noDup | no ¬y==x = remove-preserves-missing-elem y x xs (proj₁ noDup)
                                                          , remove-preserves-no-dup y xs (proj₂ noDup)
          
remove-removing-missing-elem : (x : A) → (ys : List A)
                              → ¬ (InList x ys) → remove x ys ≡ ys
remove-removing-missing-elem x [] ¬x∈ys = refl
remove-removing-missing-elem x (y ∷ ys) ¬x∈ys with dec-eq x y
remove-removing-missing-elem x (y ∷ ys) ¬x∈ys | yes x==y = ⊥-elim (¬x∈ys (here x==y))
remove-removing-missing-elem x (y ∷ ys) ¬x∈ys | no ¬x==y = cong (λ X → y ∷ X) (remove-removing-missing-elem x ys (¬InList-forget-elem x y ys ¬x∈ys))

remove-removing-missing-elem' : (x : A) → (xs ys : List A)
                              → ¬ (InList x xs) → ys ≡ xs → remove x ys ≡ xs
remove-removing-missing-elem' x xs .xs ¬x∈xs refl = remove-removing-missing-elem x xs ¬x∈xs

private
  remove-keeps-not-removed-elem : (y x : A) → (xs : List A) 
                                → InList y (remove x xs) → InList y xs
  remove-keeps-not-removed-elem y x [] y∈remxs = y∈remxs
  remove-keeps-not-removed-elem y x (z ∷ xs) y∈remxs with dec-eq x z
  remove-keeps-not-removed-elem y x (z ∷ xs) y∈remxs | yes x==z with dec-eq y z
  remove-keeps-not-removed-elem y x (z ∷ xs) y∈remxs | yes x==z | yes y==z = here y==z
  remove-keeps-not-removed-elem y x (z ∷ xs) y∈remxs | yes x==z | no ¬y==z = there (remove-keeps-not-removed-elem y x xs y∈remxs)
  remove-keeps-not-removed-elem y x (z ∷ xs) (here  y==z   ) | no ¬x==z = here y==z
  remove-keeps-not-removed-elem y x (z ∷ xs) (there y∈remxs) | no ¬x==z = there (remove-keeps-not-removed-elem y x xs y∈remxs)


remove-preserves-sorted' : (y x : A) (xs : List A)
                          → IsSortedList (x ∷ xs) → IsSortedList (x ∷ remove y xs)
remove-preserves-sorted' y x [] sorted = lift tt
remove-preserves-sorted' y x (z ∷ xs) sorted with dec-eq y z
remove-preserves-sorted' y x (z ∷ xs) (x≤z , sorted) | yes y==z = remove-preserves-sorted' y x xs (IsSortedList-replace-elem z x xs x≤z sorted)
remove-preserves-sorted' y x (z ∷ xs) (x≤z , sorted) | no ¬y==z = x≤z , remove-preserves-sorted' y z xs sorted

remove-preserves-sorted : (x : A) (xs : List A)
                        → IsSortedList xs → IsSortedList (remove x xs)
remove-preserves-sorted y [] sorted = lift tt
remove-preserves-sorted y (x ∷ xs) sorted with dec-eq y x
remove-preserves-sorted y (x ∷ xs) sorted | yes y==x = remove-preserves-sorted y xs (IsSortedList-forget-elem x xs sorted)
remove-preserves-sorted y (x ∷ xs) sorted | no ¬y==x = remove-preserves-sorted' y x xs sorted

remove-shift-elem : (x y : A) → (xs : List A) 
                  → ¬ (y == x) → remove y (x ∷ xs) ≡ x ∷ remove y xs
remove-shift-elem x y xs ¬y==x with dec-eq y x
remove-shift-elem x y xs ¬y==x | yes y==x = ⊥-elim (¬y==x y==x)
remove-shift-elem x y xs ¬y==x | no ¬y==x' = refl

remove-shrink : (x y : A) → (xs : List A) 
              → x == y
              → remove x (remove y xs) ≡ remove x xs
remove-shrink x y [] x==y = refl
remove-shrink x y (z ∷ xs) x==y with dec-eq y z | dec-eq x z
remove-shrink x y (z ∷ xs) x==y | yes y==z | yes x==z = 
  remove-shrink x y xs x==y
remove-shrink x y (z ∷ xs) x==y | yes y==z | no ¬x==z = 
  ⊥-elim (¬x==z (trans-eq x==y y==z))
remove-shrink x y (z ∷ xs) x==y | no ¬y==z | yes x==z =
  ⊥-elim (¬y==z (trans-eq (sym-eq x==y) x==z))
remove-shrink x y (z ∷ xs) x==y | no ¬y==z | no ¬x==z = 
  trans (remove-shift-elem z x (remove y xs) ¬x==z) (cong (λ X → z ∷ X) (remove-shrink x y xs x==y))

remove-removes-first : (y x : A) → (xs : List A) 
                      → y == x → remove y (x ∷ xs) ≡ remove y xs
remove-removes-first y x xs y==x with dec-eq y x
remove-removes-first y x xs y==x | yes y==x' = refl
remove-removes-first y x xs y==x | no ¬y==x = ⊥-elim (¬y==x y==x)

remove-interchange : (x y : A) → (xs : List A) 
                    → remove x (remove y xs) ≡ remove y (remove x xs)
remove-interchange x y [] = refl
remove-interchange x y (z ∷ xs) with dec-eq y z | dec-eq x z
remove-interchange x y (z ∷ xs) | yes y==z | yes x==z = remove-interchange x y xs
remove-interchange x y (z ∷ xs) | yes y==z | no ¬x==z = 
  trans (remove-interchange x y xs) (sym (remove-removes-first y z (remove x xs) y==z))
remove-interchange x y (z ∷ xs) | no ¬y==z | yes x==z = 
  trans (remove-removes-first x z (remove y xs) x==z) (remove-interchange x y xs)
remove-interchange x y (z ∷ xs) | no ¬y==z | no ¬x==z = 
  trans (trans (remove-shift-elem z x (remove  y xs) ¬x==z) (cong (λ X → z ∷ X) (remove-interchange x y xs))) 
        (sym (remove-shift-elem z y (remove x xs) ¬y==z))

nub : List A → List A
nub [] = []
nub (x ∷ xs) = x ∷ remove x (nub xs)

nub-produces-no-dup : (xs : List A) → IsNoDupList (nub xs)
nub-produces-no-dup [] = lift tt
nub-produces-no-dup (x ∷ xs)
  = remove-produces-missing-elem x (nub xs)
  , remove-preserves-no-dup x (nub xs) (nub-produces-no-dup xs)


nub-preserves-existing-elem' : (x : A) → (xs : List A)
                              → InList x (nub xs) → InList x xs
nub-preserves-existing-elem' x [] x∈nubxs = x∈nubxs
nub-preserves-existing-elem' x (y ∷ xs) (here x==y) = here x==y
nub-preserves-existing-elem' x (y ∷ xs) (there x∈nubxs) = 
  there (nub-preserves-existing-elem' x xs (remove-keeps-not-removed-elem x y (nub xs) x∈nubxs))

nub-preserves-missing-elem : (x : A) → (xs : List A)
                            → ¬ InList x xs → ¬ InList x (nub xs)
nub-preserves-missing-elem y [] ¬y∈xs y∈xs = ¬y∈xs y∈xs
nub-preserves-missing-elem y (x ∷ xs) ¬y∈xs (here y==x) = ¬y∈xs (here y==x)
nub-preserves-missing-elem y (x ∷ xs) ¬y∈xs (there y∈remnubxs) with OrdInstance.dec-eq OrdA y x
nub-preserves-missing-elem y (x ∷ xs) ¬y∈xs (there y∈remnubxs) | yes y==x = ¬y∈xs (here y==x)
nub-preserves-missing-elem y (x ∷ xs) ¬y∈xs (there y∈remnubxs) | no ¬y==x = ¬InList-forget-elem y x xs ¬y∈xs (nub-preserves-existing-elem' y xs (remove-keeps-not-removed-elem y x (nub xs) y∈remnubxs))
  where p = remove-removing-missing-elem y (nub xs) (nub-preserves-missing-elem y xs (¬InList-forget-elem y x xs ¬y∈xs))

nub-preserves-no-dup : (xs : List A) → IsNoDupList xs → IsNoDupList (nub xs)
nub-preserves-no-dup xs _noDup = nub-produces-no-dup xs

nub-nubbing-no-dup : (xs : List A) → (ys : List A) → xs ≡ ys → IsNoDupList xs → nub xs ≡ ys
nub-nubbing-no-dup [] .[] refl noDup = refl
nub-nubbing-no-dup (x ∷ xs) .(x ∷ xs) refl (¬x∈xs , noDup) =
  cong (λ X → x ∷ X) (trans (remove-removing-missing-elem x (nub xs) (nub-preserves-missing-elem x xs ¬x∈xs))
                            (nub-nubbing-no-dup xs xs refl noDup))

nub-preserves-sorted' : (x : A) (xs : List A) → IsSortedList (x ∷ xs) → IsSortedList (x ∷ nub xs)
nub-preserves-sorted' x [] sorted = lift tt
nub-preserves-sorted' x (z ∷ xs) (x≤z , sorted) = x≤z , (remove-preserves-sorted' z z (nub xs) (nub-preserves-sorted' z xs sorted))

nub-preserves-sorted : (xs : List A) → IsSortedList xs → IsSortedList (nub xs)
nub-preserves-sorted [] sorted = lift tt
nub-preserves-sorted (x ∷ xs) sorted = remove-preserves-sorted' x x (nub xs) (nub-preserves-sorted' x xs sorted)

nub-remove-interchange : (x : A) → (xs : List A) → nub (remove x xs) ≡ remove x (nub xs)
nub-remove-interchange x [] = refl
nub-remove-interchange x (y ∷ xs) with dec-eq x y
nub-remove-interchange x (y ∷ xs) | yes x==y = 
  trans (nub-remove-interchange x xs) (sym $ remove-shrink x y (nub xs) x==y)
nub-remove-interchange x (y ∷ xs) | no ¬x==y = 
  cong (λ X → y ∷ X) $ trans (cong (remove y) (nub-remove-interchange x xs)) (remove-interchange y x (nub xs))
  
nub-shrink : (xs : List A) → nub (nub xs) ≡ nub xs
nub-shrink [] = refl
nub-shrink (x ∷ xs) = cong (λ X → x ∷ X) (trans (cong (remove x) (nub-remove-interchange x (nub xs))) 
                                                (trans (remove-shrink x x (nub (nub xs)) (OrdInstance.refl-eq OrdA)) 
                                                        (cong (remove x) (nub-shrink xs))))

nub-map-id : (xs : List A) → IsNoDupList xs → nub (mapList idF xs) ≡ xs
nub-map-id [] noDup = refl
nub-map-id (x ∷ xs) (¬x∈xs , noDup) 
  = cong (λ X → x ∷ X) (remove-removing-missing-elem' x xs (nub (mapList idF xs)) ¬x∈xs (nub-map-id xs noDup))
