
module Theory.Examples.Haskell.FunctorSet.Nub where 

open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Level renaming ( suc to lsuc ; zero to lzero)
open import Data.Unit hiding ( _≤_ ; _≟_ ; total )
open import Data.Empty
open import Data.List
open import Data.List.Any hiding ( map )
open import Data.Product hiding ( map )
open import Data.Sum hiding ( map )
open import Relation.Nullary
open import Relation.Binary using ( IsPreorder )
open import Relation.Binary.PropositionalEquality

open import Haskell
open import ProofIrrelevance 

open import Theory.Examples.Haskell.FunctorSet.Base



remove : {ℓEq ℓOrd : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} {ℓOrd} A)
       → A → List A → List A
remove OrdA y [] = []
remove OrdA y (x ∷ xs) with OrdInstance.dec-eq OrdA y x
remove OrdA y (x ∷ xs) | yes y==x = remove OrdA y xs
remove OrdA y (x ∷ xs) | no ¬y==x = x ∷ remove OrdA y xs

private
  remove-produces-missing-elem : {ℓEq ℓOrd : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} {ℓOrd} A)
                               → (x : A) → (xs : List A) → ¬ (InList OrdA x (remove OrdA x xs))
  remove-produces-missing-elem OrdA y [] ()
  remove-produces-missing-elem OrdA y (x ∷ xs) y∈xs with OrdInstance.dec-eq OrdA y x
  remove-produces-missing-elem OrdA y (x ∷ xs) y∈xs | yes y==x = remove-produces-missing-elem OrdA y xs y∈xs
  remove-produces-missing-elem OrdA y (x ∷ xs) (here y==x) | no ¬y==x = ¬y==x y==x
  remove-produces-missing-elem OrdA y (x ∷ xs) (there y∈xs) | no ¬y==x = remove-produces-missing-elem OrdA y xs y∈xs

private
  remove-preserves-missing-elem : {ℓEq ℓOrd : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} {ℓOrd} A)
                          → (y x : A) → (xs : List A) → ¬ (InList OrdA x xs) → ¬ InList OrdA x (remove OrdA y xs)
  remove-preserves-missing-elem OrdA y x [] ¬x∈xs = ¬x∈xs
  remove-preserves-missing-elem OrdA y x (x' ∷ xs) ¬x∈xs x∈remxs with OrdInstance.dec-eq OrdA y x' | OrdInstance.dec-eq OrdA x x'
  remove-preserves-missing-elem OrdA y x (x' ∷ xs) ¬x∈xs x∈remxs | yes y==x' | yes x==x' = ¬x∈xs (here x==x')
  remove-preserves-missing-elem OrdA y x (x' ∷ xs) ¬x∈xs x∈remxs | yes y==x' | no ¬x==x' =
    remove-preserves-missing-elem OrdA y x xs (¬InList-forget-elem OrdA x x' xs ¬x∈xs) x∈remxs
  remove-preserves-missing-elem OrdA y x (x' ∷ xs) ¬x∈xs x∈remxs | no ¬y==x' | yes x==x' = ¬x∈xs (here x==x')
  remove-preserves-missing-elem OrdA y x (x' ∷ xs) ¬x∈xs x∈remxs | no ¬y==x' | no ¬x==x' = 
    remove-preserves-missing-elem OrdA y x xs (¬InList-forget-elem OrdA x x' xs ¬x∈xs) (InList-forget-elem OrdA x x' (remove OrdA y xs) ¬x==x' x∈remxs)

private
  remove-preserves-no-dup : {ℓEq ℓOrd : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} {ℓOrd} A)
                          → (x : A) → (xs : List A)
                          → IsNoDupList OrdA xs → IsNoDupList OrdA (remove OrdA x xs)
  remove-preserves-no-dup OrdA y [] noDup = lift tt
  remove-preserves-no-dup OrdA y (x ∷ xs) noDup with OrdInstance.dec-eq OrdA y x
  remove-preserves-no-dup OrdA y (x ∷ xs) noDup | yes y==x = remove-preserves-no-dup OrdA y xs (proj₂ noDup)
  remove-preserves-no-dup OrdA y (x ∷ xs) noDup | no ¬y==x = remove-preserves-missing-elem OrdA y x xs (proj₁ noDup)
                                                           , remove-preserves-no-dup OrdA y xs (proj₂ noDup)

private
  remove-removing-missing-elem : {ℓEq ℓOrd : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} {ℓOrd} A)
                               → (x : A) → (ys : List A)
                               → ¬ (InList OrdA x ys) → remove OrdA x ys ≡ ys
  remove-removing-missing-elem OrdA x [] ¬x∈ys = refl
  remove-removing-missing-elem OrdA x (y ∷ ys) ¬x∈ys with OrdInstance.dec-eq OrdA x y
  remove-removing-missing-elem OrdA x (y ∷ ys) ¬x∈ys | yes x==y = ⊥-elim (¬x∈ys (here x==y))
  remove-removing-missing-elem OrdA x (y ∷ ys) ¬x∈ys | no ¬x==y = cong (λ X → y ∷ X) (remove-removing-missing-elem OrdA x ys (¬InList-forget-elem OrdA x y ys ¬x∈ys))

private
  remove-keeps-not-removed-elem : {ℓEq ℓOrd : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} {ℓOrd} A)
                                → (y x : A) → (xs : List A) 
                                → InList OrdA y (remove OrdA x xs) → InList OrdA y xs
  remove-keeps-not-removed-elem OrdA y x [] y∈remxs = y∈remxs
  remove-keeps-not-removed-elem OrdA y x (z ∷ xs) y∈remxs with OrdInstance.dec-eq OrdA x z
  remove-keeps-not-removed-elem OrdA y x (z ∷ xs) y∈remxs | yes x==z with OrdInstance.dec-eq OrdA y z
  remove-keeps-not-removed-elem OrdA y x (z ∷ xs) y∈remxs | yes x==z | yes y==z = here y==z
  remove-keeps-not-removed-elem OrdA y x (z ∷ xs) y∈remxs | yes x==z | no ¬y==z = there (remove-keeps-not-removed-elem OrdA y x xs y∈remxs)
  remove-keeps-not-removed-elem OrdA y x (z ∷ xs) (here  y==z   ) | no ¬x==z = here y==z
  remove-keeps-not-removed-elem OrdA y x (z ∷ xs) (there y∈remxs) | no ¬x==z = there (remove-keeps-not-removed-elem OrdA y x xs y∈remxs)


remove-preserves-sorted' : {ℓEq ℓOrd : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} {ℓOrd} A)
                         → (y x : A) (xs : List A)
                         → IsSortedList OrdA (x ∷ xs) → IsSortedList OrdA (x ∷ remove OrdA y xs)
remove-preserves-sorted' OrdA y x [] sorted = lift tt
remove-preserves-sorted' OrdA y x (z ∷ xs) sorted with OrdInstance.dec-eq OrdA y z
remove-preserves-sorted' OrdA y x (z ∷ xs) (x≤z , sorted) | yes y==z = remove-preserves-sorted' OrdA y x xs (IsSortedList-replace-elem OrdA z x xs x≤z sorted)
remove-preserves-sorted' OrdA y x (z ∷ xs) (x≤z , sorted) | no ¬y==z = x≤z , remove-preserves-sorted' OrdA y z xs sorted

remove-preserves-sorted : {ℓEq ℓOrd : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} {ℓOrd} A)
                        → (x : A) (xs : List A)
                        → IsSortedList OrdA xs → IsSortedList OrdA (remove OrdA x xs)
remove-preserves-sorted OrdA y [] sorted = lift tt
remove-preserves-sorted OrdA y (x ∷ xs) sorted with OrdInstance.dec-eq OrdA y x
remove-preserves-sorted OrdA y (x ∷ xs) sorted | yes y==x = remove-preserves-sorted OrdA y xs (IsSortedList-forget-elem OrdA x xs sorted)
remove-preserves-sorted OrdA y (x ∷ xs) sorted | no ¬y==x = remove-preserves-sorted' OrdA y x xs sorted

remove-shift-elem : {ℓEq ℓOrd : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} {ℓOrd} A)
                  → (x y : A) → (xs : List A) 
                  → ¬ (OrdInstance._==_ OrdA y x) → remove OrdA y (x ∷ xs) ≡ x ∷ remove OrdA y xs
remove-shift-elem OrdA x y xs ¬y==x with OrdInstance.dec-eq OrdA y x
remove-shift-elem OrdA x y xs ¬y==x | yes y==x = ⊥-elim (¬y==x y==x)
remove-shift-elem OrdA x y xs ¬y==x | no ¬y==x' = refl

remove-shrink : {ℓEq ℓOrd : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} {ℓOrd} A)
              → (x y : A) → (xs : List A) 
              → OrdInstance._==_ OrdA x y
              → remove OrdA x (remove OrdA y xs) ≡ remove OrdA x xs
remove-shrink OrdA x y [] x==y = refl
remove-shrink OrdA x y (z ∷ xs) x==y with OrdInstance.dec-eq OrdA y z | OrdInstance.dec-eq OrdA x z
remove-shrink OrdA x y (z ∷ xs) x==y | yes y==z | yes x==z = 
  remove-shrink OrdA x y xs x==y
remove-shrink OrdA x y (z ∷ xs) x==y | yes y==z | no ¬x==z = 
  ⊥-elim (¬x==z (OrdInstance.trans-eq OrdA x==y y==z))
remove-shrink OrdA x y (z ∷ xs) x==y | no ¬y==z | yes x==z =
  ⊥-elim (¬y==z (OrdInstance.trans-eq OrdA (OrdInstance.sym-eq OrdA x==y) x==z))
remove-shrink OrdA x y (z ∷ xs) x==y | no ¬y==z | no ¬x==z = 
  trans (remove-shift-elem OrdA z x (remove OrdA y xs) ¬x==z) (cong (λ X → z ∷ X) (remove-shrink OrdA x y xs x==y))

remove-removes-first : {ℓEq ℓOrd : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} {ℓOrd} A)
                     → (y x : A) → (xs : List A) 
                     → OrdInstance._==_ OrdA y x → remove OrdA y (x ∷ xs) ≡ remove OrdA y xs
remove-removes-first OrdA y x xs y==x with OrdInstance.dec-eq OrdA y x
remove-removes-first OrdA y x xs y==x | yes y==x' = refl
remove-removes-first OrdA y x xs y==x | no ¬y==x = ⊥-elim (¬y==x y==x)

remove-interchange : {ℓEq ℓOrd : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} {ℓOrd} A)
                   → (x y : A) → (xs : List A) 
                   → remove OrdA x (remove OrdA y xs) ≡ remove OrdA y (remove OrdA x xs)
remove-interchange OrdA x y [] = refl
remove-interchange OrdA x y (z ∷ xs) with OrdInstance.dec-eq OrdA y z | OrdInstance.dec-eq OrdA x z
remove-interchange OrdA x y (z ∷ xs) | yes y==z | yes x==z = remove-interchange OrdA x y xs
remove-interchange OrdA x y (z ∷ xs) | yes y==z | no ¬x==z = 
  trans (remove-interchange OrdA x y xs) (sym (remove-removes-first OrdA y z (remove OrdA x xs) y==z))
remove-interchange OrdA x y (z ∷ xs) | no ¬y==z | yes x==z = 
  trans (remove-removes-first OrdA x z (remove OrdA y xs) x==z) (remove-interchange OrdA x y xs)
remove-interchange OrdA x y (z ∷ xs) | no ¬y==z | no ¬x==z = 
  trans (trans (remove-shift-elem OrdA z x (remove OrdA y xs) ¬x==z) (cong (λ X → z ∷ X) (remove-interchange OrdA x y xs))) 
        (sym (remove-shift-elem OrdA z y (remove OrdA x xs) ¬y==z))

nub : {ℓEq ℓOrd : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} {ℓOrd} A) → List A → List A
nub OrdA [] = []
nub OrdA (x ∷ xs) = x ∷ remove OrdA x (nub OrdA xs)

nub-produces-no-dup : {ℓEq ℓOrd : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} {ℓOrd} A)
                    → (xs : List A) → IsNoDupList OrdA (nub OrdA xs)
nub-produces-no-dup OrdA [] = lift tt
nub-produces-no-dup OrdA (x ∷ xs)
  = remove-produces-missing-elem OrdA x (nub OrdA xs)
  , remove-preserves-no-dup OrdA x (nub OrdA xs) (nub-produces-no-dup OrdA xs)


nub-preserves-existing-elem' : {ℓEq ℓOrd : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} {ℓOrd} A)
                             → (x : A) → (xs : List A)
                             → InList OrdA x (nub OrdA xs) → InList OrdA x xs
nub-preserves-existing-elem' OrdA x [] x∈nubxs = x∈nubxs
nub-preserves-existing-elem' OrdA x (y ∷ xs) (here x==y) = here x==y
nub-preserves-existing-elem' OrdA x (y ∷ xs) (there x∈nubxs) = 
  there (nub-preserves-existing-elem' OrdA x xs (remove-keeps-not-removed-elem OrdA x y (nub OrdA xs) x∈nubxs))

nub-preserves-missing-elem : {ℓEq ℓOrd : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} {ℓOrd} A)
                           → (x : A) → (xs : List A)
                           → ¬ InList OrdA x xs → ¬ InList OrdA x (nub OrdA xs)
nub-preserves-missing-elem OrdA y [] ¬y∈xs y∈xs = ¬y∈xs y∈xs
nub-preserves-missing-elem OrdA y (x ∷ xs) ¬y∈xs (here y==x) = ¬y∈xs (here y==x)
nub-preserves-missing-elem OrdA y (x ∷ xs) ¬y∈xs (there y∈remnubxs) with OrdInstance.dec-eq OrdA y x
nub-preserves-missing-elem OrdA y (x ∷ xs) ¬y∈xs (there y∈remnubxs) | yes y==x = ¬y∈xs (here y==x)
nub-preserves-missing-elem OrdA y (x ∷ xs) ¬y∈xs (there y∈remnubxs) | no ¬y==x = ¬InList-forget-elem OrdA y x xs ¬y∈xs (nub-preserves-existing-elem' OrdA y xs (remove-keeps-not-removed-elem OrdA y x (nub OrdA xs) y∈remnubxs))
  where p = remove-removing-missing-elem OrdA y (nub OrdA xs) (nub-preserves-missing-elem OrdA y xs (¬InList-forget-elem OrdA y x xs ¬y∈xs))


nub-nubbing-no-dup : {ℓEq ℓOrd : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} {ℓOrd} A) → (xs : List A) → IsNoDupList OrdA xs → nub OrdA xs ≡ xs
nub-nubbing-no-dup {A = A} OrdA [] noDup = refl
nub-nubbing-no-dup {A = A} OrdA (x ∷ xs) (¬x∈xs , noDup) =
  cong (λ X → x ∷ X) (trans (remove-removing-missing-elem OrdA x (nub OrdA xs) (nub-preserves-missing-elem OrdA x xs ¬x∈xs))
                            (nub-nubbing-no-dup OrdA xs noDup))

private
  ¬x==y∧y==z→¬x==z : {ℓEq ℓOrd : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} {ℓOrd} A) → (x y z : A)
                   → (¬ (OrdInstance._==_ OrdA x y)) → OrdInstance._==_ OrdA y z → ¬ (OrdInstance._==_ OrdA x z)
  ¬x==y∧y==z→¬x==z OrdA x y z ¬x==y y==z x==z = ¬x==y (OrdInstance.trans-eq OrdA x==z (OrdInstance.sym-eq OrdA y==z))
  
  x≤y∧y==z→x≤z : {ℓEq ℓOrd : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} {ℓOrd} A) → (x y z : A)
                      → OrdInstance._≤_ OrdA x y → OrdInstance._==_ OrdA y z → OrdInstance._≤_ OrdA x z
  x≤y∧y==z→x≤z OrdA x y z x≤y y==z = (proj₁ (IsPreorder.∼-resp-≈ (OrdInstance.isPreorder OrdA))) y==z x≤y


nub-preserves-sorted' : {ℓEq ℓOrd : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} {ℓOrd} A)
                      → (x : A) (xs : List A)
                      → IsSortedList OrdA (x ∷ xs) → IsSortedList OrdA (x ∷ nub OrdA xs)
nub-preserves-sorted' OrdA x [] sorted = lift tt
nub-preserves-sorted' OrdA x (z ∷ xs) (x≤z , sorted) = x≤z , (remove-preserves-sorted' OrdA z z (nub OrdA xs) (nub-preserves-sorted' OrdA z xs sorted))

nub-preserves-sorted : {ℓEq ℓOrd : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} {ℓOrd} A) 
                     → (xs : List A) 
                     → IsSortedList OrdA xs → IsSortedList OrdA (nub OrdA xs)
nub-preserves-sorted OrdA [] sorted = lift tt
nub-preserves-sorted OrdA (x ∷ xs) sorted = remove-preserves-sorted' OrdA x x (nub OrdA xs) (nub-preserves-sorted' OrdA x xs sorted)

nub-remove-interchange : {ℓEq ℓOrd : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} {ℓOrd} A)
                          → (x : A) → (xs : List A) 
                          → nub OrdA (remove OrdA x xs) ≡ remove OrdA x (nub OrdA xs)
nub-remove-interchange OrdA x [] = refl
nub-remove-interchange OrdA x (y ∷ xs) with OrdInstance.dec-eq OrdA x y
nub-remove-interchange OrdA x (y ∷ xs) | yes x==y = 
  trans (nub-remove-interchange OrdA x xs) (sym $ remove-shrink OrdA x y (nub OrdA xs) x==y)
nub-remove-interchange OrdA x (y ∷ xs) | no ¬x==y = 
  cong (λ X → y ∷ X) $ trans (cong (remove OrdA y) (nub-remove-interchange OrdA x xs)) (remove-interchange OrdA y x (nub OrdA xs))

nub-shrink : {ℓEq ℓOrd : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} {ℓOrd} A) 
           → (xs : List A) 
           → nub OrdA (nub OrdA xs) ≡ nub OrdA xs
nub-shrink OrdA [] = refl
nub-shrink OrdA (x ∷ xs) = cong (λ X → x ∷ X) (trans (cong (remove OrdA x) (nub-remove-interchange OrdA x (nub OrdA xs))) 
                                              (trans (remove-shrink OrdA x x (nub OrdA (nub OrdA xs)) (OrdInstance.refl-eq OrdA)) 
                                                     (cong (remove OrdA x) (nub-shrink OrdA xs))))
