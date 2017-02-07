
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


private
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

nub : {ℓEq ℓOrd : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} {ℓOrd} A) → List A → List A
nub OrdA [] = []
nub OrdA (x ∷ xs) = x ∷ remove OrdA x (nub OrdA xs)

nub-produces-no-dup : {ℓEq ℓOrd : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} {ℓOrd} A)
                    → (xs : List A) → IsNoDupList OrdA (nub OrdA xs)
nub-produces-no-dup OrdA [] = lift tt
nub-produces-no-dup OrdA (x ∷ xs)
  = remove-produces-missing-elem OrdA x (nub OrdA xs)
  , remove-preserves-no-dup OrdA x (nub OrdA xs) (nub-produces-no-dup OrdA xs)


nub-preserves-existing-elem : {ℓEq ℓOrd : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} {ℓOrd} A)
                            → (x : A) → (xs : List A)
                            → InList OrdA x (nub OrdA xs) → InList OrdA x xs
nub-preserves-existing-elem OrdA x xs x∈nubxs = {!!}
                           
nub-preserves-missing-elem : {ℓEq ℓOrd : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} {ℓOrd} A)
                           → (x : A) → (xs : List A)
                           → ¬ InList OrdA x xs → ¬ InList OrdA x (nub OrdA xs)
nub-preserves-missing-elem OrdA y [] ¬y∈xs y∈xs = ¬y∈xs y∈xs
nub-preserves-missing-elem OrdA y (x ∷ xs) ¬y∈xs (here y==x) = ¬y∈xs (here y==x)
nub-preserves-missing-elem OrdA y (x ∷ xs) ¬y∈xs (there y∈remnubxs) with OrdInstance.dec-eq OrdA y x
nub-preserves-missing-elem OrdA y (x ∷ xs) ¬y∈xs (there y∈remnubxs) | yes y==x = ¬y∈xs (here y==x)
nub-preserves-missing-elem OrdA y (x ∷ xs) ¬y∈xs (there y∈remnubxs) | no ¬y==x = ¬InList-forget-elem OrdA y x xs ¬y∈xs (nub-preserves-existing-elem OrdA y xs {!!})
  where p = remove-removing-missing-elem OrdA y (nub OrdA xs) (nub-preserves-missing-elem OrdA y xs {!!})


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

private
  nub-preserves-sorted' : {A : Type} → (OrdA : OrdInstance {lzero} A)
                        → (y x : A) (xs : List A)
                        → ¬ (OrdInstance._==_ OrdA y x) → (OrdInstance._≤_ OrdA y x)
                        → IsSortedList OrdA (nub OrdA (x ∷ xs)) → IsSortedList OrdA (y ∷ nub OrdA (x ∷ xs))
  nub-preserves-sorted' OrdA y x [] ¬y==x y≤x sorted = y≤x , tt
  nub-preserves-sorted' OrdA y x (z ∷ xs) ¬y==x y≤x sorted = {!!}

nub-preserves-sorted : {A : Type} → (OrdA : OrdInstance {lzero} A) → (xs : List A) → IsSortedList OrdA xs → IsSortedList OrdA (nub OrdA xs)
nub-preserves-sorted OrdA [] sorted = tt
nub-preserves-sorted OrdA (y ∷ []) sorted = tt
nub-preserves-sorted OrdA (y ∷ x ∷ xs) (y≤x , sorted) with nub-preserves-sorted OrdA (x ∷ xs) sorted
nub-preserves-sorted OrdA (y ∷ x ∷ xs) (y≤x , sorted) | p with OrdInstance.dec-eq OrdA y x
nub-preserves-sorted OrdA (y ∷ x ∷ xs) (y≤x , sorted) | p | yes y==x = {!!}
nub-preserves-sorted OrdA (y ∷ x ∷ []) (y≤x , sorted) | p | no ¬y==x = y≤x , tt
nub-preserves-sorted OrdA (y ∷ x ∷ z ∷ xs) (y≤x , sorted) | p | no ¬y==x with OrdInstance.dec-eq OrdA x z
nub-preserves-sorted OrdA (y ∷ x ∷ z ∷ xs) (y≤x , sorted) | p | no ¬y==x | no ¬x==z = y≤x , {!!}
nub-preserves-sorted OrdA (y ∷ x ∷ z ∷ xs) (y≤x , sorted) | p | no ¬y==x | yes x==z with OrdInstance.dec-eq OrdA y z
nub-preserves-sorted OrdA (y ∷ x ∷ z ∷ xs) (y≤x , sorted) | p | no ¬y==x | yes x==z | yes y==z = ⊥-elim (¬y==x (OrdInstance.trans-eq OrdA y==z (OrdInstance.sym-eq OrdA x==z)))
nub-preserves-sorted OrdA (y ∷ x ∷ z ∷ xs) (y≤x , x≤z , sorted) | p | no ¬y==x | yes x==z | no ¬y==z = {!!} -- nub-preserves-sorted' OrdA y z xs ¬y==z (OrdInstance.trans OrdA y≤x x≤z) ?

