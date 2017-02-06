
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

nub : {ℓEq ℓOrd : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} {ℓOrd} A) → List A → List A
nub OrdA [] = []
nub OrdA (x ∷ []) = x ∷ []
nub OrdA (y ∷ x ∷ xs) with OrdInstance.dec-eq OrdA y x
nub OrdA (y ∷ x ∷ xs) | yes y==x = nub OrdA (x ∷ xs)
nub OrdA (y ∷ x ∷ xs) | no ¬y==x = y ∷ nub OrdA (x ∷ xs)

nub-preserves-no-dup : {ℓEq ℓOrd : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} {ℓOrd} A) → (xs : List A) → IsNoDupList OrdA xs → nub OrdA xs ≡ xs
nub-preserves-no-dup OrdA [] noDup = refl
nub-preserves-no-dup OrdA (x ∷ []) noDup = refl
nub-preserves-no-dup OrdA (x ∷ y ∷ xs) noDup with OrdInstance.dec-eq OrdA x y
nub-preserves-no-dup OrdA (x ∷ y ∷ xs) (¬x∈y∷xs , noDup) | yes x==y = ⊥-elim (¬x∈y∷xs (here x==y))
nub-preserves-no-dup OrdA (x ∷ y ∷ xs) noDup | no ¬x==y = cong (λ XS → x ∷ XS) (nub-preserves-no-dup OrdA (y ∷ xs) (proj₂ noDup))

nub-produces-no-dup : {ℓEq : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} A) → (xs : List A) → IsSortedList OrdA xs → IsNoDupList OrdA (nub OrdA xs)
nub-produces-no-dup OrdA [] sorted = lift tt
nub-produces-no-dup OrdA (x ∷ []) sorted = (λ ()) , lift tt
nub-produces-no-dup OrdA (x ∷ y ∷ xs) sorted with OrdInstance.dec-eq OrdA x y
nub-produces-no-dup OrdA (x ∷ y ∷ xs) sorted | yes x==y = nub-produces-no-dup OrdA (y ∷ xs) (proj₂ sorted)
nub-produces-no-dup OrdA (x ∷ y ∷ []) (x≤y , sorted) | no ¬x==y = x∈y∷[] , (λ ()) , lift tt
  where x∈y∷[] : ¬ InList OrdA x (y ∷ [])
        x∈y∷[] (here x==y) = ⊥-elim (¬x==y x==y)
        x∈y∷[] (there ())
nub-produces-no-dup OrdA (x ∷ y ∷ z ∷ xs) (x≤y , y≤z ,  sorted) | no ¬x==y with nub-produces-no-dup OrdA (y ∷ z ∷ xs) (y≤z , sorted)
nub-produces-no-dup OrdA (x ∷ y ∷ z ∷ xs) (x≤y , y≤z ,  sorted) | no ¬x==y | p = f , p
  where f : ¬ InList OrdA x (nub OrdA (y ∷ z ∷ xs))
        f x∈nubxs with OrdInstance.dec-eq OrdA y z
        f x∈nubxs | yes y==z = {!!}
        f (here x==y) | no ¬y==z = ¬x==y x==y
        f (there x∈nubxs) | no ¬y==z = {!!}

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
  nub-preserves-sorted' OrdA y x (z ∷ xs) ¬y==x y≤x sorted with OrdInstance.dec-eq OrdA x z
  nub-preserves-sorted' OrdA y x (z ∷ xs) ¬y==x y≤x sorted | yes x==z = nub-preserves-sorted' OrdA y z xs (¬x==y∧y==z→¬x==z OrdA y x z ¬y==x x==z) (x≤y∧y==z→x≤z OrdA y x z y≤x x==z) sorted
  nub-preserves-sorted' OrdA y x (z ∷ xs) ¬y==x y≤x sorted | no ¬x==z = y≤x , sorted

nub-preserves-sorted : {A : Type} → (OrdA : OrdInstance {lzero} A) → (xs : List A) → IsSortedList OrdA xs → IsSortedList OrdA (nub OrdA xs)
nub-preserves-sorted OrdA [] sorted = tt
nub-preserves-sorted OrdA (y ∷ []) sorted = tt
nub-preserves-sorted OrdA (y ∷ x ∷ xs) (y≤x , sorted) with nub-preserves-sorted OrdA (x ∷ xs) sorted
nub-preserves-sorted OrdA (y ∷ x ∷ xs) (y≤x , sorted) | p with OrdInstance.dec-eq OrdA y x
nub-preserves-sorted OrdA (y ∷ x ∷ xs) (y≤x , sorted) | p | yes y==x = p
nub-preserves-sorted OrdA (y ∷ x ∷ []) (y≤x , sorted) | p | no ¬y==x = y≤x , tt
nub-preserves-sorted OrdA (y ∷ x ∷ z ∷ xs) (y≤x , sorted) | p | no ¬y==x with OrdInstance.dec-eq OrdA x z
nub-preserves-sorted OrdA (y ∷ x ∷ z ∷ xs) (y≤x , sorted) | p | no ¬y==x | no ¬x==z = y≤x , p
nub-preserves-sorted OrdA (y ∷ x ∷ z ∷ xs) (y≤x , sorted) | p | no ¬y==x | yes x==z with OrdInstance.dec-eq OrdA y z
nub-preserves-sorted OrdA (y ∷ x ∷ z ∷ xs) (y≤x , sorted) | p | no ¬y==x | yes x==z | yes y==z = ⊥-elim (¬y==x (OrdInstance.trans-eq OrdA y==z (OrdInstance.sym-eq OrdA x==z)))
nub-preserves-sorted OrdA (y ∷ x ∷ z ∷ xs) (y≤x , x≤z , sorted) | p | no ¬y==x | yes x==z | no ¬y==z = nub-preserves-sorted' OrdA y z xs ¬y==z (OrdInstance.trans OrdA y≤x x≤z) p

