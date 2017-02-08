
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
open ≡-Reasoning

open import Haskell
open import ProofIrrelevance 

open import Theory.Examples.Haskell.FunctorSet.Base


insert : {ℓEq ℓOrd : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} {ℓOrd} A) → A → List A → List A
insert OrdA x [] = x ∷ []
insert OrdA x (y ∷ ys) with OrdInstance.dec-ord OrdA x y
insert OrdA x (y ∷ ys) | yes x≤y = x ∷ y ∷ ys
insert OrdA x (y ∷ ys) | no ¬x≤y = y ∷ insert OrdA x ys

insert-preserves-sorted' : {ℓEq ℓOrd : Level} {A : Type}
                         → (OrdA : OrdInstance {ℓEq} {ℓOrd} A)
                         → (x z : A) → (xs : List A)
                         → (OrdInstance._≤_ OrdA x z)
                         → IsSortedList OrdA (x ∷ xs)
                         → IsSortedList OrdA (x ∷ insert OrdA z xs)
insert-preserves-sorted' OrdA x z [] x≤z (lift tt) with OrdInstance.dec-ord OrdA x z 
insert-preserves-sorted' OrdA x z [] x≤z (lift tt) | yes _ = x≤z , lift tt
insert-preserves-sorted' OrdA x z [] x≤z (lift tt) | no ¬x≤z = ⊥-elim (¬x≤z x≤z)
insert-preserves-sorted' OrdA x z (y ∷ xs) x≤z (x≤y , sorted[y∷xs]) with OrdInstance.dec-ord OrdA x z
insert-preserves-sorted' OrdA x z (y ∷ xs) x≤z (x≤y , sorted[y∷xs]) | yes _ with OrdInstance.dec-ord OrdA z y
insert-preserves-sorted' OrdA x z (y ∷ xs) x≤z (x≤y , sorted[y∷xs]) | yes _ | yes z≤y = x≤z , z≤y , sorted[y∷xs]
insert-preserves-sorted' OrdA x z (y ∷ xs) x≤z (x≤y , sorted[y∷xs]) | yes _ | no ¬z≤y 
  = x≤y 
  , insert-preserves-sorted' OrdA y z xs (OrdInstance.excluded-middle-ord OrdA ¬z≤y) sorted[y∷xs]
insert-preserves-sorted' OrdA x z (y ∷ xs) x≤z (x≤y , sorted[y∷xs]) | no ¬x≤z = ⊥-elim (¬x≤z x≤z)

insert-preserves-sorted : {ℓEq ℓOrd : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} {ℓOrd} A) 
                        → (x : A) → (xs : List A) 
                        → IsSortedList OrdA xs → IsSortedList OrdA (insert OrdA x xs)
insert-preserves-sorted OrdA x [] (lift tt) = lift tt
insert-preserves-sorted OrdA x (y ∷ []) (lift tt) with OrdInstance.dec-ord OrdA x y 
insert-preserves-sorted OrdA x (y ∷ []) (lift tt) | yes x≤y = x≤y , lift tt
insert-preserves-sorted OrdA x (y ∷ []) (lift tt) | no ¬x≤y with OrdInstance.total OrdA y x
insert-preserves-sorted OrdA x (y ∷ []) (lift tt) | no ¬x≤y | inj₁ y≤x = y≤x , lift tt
insert-preserves-sorted OrdA x (y ∷ []) (lift tt) | no ¬x≤y | inj₂ x≤y = ⊥-elim (¬x≤y x≤y)
insert-preserves-sorted OrdA x (y ∷ z ∷ xs) (y≤z , sorted[z∷xs]) with OrdInstance.dec-ord OrdA x y
insert-preserves-sorted OrdA x (y ∷ z ∷ xs) (y≤z , sorted[z∷xs]) | yes x≤y = x≤y , y≤z , sorted[z∷xs]
insert-preserves-sorted OrdA x (y ∷ z ∷ xs) (y≤z , sorted[z∷xs]) | no ¬x≤y with OrdInstance.total OrdA x y
insert-preserves-sorted OrdA x (y ∷ z ∷ xs) (y≤z , sorted[z∷xs]) | no ¬x≤y | inj₁ x≤y = ⊥-elim (¬x≤y x≤y)
insert-preserves-sorted OrdA x (y ∷ z ∷ xs) (y≤z , sorted[z∷xs]) | no ¬x≤y | inj₂ y≤x with OrdInstance.dec-ord OrdA x z
insert-preserves-sorted OrdA x (y ∷ z ∷ xs) (y≤z , sorted[z∷xs]) | no ¬x≤y | inj₂ y≤x | yes x≤z = y≤x , x≤z , sorted[z∷xs]
insert-preserves-sorted OrdA x (y ∷ z ∷ xs) (y≤z , sorted[z∷xs]) | no ¬x≤y | inj₂ y≤x | no ¬x≤z with insert-preserves-sorted' OrdA z x xs (OrdInstance.excluded-middle-ord OrdA ¬x≤z) sorted[z∷xs]
insert-preserves-sorted OrdA x (y ∷ z ∷ xs) (y≤z , sorted[z∷xs]) | no ¬x≤y | inj₂ y≤x | no ¬x≤z | p = y≤z , p

insert-preserves-missing-elem : {ℓEq ℓOrd : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} {ℓOrd} A) 
                              → (x y : A) → (xs : List A) 
                              → ¬ (OrdInstance._==_ OrdA x y)
                              → ¬ InList OrdA x xs
                              → ¬ InList OrdA x (insert OrdA y xs)
insert-preserves-missing-elem OrdA x y [] ¬y==x ¬x∈xs (here y==x) = ¬y==x y==x
insert-preserves-missing-elem OrdA x y [] ¬y==x ¬x∈xs (there ())
insert-preserves-missing-elem OrdA x y (z ∷ xs) ¬y==x ¬x∈xs x∈insxs with OrdInstance.dec-ord OrdA y z
insert-preserves-missing-elem OrdA x y (z ∷ xs) ¬y==x ¬x∈xs x∈insxs | yes y≤z 
  = ¬x∈xs (InList-forget-elem OrdA x y (z ∷ xs) ¬y==x x∈insxs)
insert-preserves-missing-elem OrdA x y (z ∷ xs) ¬y==x ¬x∈xs (here x==z) | no ¬y≤z = ¬x∈xs (here x==z)
insert-preserves-missing-elem OrdA x y (z ∷ xs) ¬y==x ¬x∈xs (there x∈insxs) | no ¬y≤z 
  = insert-preserves-missing-elem OrdA x y xs ¬y==x (¬InList-forget-elem OrdA x z xs ¬x∈xs) x∈insxs

insert-smallest-in-front' : {ℓEq ℓOrd : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} {ℓOrd} A)
                          → (x y : A) → (xs : List A)
                          → OrdInstance._≤_ OrdA x y
                          → insert OrdA x (y ∷ xs) ≡ x ∷ y ∷ xs
insert-smallest-in-front' OrdA x y [] x≤y with OrdInstance.dec-ord OrdA x y
insert-smallest-in-front' OrdA x y [] x≤y | yes _ = refl
insert-smallest-in-front' OrdA x y [] x≤y | no ¬x≤y = ⊥-elim (¬x≤y x≤y)
insert-smallest-in-front' OrdA x y (z ∷ xs) x≤y with OrdInstance.dec-ord OrdA x y 
insert-smallest-in-front' OrdA x y (z ∷ xs) x≤y | yes _ = refl
insert-smallest-in-front' OrdA x y (z ∷ xs) x≤y | no ¬x≤y = ⊥-elim (¬x≤y x≤y)

insert-smallest-in-front : {ℓEq ℓOrd : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} {ℓOrd} A)
                         → (x : A) → (xs : List A)
                         → IsSortedList OrdA (x ∷ xs)
                         → insert OrdA x xs ≡ x ∷ xs
insert-smallest-in-front OrdA x [] (lift tt) = refl
insert-smallest-in-front OrdA x (y ∷ xs) (x≤y , sorted) = insert-smallest-in-front' OrdA x y xs x≤y

insert-shift-elem : {ℓEq ℓOrd : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} {ℓOrd} A)
                  → (y x : A) → (xs : List A)
                  → OrdInstance._≤_ OrdA x y → ¬ (OrdInstance._==_ OrdA y x)
                  → insert OrdA y (x ∷ xs) ≡ x ∷ insert OrdA y xs
insert-shift-elem OrdA y x [] x≤y ¬y==x with OrdInstance.dec-ord OrdA y x
insert-shift-elem OrdA y x [] x≤y ¬y==x | yes y≤x = ⊥-elim (¬y==x (OrdInstance.antisym OrdA y≤x x≤y))
insert-shift-elem OrdA y x [] x≤y ¬y==x | no ¬y≤x = refl
insert-shift-elem OrdA y x (z ∷ xs) x≤y ¬y==x with OrdInstance.dec-ord OrdA y x
insert-shift-elem OrdA y x (z ∷ xs) x≤y ¬y==x | yes y≤x = ⊥-elim (¬y==x (OrdInstance.antisym OrdA y≤x x≤y))
insert-shift-elem OrdA y x (z ∷ xs) x≤y ¬y==x | no ¬y≤x with OrdInstance.dec-ord OrdA y z
insert-shift-elem OrdA y x (z ∷ xs) x≤y ¬y==x | no ¬y≤x | yes y≤z = refl
insert-shift-elem OrdA y x (z ∷ xs) x≤y ¬y==x | no ¬y≤x | no ¬y≤z = refl

insert-interchange : {ℓEq ℓOrd : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} {ℓOrd} A) 
                   → (x y : A) → (xs : List A) 
                   → ¬ (OrdInstance._==_ OrdA x y)
                   → insert OrdA x (insert OrdA y xs) ≡ insert OrdA y (insert OrdA x xs)
insert-interchange OrdA x y [] ¬x==y with OrdInstance.dec-ord OrdA x y | OrdInstance.dec-ord OrdA y x
insert-interchange OrdA x y [] ¬x==y | yes x≤y | yes y≤x = ⊥-elim (¬x==y (OrdInstance.antisym OrdA x≤y y≤x))
insert-interchange OrdA x y [] ¬x==y | yes x≤y | no ¬y≤x = refl
insert-interchange OrdA x y [] ¬x==y | no ¬x≤y | yes y≤x = refl
insert-interchange OrdA x y [] ¬x==y | no ¬x≤y | no ¬y≤x = ⊥-elim (OrdInstance.total-contr OrdA ¬y≤x ¬x≤y)
insert-interchange OrdA x y (z ∷ xs) ¬x==y with OrdInstance.dec-ord OrdA y z 
insert-interchange OrdA x y (z ∷ xs) ¬x==y | yes y≤z with OrdInstance.dec-ord OrdA x y
insert-interchange OrdA x y (z ∷ xs) ¬x==y | yes y≤z | yes x≤y with OrdInstance.dec-ord OrdA x z
insert-interchange OrdA x y (z ∷ xs) ¬x==y | yes y≤z | yes x≤y | yes x≤z with OrdInstance.dec-ord OrdA y x
insert-interchange OrdA x y (z ∷ xs) ¬x==y | yes y≤z | yes x≤y | yes x≤z | yes y≤x = ⊥-elim (¬x==y (OrdInstance.antisym OrdA x≤y y≤x))
insert-interchange OrdA x y (z ∷ xs) ¬x==y | yes y≤z | yes x≤y | yes x≤z | no ¬y≤x with OrdInstance.dec-ord OrdA y z
insert-interchange OrdA x y (z ∷ xs) ¬x==y | yes y≤z | yes x≤y | yes x≤z | no ¬y≤x | yes _ = refl
insert-interchange OrdA x y (z ∷ xs) ¬x==y | yes y≤z | yes x≤y | yes x≤z | no ¬y≤x | no ¬y≤z = ⊥-elim (¬y≤z y≤z)
insert-interchange OrdA x y (z ∷ xs) ¬x==y | yes y≤z | yes x≤y | no ¬x≤z = ⊥-elim (¬x≤z (OrdInstance.trans OrdA x≤y y≤z))
insert-interchange OrdA x y (z ∷ xs) ¬x==y | yes y≤z | no ¬x≤y with OrdInstance.dec-ord OrdA x z
insert-interchange OrdA x y (z ∷ xs) ¬x==y | yes y≤z | no ¬x≤y | yes x≤z with OrdInstance.dec-ord OrdA y x
insert-interchange OrdA x y (z ∷ xs) ¬x==y | yes y≤z | no ¬x≤y | yes x≤z | yes y≤x = refl
insert-interchange OrdA x y (z ∷ xs) ¬x==y | yes y≤z | no ¬x≤y | yes x≤z | no ¬y≤x = ⊥-elim (OrdInstance.total-contr OrdA ¬x≤y ¬y≤x)
insert-interchange OrdA x y (z ∷ xs) ¬x==y | yes y≤z | no ¬x≤y | no ¬x≤z with OrdInstance.dec-ord OrdA y z
insert-interchange OrdA x y (z ∷ xs) ¬x==y | yes y≤z | no ¬x≤y | no ¬x≤z | yes _ = refl
insert-interchange OrdA x y (z ∷ xs) ¬x==y | yes y≤z | no ¬x≤y | no ¬x≤z | no ¬y≤z = ⊥-elim (¬y≤z y≤z)
insert-interchange OrdA x y (z ∷ xs) ¬x==y | no ¬y≤z with OrdInstance.dec-ord OrdA x z
insert-interchange OrdA x y (z ∷ xs) ¬x==y | no ¬y≤z | yes x≤z with OrdInstance.dec-ord OrdA y x
insert-interchange OrdA x y (z ∷ xs) ¬x==y | no ¬y≤z | yes x≤z | yes y≤x = ⊥-elim (¬y≤z (OrdInstance.trans OrdA y≤x x≤z))
insert-interchange OrdA x y (z ∷ xs) ¬x==y | no ¬y≤z | yes x≤z | no ¬y≤x with OrdInstance.dec-ord OrdA y z
insert-interchange OrdA x y (z ∷ xs) ¬x==y | no ¬y≤z | yes x≤z | no ¬y≤x | yes y≤z = ⊥-elim (¬y≤z y≤z)
insert-interchange OrdA x y (z ∷ xs) ¬x==y | no ¬y≤z | yes x≤z | no ¬y≤x | no _ = refl
insert-interchange OrdA x y (z ∷ xs) ¬x==y | no ¬y≤z | no ¬x≤z with OrdInstance.dec-ord OrdA y z
insert-interchange OrdA x y (z ∷ xs) ¬x==y | no ¬y≤z | no ¬x≤z | yes y≤z = ⊥-elim (¬y≤z y≤z)
insert-interchange OrdA x y (z ∷ xs) ¬x==y | no ¬y≤z | no ¬x≤z | no _ = cong (λ X → z ∷ X) (insert-interchange OrdA x y xs ¬x==y)

sort : {ℓEq ℓOrd : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} {ℓOrd} A) → List A → List A
sort OrdA [] = []
sort OrdA (x ∷ xs) = insert OrdA x (sort OrdA xs)

sort-produces-sorted : {ℓEq ℓOrd : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} {ℓOrd} A) → (xs : List A) → IsSortedList OrdA (sort OrdA xs)
sort-produces-sorted OrdA [] = lift tt
sort-produces-sorted OrdA (x ∷ []) = lift tt
sort-produces-sorted OrdA (x ∷ y ∷ xs) = insert-preserves-sorted OrdA x (insert OrdA y (sort OrdA xs))
                                       ( insert-preserves-sorted OrdA y (sort OrdA xs) (sort-produces-sorted OrdA xs))

sort-sorting-sorted : {ℓEq ℓOrd : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} {ℓOrd} A) → (xs : List A) → IsSortedList OrdA xs → sort OrdA xs ≡ xs
sort-sorting-sorted OrdA [] sorted = refl
sort-sorting-sorted OrdA (y ∷ []) sorted = refl
sort-sorting-sorted OrdA (y ∷ x ∷ xs) (y≤x , sorted) with sort-sorting-sorted OrdA (x ∷ xs) sorted
sort-sorting-sorted OrdA (y ∷ x ∷ xs) (y≤x , sorted) | p =
  trans (cong (insert OrdA y) p) (insert-smallest-in-front OrdA y (x ∷ xs) (y≤x , sorted))

sort-shrink : {ℓEq ℓOrd : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} {ℓOrd} A) 
           → (xs : List A) 
           → sort OrdA (sort OrdA xs) ≡ sort OrdA xs
sort-shrink OrdA [] = refl
sort-shrink OrdA (x ∷ xs) = sort-sorting-sorted OrdA (insert OrdA x (sort OrdA xs)) (insert-preserves-sorted OrdA x (sort OrdA xs) (sort-produces-sorted OrdA xs))


