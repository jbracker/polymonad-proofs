
open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Level renaming ( suc to lsuc ; zero to lzero)
open import Data.Unit hiding ( _≤_ ; _≟_ ; total )
open import Data.Empty
open import Data.List hiding ( map )
open import Data.List.Any hiding ( map )
open import Data.Product hiding ( map )
open import Data.Sum hiding ( map )
open import Relation.Nullary
open import Relation.Binary using ( IsDecEquivalence ; IsEquivalence ; IsDecTotalOrder ; IsPreorder )
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Utilities
open import Haskell
open import ProofIrrelevance

import Theory.Examples.Haskell.FunctorSet.Base as B

open import Theory.Examples.Haskell.FunctorSet.Base using ( OrdInstance )

module Theory.Examples.Haskell.FunctorSet.NubAndSort {ℓEq ℓOrd : Level} {A : Type} (OrdA : OrdInstance {ℓEq} {ℓOrd} A) where
  
private
  import Theory.Examples.Haskell.FunctorSet.Sort as S
  import Theory.Examples.Haskell.FunctorSet.Nub as N
  
  open module ListPropertiesA = B.ListProperties OrdA
  open module SortA = S OrdA
  open module NubA = N OrdA
  open B.OrdInstance OrdA
  
insert-remove-preserves-no-dup : (x : A) → (xs : List A) 
                               → IsNoDupList xs → IsNoDupList (insert x $ remove x xs)
insert-remove-preserves-no-dup y [] (lift tt) = (λ ()) , lift tt
insert-remove-preserves-no-dup y (x ∷ xs) (¬x∈xs , noDup) with dec-eq y x
insert-remove-preserves-no-dup y (x ∷ xs) (¬x∈xs , noDup) | yes y==x = insert-remove-preserves-no-dup y xs noDup
insert-remove-preserves-no-dup y (x ∷ xs) (¬x∈xs , noDup) | no ¬y==x with dec-ord y x
insert-remove-preserves-no-dup y (x ∷ xs) (¬x∈xs , noDup) | no ¬y==x | yes y≤x 
  = ¬InList-prepend-elem y x (remove y xs) ¬y==x (remove-produces-missing-elem y xs) 
  , remove-preserves-missing-elem y x xs ¬x∈xs 
  , remove-preserves-no-dup y xs noDup
insert-remove-preserves-no-dup y (x ∷ xs) (¬x∈xs , noDup) | no ¬y==x | no ¬y≤x 
  = insert-preserves-missing-elem x y (remove y xs) (sym-not-eq ¬y==x) (remove-preserves-missing-elem y x xs ¬x∈xs) 
  , insert-remove-preserves-no-dup y xs noDup
  
insert-remove-elim : (x : A) → (xs ys : List A)
                   → xs ≡ ys
                   → IsSortedList (x ∷ xs) → IsNoDupList (x ∷ xs)
                   → insert x (remove x xs) ≡ x ∷ ys
insert-remove-elim y [] .[] refl (lift tt) (¬y∈[] , lift tt) = refl
insert-remove-elim y (x ∷ xs) ._ refl (y≤x , sorted) (¬y∈x∷xs , ¬x∈xs , noDup) with dec-eq y x
insert-remove-elim y (x ∷ xs) ._ refl (y≤x , sorted) (¬y∈x∷xs , ¬x∈xs , noDup) | yes y==x = ⊥-elim (¬y∈x∷xs (here y==x))
insert-remove-elim y (x ∷ xs) ._ refl (y≤x , sorted) (¬y∈x∷xs , ¬x∈xs , noDup) | no ¬y==x with dec-ord y x
insert-remove-elim y (x ∷ xs) ._ refl (y≤x , sorted) (¬y∈x∷xs , ¬x∈xs , noDup) | no ¬y==x | yes _ 
  = cong (λ X → y ∷ x ∷ X) (remove-removing-missing-elem y xs (¬InList-forget-elem y x xs ¬y∈x∷xs))
insert-remove-elim y (x ∷ xs) ._ refl (y≤x , sorted) (¬y∈x∷xs , ¬x∈xs , noDup) | no ¬y==x | no ¬y≤x = ⊥-elim (¬y≤x y≤x)
  
nub∘insert≡insert∘remove∘nub : (x : A) → (xs : List A)
                             → IsSortedList (x ∷ xs)
                             → nub (insert x xs) ≡ insert x (remove x (nub xs))
nub∘insert≡insert∘remove∘nub x [] sorted = refl
nub∘insert≡insert∘remove∘nub x (y ∷ xs) (x≤y , sorted) with dec-ord x y
nub∘insert≡insert∘remove∘nub x (y ∷ xs) (x≤y , sorted) | yes _ with dec-eq x y
nub∘insert≡insert∘remove∘nub x (y ∷ xs) (x≤y , sorted) | yes _ | yes x==y 
  = sym (insert-smallest-in-front x 
        (remove x (remove y (nub xs))) 
          (remove-preserves-sorted' x x (remove y (nub xs)) 
            (remove-preserves-sorted' y x (nub xs) 
              (nub-preserves-sorted' x xs 
                (IsSortedList-replace-elem y x xs x≤y sorted)))))
nub∘insert≡insert∘remove∘nub x (y ∷ xs) (x≤y , sorted) | yes _ | no ¬x==y with dec-ord x y
nub∘insert≡insert∘remove∘nub x (y ∷ xs) (x≤y , sorted) | yes _ | no ¬x==y | yes _ = refl
nub∘insert≡insert∘remove∘nub x (y ∷ xs) (x≤y , sorted) | yes _ | no ¬x==y | no ¬x≤y = ⊥-elim (¬x≤y x≤y)
nub∘insert≡insert∘remove∘nub x (y ∷ xs) (x≤y , sorted) | no ¬x≤y = ⊥-elim (¬x≤y x≤y)

sort∘nub≡nub∘sort : (xs : List A) → IsSortedList xs
                  → sort (nub xs) ≡ nub (sort xs)
sort∘nub≡nub∘sort [] _ = refl
sort∘nub≡nub∘sort (x ∷ xs) sorted = begin
  insert x (sort (remove x (nub xs)))
    ≡⟨ cong (insert x) (sort-sorting-sorted (remove x (nub xs)) (remove-preserves-sorted x (nub xs) (nub-preserves-sorted xs (IsSortedList-forget-elem x xs sorted)))) ⟩
  insert x (remove x (nub xs))
    ≡⟨ cong (insert x) (sym $ nub-remove-interchange x xs) ⟩
  insert x (nub (remove x xs))
    ≡⟨ cong (insert x) (nub-remove-interchange x xs) ⟩
  insert x (remove x (nub xs))
    ≡⟨ sym (nub∘insert≡insert∘remove∘nub x xs sorted) ⟩
  nub (insert x xs)
    ≡⟨ cong (nub ∘F insert x) (sym (sort-sorting-sorted xs (IsSortedList-forget-elem x xs sorted))) ⟩
  nub (insert x (sort xs)) ∎

