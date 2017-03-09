
open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Level renaming ( suc to lsuc ; zero to lzero)
open import Data.Unit hiding ( _≤_ ; _≟_ ; total )
open import Data.Empty
open import Data.List
open import Data.List.Any hiding ( map )
open import Data.Product hiding ( map )
open import Data.Sum hiding ( map )
open import Relation.Nullary
open import Relation.Binary using ( IsDecEquivalence ; IsEquivalence ; IsDecTotalOrder ; IsPreorder )
open import Relation.Binary.PropositionalEquality

open import Extensionality
open import Utilities
open import Haskell
open import ProofIrrelevance

import Theory.Examples.Haskell.FunctorSet.Base as B
open B.ListProperties
open import Theory.Examples.Haskell.FunctorSet.Sort
open import Theory.Examples.Haskell.FunctorSet.Nub
open import Theory.Examples.Haskell.FunctorSet.NubAndSort

module Theory.Examples.Haskell.FunctorSet.Map {ℓEqA ℓOrdA ℓEqB ℓOrdB : Level} {A B : Type} (OrdA : B.OrdInstance {ℓEqA} {ℓOrdA} A) (OrdB : B.OrdInstance {ℓEqB} {ℓOrdB} B) where
  
open ≡-Reasoning
open B.OrdInstance

private
  open module M = B.Monotonic OrdA OrdB
  _=A=_ = _==_ OrdA
  _=B=_ = _==_ OrdB

map-preserves-sorted : (f : A → B) → Monotonic f → (xs : List A) 
                     → (IsSortedList OrdA xs) → (IsSortedList OrdB (map f xs))
map-preserves-sorted f mon-f [] sorted = lift tt
map-preserves-sorted f mon-f (x ∷ []) sorted = lift tt
map-preserves-sorted f mon-f (x ∷ y ∷ xs) (x≤y , sorted) = mon-f x y x≤y , map-preserves-sorted f mon-f (y ∷ xs) sorted
{-
map-preserves-sorted-struct-eq : (f : A → B)
                               → IsStructuralEquality OrdA → IsStructuralEquality Ord
                               → (xs : List A)
                               → IsSortedList OrdA xs → IsSortedList OrdB (map f xs)
map-preserves-sorted-struct-eq f struct-eqA
-}
struct-eq-preserves-equality : (f : A → B)
                             → IsStructuralEquality OrdA
                             → (a b : A) → (a =A= b) → (f a =B= f b)
struct-eq-preserves-equality f struct-eqA a b a=A=b with struct-eqA a b a=A=b
struct-eq-preserves-equality f struct-eqA a .a a=A=b | refl = refl-eq OrdB {f a}

remove∘map∘remove≡remove∘map : (f : A → B) → (a : A) → (as : List A)
                             → IsStructuralEquality OrdA
                             → remove OrdB (f a) (map f (remove OrdA a as)) ≡ remove OrdB (f a) (map f as)
remove∘map∘remove≡remove∘map f a [] struct-eqA = refl
remove∘map∘remove≡remove∘map f a (x ∷ xs) struct-eqA with dec-eq OrdA a x
remove∘map∘remove≡remove∘map f a (x ∷ xs) struct-eqA | yes a=x with dec-eq OrdB (f a) (f x)
remove∘map∘remove≡remove∘map f a (x ∷ xs) struct-eqA | yes a=x | yes fa=fx = remove∘map∘remove≡remove∘map f a xs struct-eqA
remove∘map∘remove≡remove∘map f a (x ∷ xs) struct-eqA | yes a=x | no ¬fa=fx = ⊥-elim (¬fa=fx (struct-eq-preserves-equality f struct-eqA a x a=x))
remove∘map∘remove≡remove∘map f a (x ∷ xs) struct-eqA | no ¬a=x with dec-eq OrdB (f a) (f x)
remove∘map∘remove≡remove∘map f a (x ∷ xs) struct-eqA | no ¬a=x | yes fa=fx = remove∘map∘remove≡remove∘map f a xs struct-eqA
remove∘map∘remove≡remove∘map f a (x ∷ xs) struct-eqA | no ¬a=x | no ¬fa=fx = cong (_∷_ (f x)) (remove∘map∘remove≡remove∘map f a xs struct-eqA)

nub∘map∘nub≡nub∘map : (f : A → B) → (as : List A)
                    → IsStructuralEquality OrdA
                    → nub OrdB (map f (nub OrdA as)) ≡ nub OrdB (map f as)
nub∘map∘nub≡nub∘map  f [] struct-eqA = refl
nub∘map∘nub≡nub∘map f (a ∷ as) struct-eqA = begin
  nub OrdB (map f (nub OrdA (a ∷ as)))
    ≡⟨⟩
  f a ∷ remove OrdB (f a) (nub OrdB (map f (remove OrdA a (nub OrdA as))))
    ≡⟨ cong (_∷_ (f a)) (sym $ nub-remove-interchange OrdB (f a) (map f (remove OrdA a (nub OrdA as)))) ⟩
  f a ∷ nub OrdB (remove OrdB (f a) (map f (remove OrdA a (nub OrdA as))))
    ≡⟨ cong (λ P → f a ∷ nub OrdB P) (remove∘map∘remove≡remove∘map f a (nub OrdA as) struct-eqA) ⟩
  f a ∷ nub OrdB (remove OrdB (f a) (map f (nub OrdA as)))
    ≡⟨ cong (_∷_ (f a)) (nub-remove-interchange OrdB (f a) (map f (nub OrdA as))) ⟩
  f a ∷ remove OrdB (f a) (nub OrdB (map f (nub OrdA as)))
    ≡⟨ cong (λ P → f a ∷ remove OrdB (f a) P) (nub∘map∘nub≡nub∘map f as struct-eqA) ⟩
  f a ∷ remove OrdB (f a) (nub OrdB (map f as))
    ≡⟨⟩
  nub OrdB (map f (a ∷ as)) ∎

sort∘insert∘map≡sort∘map∘insert : (f : A → B) → (a : A) → (as : List A)
                                → IsStructuralEquality OrdB
                                → sort OrdB (insert OrdB (f a) (map f as)) ≡ sort OrdB (map f (insert OrdA a as))
sort∘insert∘map≡sort∘map∘insert f a [] struct-eqB = refl
sort∘insert∘map≡sort∘map∘insert f a (x ∷ xs) struct-eqB with dec-ord OrdA a x
sort∘insert∘map≡sort∘map∘insert f a (x ∷ xs) struct-eqB | yes a≤x with dec-ord OrdB (f a) (f x)
sort∘insert∘map≡sort∘map∘insert f a (x ∷ xs) struct-eqB | yes a≤x | yes fa≤fx = refl
sort∘insert∘map≡sort∘map∘insert f a (x ∷ xs) struct-eqB | yes a≤x | no ¬fa≤fx with dec-eq OrdB (f a) (f x)
sort∘insert∘map≡sort∘map∘insert f a (x ∷ xs) struct-eqB | yes a≤x | no ¬fa≤fx | yes fa=fx = ⊥-elim (¬fa≤fx (proj₁ (antisym-ord' OrdB fa=fx)))
sort∘insert∘map≡sort∘map∘insert f a (x ∷ xs) struct-eqB | yes a≤x | no ¬fa≤fx | no ¬fa=fx = begin
  insert OrdB (f x) (sort OrdB (insert OrdB (f a) (map f xs)))
    ≡⟨ cong (insert OrdB (f x)) (sort-insert-interchange OrdB (f a) (map f xs)) ⟩
  insert OrdB (f x) (insert OrdB (f a) (sort OrdB (map f xs)))
    ≡⟨ insert-interchange OrdB (f x) (f a) (sort OrdB (map f xs)) (sym-not-eq OrdB ¬fa=fx) ⟩
  insert OrdB (f a) (insert OrdB (f x) (sort OrdB (map f xs))) ∎
sort∘insert∘map≡sort∘map∘insert f a (x ∷ xs) struct-eqB | no ¬a≤x with dec-ord OrdB (f a) (f x)
sort∘insert∘map≡sort∘map∘insert f a (x ∷ xs) struct-eqB | no ¬a≤x | yes fa≤fx = begin
  insert OrdB (f a) (insert OrdB (f x) (sort OrdB (map f xs)))
    ≡⟨ cong (insert OrdB (f a)) (sym (sort-insert-interchange OrdB (f x) (map f xs))) ⟩
  insert OrdB (f a) (sort OrdB (insert OrdB (f x) (map f xs)))
    ≡⟨ sym (sort-insert-interchange OrdB (f a) (insert OrdB (f x) (map f xs))) ⟩
  sort OrdB (insert OrdB (f a) (insert OrdB (f x) (map f xs)))
    ≡⟨ cong (sort OrdB) (insert-interchange-struct-eq OrdB (f a) (f x) (map f xs) struct-eqB) ⟩
  sort OrdB (insert OrdB (f x) (insert OrdB (f a) (map f xs)))
    ≡⟨ sort-insert-interchange OrdB (f x) (insert OrdB (f a) (map f xs)) ⟩
  insert OrdB (f x) (sort OrdB (insert OrdB (f a) (map f xs)))
    ≡⟨ cong (insert OrdB (f x)) (sort∘insert∘map≡sort∘map∘insert f a xs struct-eqB) ⟩
  insert OrdB (f x) (sort OrdB (map f (insert OrdA a xs))) ∎
sort∘insert∘map≡sort∘map∘insert f a (x ∷ xs) struct-eqB | no ¬a≤x | no ¬fa≤fx 
  = cong (insert OrdB (f x)) (sort∘insert∘map≡sort∘map∘insert f a xs struct-eqB)

sort∘map∘sort≡sort∘map : (f : A → B) → (as : List A)
                       → IsStructuralEquality OrdB
                       → sort OrdB (map f (sort OrdA as)) ≡ sort OrdB (map f as)
sort∘map∘sort≡sort∘map f [] struct-eqB = refl
sort∘map∘sort≡sort∘map f (a ∷ as) struct-eqB = begin
  sort OrdB (map f (insert OrdA a (sort OrdA as)))
    ≡⟨ sym (sort∘insert∘map≡sort∘map∘insert f a (sort OrdA as) struct-eqB) ⟩
  sort OrdB (insert OrdB (f a) (map f (sort OrdA as)))
    ≡⟨ sort-insert-interchange OrdB (f a) (map f (sort OrdA as)) ⟩
  insert OrdB (f a) (sort OrdB (map f (sort OrdA as)))
    ≡⟨ cong (insert OrdB (f a)) (sort∘map∘sort≡sort∘map f as struct-eqB) ⟩
  insert OrdB (f a) (sort OrdB (map f as)) ∎
{-
nub∘sort∘map∘sort∘nub≡nub∘sort∘map : (f : A → B) → (as : List A)
                                   → IsStructuralEquality OrdA
                                   → IsStructuralEquality OrdB
                                   → nub OrdB (sort OrdB (map f (sort OrdA (nub OrdA as)))) ≡ nub OrdB (sort OrdB (map f as))
nub∘sort∘map∘sort∘nub≡nub∘sort∘map f as struct-eqA struct-eqB = {!!}
-}
