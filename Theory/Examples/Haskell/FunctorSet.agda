
-- TODO: Finish proofs
module Theory.Examples.Haskell.FunctorSet where

open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Level renaming ( suc to lsuc ; zero to lzero)
open import Data.Unit hiding ( _≤_ ; _≟_ ; total )
open import Data.Empty
open import Data.List
open import Data.List.Any hiding ( map )
open import Data.List.Properties using ( map-id ; map-compose )
open import Data.Nat renaming ( _>_ to _>ℕ_ ; _<_ to _<ℕ_ ; _≤_ to _≤ℕ_ ; _≥_ to _≥ℕ_ ) hiding ( _⊔_ ; _≟_ )
open import Data.Product hiding ( map )
open import Data.Sum hiding ( map )
open import Relation.Nullary
open import Relation.Binary using ( IsDecEquivalence ; IsEquivalence ; IsDecTotalOrder ; IsPreorder )
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning


open import Utilities renaming ( _∈_ to _∈'_ )
open import Congruence
open import Substitution
open import Haskell
open import Haskell.Functor renaming ( Functor to HFunctor )
open import Haskell.Applicative
open import Haskell.Monad
open import Haskell.Monad.List
open import ProofIrrelevance
open import Theory.Category
open import Theory.Subcategory
open import Theory.Functor
open import Theory.ConstrainedFunctor
open import Theory.Examples.Subcategory
open import Theory.Examples.Category
open import Theory.Examples.HaskellFunctorToFunctor

-------------------------------------------------------------------------------
-- Definition of Eq and Ord instances
-------------------------------------------------------------------------------

-- An 'Eq' instance in Haskell describes a decidable equivalence 
-- relation for its type.
record EqInstance {ℓ : Level} (A : Type) : Set (lsuc ℓ) where
  field
    _==_ : A → A → Set ℓ
    isDecEquivalence : IsDecEquivalence {A = A} _==_
    proof-irr-eq : {a b : A} → ProofIrrelevance (a == b)

  dec-eq = IsDecEquivalence._≟_ isDecEquivalence
    
  open Relation.Binary.IsDecEquivalence isDecEquivalence public renaming ( trans to trans-eq ; sym to sym-eq ; refl to refl-eq)

-- An 'Ord' instance in Haskell describes a decidable total ordering
-- relation for its type.
record OrdInstance {ℓEq ℓOrd : Level} (A : Type) : Set (lsuc ℓEq ⊔ lsuc ℓOrd) where
  field
    _≤_ : A → A → Set ℓOrd
    eqInstance : EqInstance {ℓ = ℓEq} A
    proof-irr-ord : {a b : A} → ProofIrrelevance (a ≤ b)
  
  open EqInstance eqInstance public using (_==_ ; dec-eq ; trans-eq ; sym-eq ; refl-eq ; proof-irr-eq)
  
  field
    isDecTotalOrder : IsDecTotalOrder {A = A} _==_ _≤_
  
  dec-ord = IsDecTotalOrder._≤?_ isDecTotalOrder
  
  open Relation.Binary.IsDecTotalOrder isDecTotalOrder public
  
  excluded-middle-ord : {x y : A} → ¬ (x ≤ y) → (y ≤ x)
  excluded-middle-ord {x} {y} ¬x≤y with total x y
  excluded-middle-ord {x} {y} ¬x≤y | inj₁ x≤y = ⊥-elim (¬x≤y x≤y)
  excluded-middle-ord {x} {y} ¬x≤y | inj₂ y≤x = y≤x

-------------------------------------------------------------------------------
-- Definition of predicates on lists
-------------------------------------------------------------------------------

IsSortedList : {ℓEq : Level} {A : Type} → OrdInstance {ℓEq} A → List A → Set lzero
IsSortedList OrdA [] = ⊤
IsSortedList OrdA (x ∷ []) = ⊤
IsSortedList OrdA (x ∷ y ∷ xs) = (x ≤ y) × IsSortedList OrdA (y ∷ xs)
  where _≤_ = OrdInstance._≤_ OrdA

InList : {ℓEq ℓOrd : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} {ℓOrd} A) → A → List A → Set ℓEq
InList {ℓEq} {ℓOrd} {A} OrdA x xs = Any (OrdInstance._==_ OrdA x) xs

IsNoDupList : {ℓEq ℓOrd : Level} {A : Type} → OrdInstance {ℓEq} {ℓOrd} A → List A → Set (ℓEq ⊔ ℓOrd)
IsNoDupList OrdA [] = Lift ⊤
IsNoDupList OrdA (x ∷ xs) = ¬ (InList OrdA x xs) × IsNoDupList OrdA xs

law-IsSortedList-forget-elem : {ℓEq : Level} {A : Type} 
                             → (OrdA : OrdInstance {ℓEq} A) → (x : A) → (xs : List A) 
                             → IsSortedList OrdA (x ∷ xs) → IsSortedList OrdA xs
law-IsSortedList-forget-elem OrdA x [] tt = tt
law-IsSortedList-forget-elem OrdA x (y ∷ xs) (x≤y , sorted) = sorted

proof-irr-IsSortedList : {ℓEq : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} A) → (xs : List A) → ProofIrrelevance (IsSortedList OrdA xs)
proof-irr-IsSortedList OrdA [] sortedX sortedY = refl
proof-irr-IsSortedList OrdA (x ∷ []) sortedX sortedY = refl
proof-irr-IsSortedList OrdA (x ∷ y ∷ xs) (x≤y , sortedX) (x≤y' , sortedY) with OrdInstance.proof-irr-ord OrdA x≤y x≤y'
proof-irr-IsSortedList OrdA (x ∷ y ∷ xs) (x≤y , sortedX) (.x≤y , sortedY) | refl = cong (λ X → x≤y , X) (proof-irr-IsSortedList OrdA (y ∷ xs) sortedX sortedY)


proof-irr-IsNoDupList : {ℓEq ℓOrd : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} {ℓOrd} A) → (xs : List A) → ProofIrrelevance (IsNoDupList OrdA xs)
proof-irr-IsNoDupList OrdA [] noDupX noDupY = refl
proof-irr-IsNoDupList OrdA (x ∷ xs) (¬x∈xs , noDupX) (¬x∈xs' , noDupY) with proof-irr-¬ ¬x∈xs ¬x∈xs'
proof-irr-IsNoDupList OrdA (x ∷ xs) (¬x∈xs , noDupX) (.¬x∈xs , noDupY) | refl = cong (λ X → ¬x∈xs , X) (proof-irr-IsNoDupList OrdA xs noDupX noDupY)

-------------------------------------------------------------------------------
-- Definition of ordered sets in form of lists
-------------------------------------------------------------------------------

data ListSet (A : Σ Type OrdInstance) : Type where
  listSet : (xs : List (proj₁ A)) → IsSortedList (proj₂ A) xs → IsNoDupList (proj₂ A) xs → ListSet A

eqListSet : {A : Type} → (OrdA : OrdInstance A) → (xs ys : List A)
          → (sortedX : IsSortedList OrdA xs) → (sortedY : IsSortedList OrdA ys)
          → (noDupX  : IsNoDupList OrdA xs)  → (noDupY : IsNoDupList OrdA ys)
          → xs ≡ ys
          → listSet xs sortedX noDupX ≡ listSet ys sortedY noDupY
eqListSet OrdA xs .xs sortedX sortedY noDupX noDupY refl with proof-irr-IsSortedList OrdA xs sortedX sortedY
eqListSet OrdA xs .xs sortedX .sortedX noDupX noDupY refl | refl with proof-irr-IsNoDupList OrdA xs noDupX noDupY
eqListSet OrdA xs .xs sortedX .sortedX noDupX .noDupX refl | refl | refl = refl

insert : {ℓEq ℓOrd : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} {ℓOrd} A) → A → List A → List A
insert OrdA x [] = x ∷ []
insert OrdA x (y ∷ ys) with OrdInstance.dec-ord OrdA x y
insert OrdA x (y ∷ ys) | yes x≤y = x ∷ y ∷ ys
insert OrdA x (y ∷ ys) | no ¬x≤y = y ∷ insert OrdA x ys

law-insert-preserve-sorted' : {ℓEq : Level }{A : Type}
                            → (OrdA : OrdInstance {ℓEq} A)
                            → (x z : A) → (xs : List A)
                            → IsSortedList OrdA (x ∷ xs)
                            → (IsSortedList OrdA (x ∷ insert OrdA z xs)) 
                            ⊎ (IsSortedList OrdA (z ∷ x ∷ xs))
law-insert-preserve-sorted' OrdA x z [] tt with OrdInstance.dec-ord OrdA x z 
law-insert-preserve-sorted' OrdA x z [] tt | yes x≤z = inj₁ $ x≤z , tt
law-insert-preserve-sorted' OrdA x z [] tt | no ¬x≤z with OrdInstance.total OrdA x z
law-insert-preserve-sorted' OrdA x z [] tt | no ¬x≤z | inj₁ x≤z = ⊥-elim (¬x≤z x≤z)
law-insert-preserve-sorted' OrdA x z [] tt | no ¬x≤z | inj₂ z≤x = inj₂ $ z≤x , tt
law-insert-preserve-sorted' OrdA x z (y ∷ xs) (x≤y , sorted[y∷xs]) with OrdInstance.dec-ord OrdA x z
law-insert-preserve-sorted' OrdA x z (y ∷ xs) (x≤y , sorted[y∷xs]) | yes x≤z with OrdInstance.dec-ord OrdA z y
law-insert-preserve-sorted' OrdA x z (y ∷ xs) (x≤y , sorted[y∷xs]) | yes x≤z | yes z≤y = inj₁ $ x≤z , z≤y , sorted[y∷xs]
law-insert-preserve-sorted' OrdA x z (y ∷ xs) (x≤y , sorted[y∷xs]) | yes x≤z | no ¬z≤y with law-insert-preserve-sorted' OrdA y z xs sorted[y∷xs]
law-insert-preserve-sorted' OrdA x z (y ∷ xs) (x≤y , sorted[y∷xs]) | yes x≤z | no ¬z≤y | inj₁ p = inj₁ $ x≤y , p
law-insert-preserve-sorted' OrdA x z (y ∷ xs) (x≤y , sorted[y∷xs]) | yes x≤z | no ¬z≤y | inj₂ (z≤y , _) = ⊥-elim (¬z≤y z≤y)
law-insert-preserve-sorted' OrdA x z (y ∷ xs) (x≤y , sorted[y∷xs]) | no ¬x≤z with OrdInstance.total OrdA x z
law-insert-preserve-sorted' OrdA x z (y ∷ xs) (x≤y , sorted[y∷xs]) | no ¬x≤z | inj₁ x≤z = ⊥-elim (¬x≤z x≤z)
law-insert-preserve-sorted' OrdA x z (y ∷ xs) (x≤y , sorted[y∷xs]) | no ¬x≤z | inj₂ z≤x = inj₂ $ z≤x , x≤y , sorted[y∷xs]

law-insert-preserve-sorted : {ℓEq : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} A) → (x : A) → (xs : List A) → IsSortedList OrdA xs → IsSortedList OrdA (insert OrdA x xs)
law-insert-preserve-sorted OrdA x [] tt = tt
law-insert-preserve-sorted OrdA x (y ∷ []) tt with OrdInstance.dec-ord OrdA x y 
law-insert-preserve-sorted OrdA x (y ∷ []) tt | yes x≤y = x≤y , tt
law-insert-preserve-sorted OrdA x (y ∷ []) tt | no ¬x≤y with OrdInstance.total OrdA y x
law-insert-preserve-sorted OrdA x (y ∷ []) tt | no ¬x≤y | inj₁ y≤x = y≤x , tt
law-insert-preserve-sorted OrdA x (y ∷ []) tt | no ¬x≤y | inj₂ x≤y = ⊥-elim (¬x≤y x≤y)
law-insert-preserve-sorted OrdA x (y ∷ z ∷ xs) (y≤z , sorted[z∷xs]) with OrdInstance.dec-ord OrdA x y
law-insert-preserve-sorted OrdA x (y ∷ z ∷ xs) (y≤z , sorted[z∷xs]) | yes x≤y = x≤y , y≤z , sorted[z∷xs]
law-insert-preserve-sorted OrdA x (y ∷ z ∷ xs) (y≤z , sorted[z∷xs]) | no ¬x≤y with OrdInstance.total OrdA x y
law-insert-preserve-sorted OrdA x (y ∷ z ∷ xs) (y≤z , sorted[z∷xs]) | no ¬x≤y | inj₁ x≤y = ⊥-elim (¬x≤y x≤y)
law-insert-preserve-sorted OrdA x (y ∷ z ∷ xs) (y≤z , sorted[z∷xs]) | no ¬x≤y | inj₂ y≤x with OrdInstance.dec-ord OrdA x z
law-insert-preserve-sorted OrdA x (y ∷ z ∷ xs) (y≤z , sorted[z∷xs]) | no ¬x≤y | inj₂ y≤x | yes x≤z = y≤x , x≤z , sorted[z∷xs]
law-insert-preserve-sorted OrdA x (y ∷ z ∷ xs) (y≤z , sorted[z∷xs]) | no ¬x≤y | inj₂ y≤x | no ¬x≤z with law-insert-preserve-sorted' OrdA z x xs sorted[z∷xs]
law-insert-preserve-sorted OrdA x (y ∷ z ∷ xs) (y≤z , sorted[z∷xs]) | no ¬x≤y | inj₂ y≤x | no ¬x≤z | inj₁ p = y≤z , p
law-insert-preserve-sorted OrdA x (y ∷ z ∷ xs) (y≤z , sorted[z∷xs]) | no ¬x≤y | inj₂ y≤x | no ¬x≤z | inj₂ (x≤z , _) = ⊥-elim (¬x≤z x≤z) 

sort : {ℓEq ℓOrd : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} {ℓOrd} A) → List A → List A
sort OrdA [] = []
sort OrdA (x ∷ xs) = insert OrdA x (sort OrdA xs)

law-sort-sorted : {ℓEq : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} A) → (xs : List A) → IsSortedList OrdA (sort OrdA xs)
law-sort-sorted OrdA [] = tt
law-sort-sorted OrdA (x ∷ []) = tt
law-sort-sorted OrdA (x ∷ y ∷ xs) = law-insert-preserve-sorted OrdA x
                                                               (insert OrdA y (sort OrdA xs))
                                                               (law-insert-preserve-sorted OrdA y (sort OrdA xs) (law-sort-sorted OrdA xs))


law-insert-smaller-in-front : {ℓEq : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} A)
                            → (y x : A) → (xs : List A)
                            → (OrdInstance._≤_ OrdA y x) → IsSortedList OrdA xs
                            → insert OrdA y (x ∷ xs) ≡ y ∷ (x ∷ xs)
law-insert-smaller-in-front OrdA y x xs y≤x sorted with OrdInstance.dec-ord OrdA y x
law-insert-smaller-in-front OrdA y x xs y≤x sorted | yes y≤x' = refl
law-insert-smaller-in-front OrdA y x xs y≤x sorted | no ¬y≤x = ⊥-elim (¬y≤x y≤x)

law-sort-preserve-sorted : {ℓEq : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} A) → (xs : List A) → IsSortedList OrdA xs → sort OrdA xs ≡ xs
law-sort-preserve-sorted OrdA [] sorted = refl
law-sort-preserve-sorted OrdA (y ∷ []) sorted = refl
law-sort-preserve-sorted OrdA (y ∷ x ∷ xs) (y≤x , sorted) with law-sort-preserve-sorted OrdA (x ∷ xs) sorted
law-sort-preserve-sorted OrdA (y ∷ x ∷ xs) (y≤x , sorted) | p =
  trans (cong (insert OrdA y) p)
        (law-insert-smaller-in-front OrdA y x xs y≤x (law-IsSortedList-forget-elem OrdA x xs sorted))


nub : {ℓEq ℓOrd : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} {ℓOrd} A) → List A → List A
nub OrdA [] = []
nub OrdA (x ∷ []) = x ∷ []
nub OrdA (y ∷ x ∷ xs) with OrdInstance.dec-eq OrdA y x
nub OrdA (y ∷ x ∷ xs) | yes y==x = nub OrdA (x ∷ xs)
nub OrdA (y ∷ x ∷ xs) | no ¬y==x = y ∷ nub OrdA (x ∷ xs)

law-nub-preserve-no-dup : {ℓEq ℓOrd : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} {ℓOrd} A) → (xs : List A) → IsNoDupList OrdA xs → nub OrdA xs ≡ xs
law-nub-preserve-no-dup OrdA [] noDup = refl
law-nub-preserve-no-dup OrdA (x ∷ []) noDup = refl
law-nub-preserve-no-dup OrdA (x ∷ y ∷ xs) noDup with OrdInstance.dec-eq OrdA x y
law-nub-preserve-no-dup OrdA (x ∷ y ∷ xs) (¬x∈y∷xs , noDup) | yes x==y = ⊥-elim (¬x∈y∷xs (here x==y))
law-nub-preserve-no-dup OrdA (x ∷ y ∷ xs) noDup | no ¬x==y = cong (λ XS → x ∷ XS) (law-nub-preserve-no-dup OrdA (y ∷ xs) (proj₂ noDup))

law-nub-no-dup : {ℓEq : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} A) → (xs : List A) → IsSortedList OrdA xs → IsNoDupList OrdA (nub OrdA xs)
law-nub-no-dup OrdA [] sorted = lift tt
law-nub-no-dup OrdA (x ∷ []) sorted = (λ ()) , lift tt
law-nub-no-dup OrdA (x ∷ y ∷ xs) sorted with OrdInstance.dec-eq OrdA x y
law-nub-no-dup OrdA (x ∷ y ∷ xs) sorted | yes x==y = law-nub-no-dup OrdA (y ∷ xs) (proj₂ sorted)
law-nub-no-dup OrdA (x ∷ y ∷ []) (x≤y , sorted) | no ¬x==y = x∈y∷[] , (λ ()) , lift tt
  where x∈y∷[] : ¬ InList OrdA x (y ∷ [])
        x∈y∷[] (here x==y) = ⊥-elim (¬x==y x==y)
        x∈y∷[] (there ())
law-nub-no-dup OrdA (x ∷ y ∷ z ∷ xs) (x≤y , y≤z ,  sorted) | no ¬x==y with law-nub-no-dup OrdA (y ∷ z ∷ xs) (y≤z , sorted)
law-nub-no-dup OrdA (x ∷ y ∷ z ∷ xs) (x≤y , y≤z ,  sorted) | no ¬x==y | p = f , p
  where f : ¬ InList OrdA x (nub OrdA (y ∷ z ∷ xs))
        f x∈nubxs with OrdInstance.dec-eq OrdA y z
        f x∈nubxs | yes y==z = {!!}
        f (here x==y) | no ¬y==z = ¬x==y x==y
        f (there x∈nubxs) | no ¬y==z = {!!}

¬x==y∧y==z→¬x==z : {ℓEq ℓOrd : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} {ℓOrd} A) → (x y z : A)
                 → (¬ (OrdInstance._==_ OrdA x y)) → OrdInstance._==_ OrdA y z → ¬ (OrdInstance._==_ OrdA x z)
¬x==y∧y==z→¬x==z OrdA x y z ¬x==y y==z x==z = ¬x==y (OrdInstance.trans-eq OrdA x==z (OrdInstance.sym-eq OrdA y==z))

x≤y∧y==z→x≤z : {ℓEq ℓOrd : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} {ℓOrd} A) → (x y z : A)
                 → OrdInstance._≤_ OrdA x y → OrdInstance._==_ OrdA y z → OrdInstance._≤_ OrdA x z
x≤y∧y==z→x≤z OrdA x y z x≤y y==z = (proj₁ (IsPreorder.∼-resp-≈ (OrdInstance.isPreorder OrdA))) y==z x≤y

law-nub-preserve-sorted' : {A : Type} → (OrdA : OrdInstance {lzero} A)
                         → (y x : A) (xs : List A)
                         → ¬ (OrdInstance._==_ OrdA y x) → (OrdInstance._≤_ OrdA y x)
                         → IsSortedList OrdA (nub OrdA (x ∷ xs)) → IsSortedList OrdA (y ∷ nub OrdA (x ∷ xs))
law-nub-preserve-sorted' OrdA y x [] ¬y==x y≤x sorted = y≤x , tt
law-nub-preserve-sorted' OrdA y x (z ∷ xs) ¬y==x y≤x sorted with OrdInstance.dec-eq OrdA x z
law-nub-preserve-sorted' OrdA y x (z ∷ xs) ¬y==x y≤x sorted | yes x==z = law-nub-preserve-sorted' OrdA y z xs (¬x==y∧y==z→¬x==z OrdA y x z ¬y==x x==z) (x≤y∧y==z→x≤z OrdA y x z y≤x x==z) sorted
law-nub-preserve-sorted' OrdA y x (z ∷ xs) ¬y==x y≤x sorted | no ¬x==z = y≤x , sorted

law-nub-preserve-sorted : {A : Type} → (OrdA : OrdInstance {lzero} A) → (xs : List A) → IsSortedList OrdA xs → IsSortedList OrdA (nub OrdA xs)
law-nub-preserve-sorted OrdA [] sorted = tt
law-nub-preserve-sorted OrdA (y ∷ []) sorted = tt
law-nub-preserve-sorted OrdA (y ∷ x ∷ xs) (y≤x , sorted) with law-nub-preserve-sorted OrdA (x ∷ xs) sorted
law-nub-preserve-sorted OrdA (y ∷ x ∷ xs) (y≤x , sorted) | p with OrdInstance.dec-eq OrdA y x
law-nub-preserve-sorted OrdA (y ∷ x ∷ xs) (y≤x , sorted) | p | yes y==x = p
law-nub-preserve-sorted OrdA (y ∷ x ∷ []) (y≤x , sorted) | p | no ¬y==x = y≤x , tt
law-nub-preserve-sorted OrdA (y ∷ x ∷ z ∷ xs) (y≤x , sorted) | p | no ¬y==x with OrdInstance.dec-eq OrdA x z
law-nub-preserve-sorted OrdA (y ∷ x ∷ z ∷ xs) (y≤x , sorted) | p | no ¬y==x | no ¬x==z = y≤x , p
law-nub-preserve-sorted OrdA (y ∷ x ∷ z ∷ xs) (y≤x , sorted) | p | no ¬y==x | yes x==z with OrdInstance.dec-eq OrdA y z
law-nub-preserve-sorted OrdA (y ∷ x ∷ z ∷ xs) (y≤x , sorted) | p | no ¬y==x | yes x==z | yes y==z = ⊥-elim (¬y==x (OrdInstance.trans-eq OrdA y==z (OrdInstance.sym-eq OrdA x==z)))
law-nub-preserve-sorted OrdA (y ∷ x ∷ z ∷ xs) (y≤x , x≤z , sorted) | p | no ¬y==x | yes x==z | no ¬y==z = law-nub-preserve-sorted' OrdA y z xs ¬y==z (OrdInstance.trans OrdA y≤x x≤z) p

law-sort-nub-interchange : {ℓEq : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} A)
                         → (xs : List A) → IsSortedList OrdA xs
                         → sort OrdA (nub OrdA xs) ≡ nub OrdA (sort {ℓEq} OrdA xs)
law-sort-nub-interchange OrdA xs sorted = {!!}

mkListSet : {α : Σ Type (OrdInstance {lzero})} → List (proj₁ α) → ListSet α
mkListSet {α , OrdA} xs = listSet (nub OrdA (sort OrdA xs))
                                  (law-nub-preserve-sorted OrdA (sort OrdA xs) (law-sort-sorted OrdA xs))
                                  (law-nub-no-dup OrdA (sort OrdA xs) (law-sort-sorted OrdA xs))

setmap : {α β : Σ Type OrdInstance} → (Σ (proj₁ α → proj₁ β) (λ _ → ⊤)) → ListSet α → ListSet β
setmap {α , OrdA} {β , OrdB} (f , tt) (listSet xs sorted noDup) = mkListSet (map f xs)

FunctorListSet : ConstrainedFunctor
FunctorListSet = record
  { ObjCts = ObjCts
  ; HomCts = HomCts
  ; _∘Ct_ = λ {α} {β} {γ} {f} {g} {α'} {β'} {γ'} → _∘Ct_ {α} {β} {γ} {f} {g} {α'} {β'} {γ'}
  ; ctId = λ {α} {α'} → ctId {α} {α'}
  ; ctAssoc = λ {α} {β} {γ} {δ} {α'} {β'} {γ'} {δ'} {f} {g} {h} → ctAssoc {α} {β} {γ} {δ} {α'} {β'} {γ'} {δ'} {f} {g} {h}
  ; ctIdR = λ {α} {β} {α'} {β'} {f} → ctIdR {α} {β} {α'} {β'} {f}
  ; ctIdL = λ {α} {β} {α'} {β'} {f} → ctIdL {α} {β} {α'} {β'} {f}
  ; F = F
  ; ctMap = setmap
  ; ctFuncId = ctFuncId
  ; ctFuncComp = ctFuncComp
  ; ctObjProofIrr = {!!}
  ; ctHomProofIrr = {!!}
  } where
    ObjCts : Type → Set (lsuc lzero)
    ObjCts = OrdInstance
    
    HomCts : {α β : Type} → ObjCts α → ObjCts β → (α → β) → Set lzero
    HomCts OrdA OrdB f = ⊤
    
    Obj : Set (lsuc lzero)
    Obj = Σ Type ObjCts

    Hom : Obj → Obj → Set lzero
    Hom α β = Σ (proj₁ α → proj₁ β) (HomCts (proj₂ α) (proj₂ β))
    
    F : Obj → Type
    F (α , OrdA) = ListSet (α , OrdA)
    
    _∘Ct_ : {α β γ : Type} {f : β → γ} {g : α → β} 
        → {α' : ObjCts α} {β' : ObjCts β} {γ' : ObjCts γ}
        → HomCts β' γ' f → HomCts α' β' g → HomCts α' γ' (f ∘F g)
    _∘Ct_ tt tt = tt
    
    ctId : {α : Type} {α' : ObjCts α} → HomCts α' α' idF
    ctId = tt
    
    ctAssoc : {α β γ δ : Type} 
            → {α' : ObjCts α} {β' : ObjCts β} {γ' : ObjCts γ} {δ' : ObjCts δ}
            → {f : α → β} {g : β → γ} {h : γ → δ}
            → (f' : HomCts α' β' f) (g' : HomCts β' γ' g) (h' : HomCts γ' δ' h)
            → _∘Ct_ {α} {γ} {δ} {h} {g ∘F f} {α'} {γ'} {δ'} h' (_∘Ct_ {α} {β} {γ} {g} {f} {α'} {β'} {γ'} g' f') 
            ≡ _∘Ct_ {α} {β} {δ} {h ∘F g} {f} {α'} {β'} {δ'} (_∘Ct_ {β} {γ} {δ} {h} {g} {β'} {γ'} {δ'} h' g') f'
    ctAssoc tt tt tt = refl
    
    ctIdR : {α β : Type} {α' : ObjCts α} {β' : ObjCts β} {f : α → β}
          → (f' : HomCts α' β' f) → _∘Ct_ {α} {β} {β} {idF} {f} {α'} {β'} {β'} (ctId {β} {β'}) f' ≡ f'
    ctIdR tt = refl
    
    ctIdL : {α β : Type} {α' : ObjCts α} {β' : ObjCts β} {f : α → β}
          → (f' : HomCts α' β' f) → _∘Ct_ {α} {α} {β} {f} {idF} {α'} {α'} {β'} f' (ctId {α} {α'}) ≡ f'
    ctIdL tt = refl
    
    ctFuncId : {α : Obj} → setmap {α = α} {α} (idF , ctId {proj₁ α} {proj₂ α}) ≡ idF
    ctFuncId {α , OrdA} = funExt helper
      where helper : (x : ListSet (α , OrdA)) → setmap (idF , ctId {α} {OrdA}) x ≡ idF x
            helper (listSet xs sorted noDup) = eqListSet OrdA (nub OrdA (sort OrdA (map idF xs))) xs
              (law-nub-preserve-sorted OrdA (sort OrdA (map idF xs)) (law-sort-sorted OrdA (map idF xs))) sorted
              (law-nub-no-dup OrdA (sort OrdA (map idF xs)) (law-sort-sorted OrdA (map idF xs))) noDup
              (trans (trans (cong (nub OrdA ∘F sort OrdA) (map-id xs))
                            (cong (nub OrdA) (law-sort-preserve-sorted OrdA xs sorted)))
                     (law-nub-preserve-no-dup OrdA xs noDup))

    ctFuncComp : {α β γ : Obj} {f : Hom α β} {g : Hom β γ}
               → setmap {α = α} {γ} (proj₁ g ∘F proj₁ f , _∘Ct_ {proj₁ α} {proj₁ β} {proj₁ γ} {proj₁ g} {proj₁ f} {proj₂ α} {proj₂ β} {proj₂ γ} (proj₂ g) (proj₂ f))
               ≡ setmap {α = β} {γ} g ∘F setmap f
    ctFuncComp {α , OrdA} {β , OrdB} {γ , OrdC} {f , tt} {g , tt} = funExt helper
      where
        
        helper : (x : ListSet (α , OrdA)) → setmap (g ∘F f , tt) x ≡ (setmap (g , tt) ∘F setmap (f , tt)) x
        helper (listSet xs sorted noDup) = begin
          setmap {α , OrdA} {γ , OrdC} (g ∘F f , tt) (listSet xs sorted noDup)
            ≡⟨ refl ⟩
          listSet (nub OrdC (sort OrdC (map (g ∘F f) xs)))
                  (law-nub-preserve-sorted OrdC (sort OrdC (map (g ∘F f) xs)) (law-sort-sorted OrdC (map (g ∘F f) xs)))
                  (law-nub-no-dup OrdC (sort OrdC (map (g ∘F f) xs)) (law-sort-sorted OrdC (map (g ∘F f) xs)))
            ≡⟨ eqListSet OrdC (nub OrdC (sort OrdC (map (g ∘F f) xs))) (nub OrdC (sort OrdC (map g (nub OrdB (sort OrdB (map f xs))))))
                         (law-nub-preserve-sorted OrdC (sort OrdC (map (g ∘F f) xs)) (law-sort-sorted OrdC (map (g ∘F f) xs)))
                         (law-nub-preserve-sorted OrdC (sort OrdC (map g (nub OrdB (sort OrdB (map f xs))))) (law-sort-sorted OrdC (map g (nub OrdB (sort OrdB (map f xs))))))
                         (law-nub-no-dup OrdC (sort OrdC (map (g ∘F f) xs)) (law-sort-sorted OrdC (map (g ∘F f) xs)))
                         (law-nub-no-dup OrdC (sort OrdC (map g (nub OrdB (sort OrdB (map f xs))))) (law-sort-sorted OrdC (map g (nub OrdB (sort OrdB (map f xs))))))
                         helper' ⟩
          listSet (nub OrdC (sort OrdC (map g (nub OrdB (sort OrdB (map f xs))))))
                  (law-nub-preserve-sorted OrdC (sort OrdC (map g (nub OrdB (sort OrdB (map f xs))))) (law-sort-sorted OrdC (map g (nub OrdB (sort OrdB (map f xs))))))
                  (law-nub-no-dup OrdC (sort OrdC (map g (nub OrdB (sort OrdB (map f xs))))) (law-sort-sorted OrdC (map g (nub OrdB (sort OrdB (map f xs))))))
            ≡⟨ refl ⟩
          setmap {β , OrdB} {γ , OrdC} (g , tt) (setmap {α , OrdA} {β , OrdB} (f , tt) (listSet xs sorted noDup))
            ≡⟨ refl ⟩
          (setmap {β , OrdB} {γ , OrdC} (g , tt) ∘F setmap {α , OrdA} {β , OrdB} (f , tt)) (listSet xs sorted noDup) ∎
            where
              helper' : nub OrdC (sort OrdC (map (g ∘F f) xs)) ≡ nub OrdC (sort OrdC (map g (nub OrdB (sort OrdB (map f xs)))))
              helper' = begin
                nub OrdC (sort OrdC (map (g ∘F f) xs))
                  ≡⟨ cong (nub OrdC ∘F sort OrdC) (map-compose xs) ⟩
                nub OrdC (sort OrdC (map g (map f xs)))
                  ≡⟨ {!!} ⟩
                nub OrdC (nub OrdC (sort OrdC (sort OrdC (map g (map f xs)))))
                  ≡⟨ {!!} ⟩
                nub OrdC (sort OrdC (nub OrdC (map g (sort OrdB (map f xs)))))
                  ≡⟨ {!!} ⟩
                nub OrdC (sort OrdC (nub OrdC (map g (sort OrdB (map f xs)))))
                  ≡⟨ {!!} ⟩
                nub OrdC (sort OrdC (map g (nub OrdB (sort OrdB (map f xs))))) ∎
