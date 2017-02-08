
module Theory.Examples.Haskell.FunctorSet.Base where 

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

open import Haskell
open import ProofIrrelevance

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
  
  total-contr : {x y : A} → ¬ (x ≤ y) → ¬ (y ≤ x) → ⊥
  total-contr {x} {y} x≤y y≤x with total x y
  total-contr ¬x≤y ¬y≤x | inj₁ x≤y = ¬x≤y x≤y
  total-contr ¬x≤y ¬y≤x | inj₂ y≤x = ¬y≤x y≤x

  sym-not-eq : {x y : A} → ¬ (x == y) → ¬ (y == x)
  sym-not-eq {x} {y} ¬x==y y==x = ¬x==y (sym-eq y==x)

  excluded-middle-ord : {x y : A} → ¬ (x ≤ y) → (y ≤ x)
  excluded-middle-ord {x} {y} ¬x≤y with total x y
  excluded-middle-ord {x} {y} ¬x≤y | inj₁ x≤y = ⊥-elim (¬x≤y x≤y)
  excluded-middle-ord {x} {y} ¬x≤y | inj₂ y≤x = y≤x

-------------------------------------------------------------------------------
-- Eq instance of lists in Haskell
-------------------------------------------------------------------------------

EqList : {A : Type} → EqInstance A → EqInstance (List A)
EqList {A} EqA = record 
  { _==_ = _==_
  ; isDecEquivalence = record 
    { isEquivalence = record 
      { refl = λ {xs} → lrefl {xs} 
      ; sym = λ {xs} {ys} → lsym {xs} {ys} 
      ; trans = λ {xs} {ys} {zs} → ltrans {xs} {ys} {zs}
      } 
    ; _≟_ = _=?=_
    }
  ; proof-irr-eq = λ {xs} {ys} → proof-irr {xs} {ys}
  } where
    _=A=_ = EqInstance._==_ EqA
    
    _==_ : List A → List A → Set lzero
    [] == [] = ⊤
    [] == (x ∷ ys) = ⊥
    (x ∷ xs) == [] = ⊥
    (x ∷ xs) == (y ∷ ys) = (x =A= y) × (xs == ys)
    
    lrefl : {xs : List A} → xs == xs
    lrefl {[]} = tt
    lrefl {x ∷ xs} = EqInstance.refl-eq EqA {x} , lrefl {xs}
    
    lsym : {xs ys : List A} → xs == ys → ys == xs
    lsym {[]} {[]} tt = tt
    lsym {[]} {x ∷ ys} ()
    lsym {x ∷ xs} {[]} ()
    lsym {x ∷ xs} {y ∷ ys} (x==y , xs==ys) = EqInstance.sym-eq EqA x==y , lsym {xs} {ys} xs==ys
    
    ltrans : {xs ys zs : List A} → xs == ys → ys == zs → xs == zs
    ltrans {[]} {[]} {[]} tt tt = tt
    ltrans {[]} {[]} {z ∷ zs} tt ()
    ltrans {[]} {y ∷ ys} () ys==zs
    ltrans {x ∷ xs} {[]} () ys==zs
    ltrans {x ∷ xs} {y ∷ ys} {[]} (x==y , xs==ys) ()
    ltrans {x ∷ xs} {y ∷ ys} {z ∷ zs} (x==y , xs==ys) (y==z , ys==zs) = EqInstance.trans-eq EqA x==y y==z , ltrans {xs} {ys} {zs} xs==ys ys==zs
    
    _=?=_ : (x y : List A) → Dec (x == y)
    [] =?= [] = yes tt
    [] =?= (x ∷ ys) = no (λ ())
    (x ∷ xs) =?= [] = no (λ ())
    (x ∷ xs) =?= (y ∷ ys) with EqInstance.dec-eq EqA x y | xs =?= ys
    (x ∷ xs) =?= (y ∷ ys) | yes x==y | yes xs==ys = yes (x==y , xs==ys)
    (x ∷ xs) =?= (y ∷ ys) | yes x==y | no ¬xs==ys = no (¬xs==ys ∘F proj₂)
    (x ∷ xs) =?= (y ∷ ys) | no ¬x==y | xs=?=ys    = no (¬x==y   ∘F proj₁)
    
    proof-irr : {xs ys : List A} → ProofIrrelevance (xs == ys)
    proof-irr {[]} {[]} tt tt = refl
    proof-irr {[]} {y ∷ ys} () eqYs
    proof-irr {x ∷ xs} {[]} () eqXs
    proof-irr {x ∷ xs} {y ∷ ys} (eqX , eqXs) (eqY , eqYs) with EqInstance.proof-irr-eq EqA eqX eqY | proof-irr {xs} {ys} eqXs eqYs
    proof-irr {x ∷ xs} {y ∷ ys} (eqX , eqXs) (.eqX , .eqXs) | refl | refl = refl

-------------------------------------------------------------------------------
-- Definition of predicates on lists
-------------------------------------------------------------------------------

IsSortedList : {ℓEq ℓOrd : Level} {A : Type} → OrdInstance {ℓEq} {ℓOrd} A → List A → Set ℓOrd
IsSortedList OrdA [] = Lift ⊤
IsSortedList OrdA (x ∷ []) = Lift ⊤
IsSortedList OrdA (x ∷ y ∷ xs) = (x ≤ y) × IsSortedList OrdA (y ∷ xs)
  where _≤_ = OrdInstance._≤_ OrdA

IsSortedList-forget-elem : {ℓEq ℓOrd : Level} {A : Type} 
                         → (OrdA : OrdInstance {ℓEq} {ℓOrd} A) → (x : A) → (xs : List A) 
                         → IsSortedList OrdA (x ∷ xs) → IsSortedList OrdA xs
IsSortedList-forget-elem OrdA x [] (lift tt) = lift tt
IsSortedList-forget-elem OrdA x (y ∷ xs) (x≤y , sorted) = sorted

IsSortedList-replace-elem : {ℓEq ℓOrd : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} {ℓOrd} A) 
                          → (z x : A) → (xs : List A) 
                          → OrdInstance._≤_ OrdA x z → IsSortedList OrdA (z ∷ xs) → IsSortedList OrdA (x ∷ xs)
IsSortedList-replace-elem OrdA z x [] x≤z (lift tt) = lift tt
IsSortedList-replace-elem OrdA z x (y ∷ xs) x≤z (z≤y , sorted) = OrdInstance.trans OrdA x≤z z≤y , sorted

InList : {ℓEq ℓOrd : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} {ℓOrd} A) → A → List A → Set ℓEq
InList {ℓEq} {ℓOrd} {A} OrdA x xs = Any (OrdInstance._==_ OrdA x) xs

¬InList-forget-elem : {ℓEq ℓOrd : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} {ℓOrd} A)
                    → (y x : A) (xs : List A)
                    → ¬ (InList OrdA y (x ∷ xs)) → ¬ (InList OrdA y xs)
¬InList-forget-elem OrdA y x xs ¬y∈x∷xs y∈xs = ¬y∈x∷xs (there y∈xs)

¬InList-prepend-elem : {ℓEq ℓOrd : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} {ℓOrd} A)
                              → (y x : A) → (xs : List A)
                              → ¬ (OrdInstance._==_ OrdA y x)
                              → ¬ InList OrdA y xs
                              → ¬ InList OrdA y (x ∷ xs)
¬InList-prepend-elem OrdA y x [] ¬y==x ¬y∈[] (here y==x) = ¬y==x y==x
¬InList-prepend-elem OrdA y x [] ¬y==x ¬y∈[] (there ())
¬InList-prepend-elem OrdA y x (z ∷ xs) ¬y==x ¬y∈z∷xs (here y==x) = ¬y==x y==x
¬InList-prepend-elem OrdA y x (z ∷ xs) ¬y==x ¬y∈z∷xs (there y∈z∷xs) = ¬y∈z∷xs y∈z∷xs

InList-forget-elem : {ℓEq ℓOrd : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} {ℓOrd} A)
                    → (y x : A) (xs : List A)
                    → ¬ (OrdInstance._==_ OrdA y x)
                    → InList OrdA y (x ∷ xs) → InList OrdA y xs
InList-forget-elem OrdA y x xs ¬y==x (here y==x) = ⊥-elim (¬y==x y==x)
InList-forget-elem OrdA y x xs ¬y==x (there y∈x∷xs) = y∈x∷xs

IsNoDupList : {ℓEq ℓOrd : Level} {A : Type} → OrdInstance {ℓEq} {ℓOrd} A → List A → Set (ℓEq ⊔ ℓOrd)
IsNoDupList OrdA [] = Lift ⊤
IsNoDupList OrdA (x ∷ xs) = ¬ (InList OrdA x xs) × IsNoDupList OrdA xs

-------------------------------------------------------------------------------
-- Proof irrelevancy for sorted and no duplicate list
-------------------------------------------------------------------------------

proof-irr-IsSortedList : {ℓEq ℓOrd : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} {ℓOrd} A) → (xs : List A) → ProofIrrelevance (IsSortedList OrdA xs)
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

private
  Obj : {ℓEq ℓOrd : Level} → Set (lsuc (ℓOrd ⊔ ℓEq))
  Obj {ℓEq} {ℓOrd} = Σ Type (OrdInstance {ℓEq} {ℓOrd})

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
