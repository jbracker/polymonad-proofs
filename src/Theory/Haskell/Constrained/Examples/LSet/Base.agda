
open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Level

open import Data.Unit hiding ( _≤_ ; _≟_ ; total )
open import Data.Empty
open import Data.List
open import Data.List.All hiding ( map )
open import Data.Product hiding ( map )
open import Data.Sum hiding ( map )

open import Relation.Nullary
open import Relation.Binary using ( IsDecEquivalence ; IsEquivalence ; IsDecTotalOrder ; IsPreorder ; IsPartialOrder )
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality using ( refl ; ≡-to-≅ )

open import Equality
open import Extensionality
open import ProofIrrelevance

module Theory.Haskell.Constrained.Examples.LSet.Base {ℓ : Level} where 

private
  Type = Set ℓ

-------------------------------------------------------------------------------
-- Definition of Eq and Ord instances
-------------------------------------------------------------------------------

-- An 'Eq' instance in Haskell describes a decidable equivalence 
-- relation for its type.
record EqInstance {ℓEq : Level} (A : Type) : Set (suc (ℓ ⊔ ℓEq)) where
  field
    _==_ : A → A → Set ℓEq
    isDecEquivalence : IsDecEquivalence {A = A} _==_
    proof-irr-eq : {a b : A} → ProofIrrelevance (a == b)

  dec-eq = IsDecEquivalence._≟_ isDecEquivalence
    
  open Relation.Binary.IsDecEquivalence isDecEquivalence public renaming ( trans to trans-eq ; sym to sym-eq ; refl to refl-eq)

-- An 'Ord' instance in Haskell describes a decidable total ordering
-- relation for its type.
record OrdInstance {ℓEq ℓOrd : Level} (A : Type) : Set (suc (ℓ ⊔ ℓEq ⊔ ℓOrd)) where
  field
    _≤_ : A → A → Set ℓOrd
    eqInstance : EqInstance {ℓEq = ℓEq} A
    proof-irr-ord : {a b : A} → ProofIrrelevance (a ≤ b)
  
  open EqInstance eqInstance public using (_==_ ; dec-eq ; trans-eq ; sym-eq ; refl-eq ; proof-irr-eq)
  
  field
    isDecTotalOrder : IsDecTotalOrder {A = A} _==_ _≤_
  
  dec-ord = IsDecTotalOrder._≤?_ isDecTotalOrder
  
  open Relation.Binary.IsDecTotalOrder isDecTotalOrder public renaming ( trans to trans-ord ; antisym to antisym-ord ; refl to refl-ord )
  
  abstract
    total-contr : {x y : A} → ¬ (x ≤ y) → ¬ (y ≤ x) → ⊥
    total-contr {x} {y} ¬x≤y ¬y≤x with total x y
    total-contr ¬x≤y ¬y≤x | inj₁ x≤y = ¬x≤y x≤y
    total-contr ¬x≤y ¬y≤x | inj₂ y≤x = ¬y≤x y≤x
  
  abstract
    sym-not-eq : {x y : A} → ¬ (x == y) → ¬ (y == x)
    sym-not-eq {x} {y} ¬x==y y==x = ¬x==y (sym-eq y==x)
  
  abstract
    eq-ord-comp : {x y z : A} → x == y → y ≤ z → x ≤ z
    eq-ord-comp x==y y≤z = proj₂ (IsPartialOrder.≤-resp-≈ isPartialOrder) (sym-eq x==y) y≤z
  
  abstract
    ord-eq-comp : {x y z : A} → x ≤ y → y == z → x ≤ z
    ord-eq-comp x≤y y==z = proj₁ (IsPartialOrder.≤-resp-≈ isPartialOrder) y==z x≤y

  abstract
    eq-contr : {x y : A} → x == y → (¬ (x ≤ y) ⊎ ¬ (y ≤ x)) → ⊥
    eq-contr {x} {y} x==y (inj₁ ¬x≤y) with total x y
    eq-contr x==y (inj₁ ¬x≤y) | inj₁ x≤y = ¬x≤y x≤y
    eq-contr x==y (inj₁ ¬x≤y) | inj₂ y≤x = ¬x≤y (eq-ord-comp x==y (ord-eq-comp y≤x x==y))
    eq-contr {x} {y} x==y (inj₂ ¬y≤x) with total x y
    eq-contr x==y (inj₂ ¬y≤x) | inj₁ x≤y = ¬y≤x (ord-eq-comp (eq-ord-comp (sym-eq x==y) x≤y) (sym-eq x==y))
    eq-contr x==y (inj₂ ¬y≤x) | inj₂ y≤x = ¬y≤x y≤x

  abstract
    excluded-middle-ord : {x y : A} → ¬ (x ≤ y) → (y ≤ x)
    excluded-middle-ord {x} {y} ¬x≤y with total x y
    excluded-middle-ord {x} {y} ¬x≤y | inj₁ x≤y = ⊥-elim (¬x≤y x≤y)
    excluded-middle-ord {x} {y} ¬x≤y | inj₂ y≤x = y≤x
  
  abstract
    excluded-middle-ord' : {x y : A} → ¬ (x == y) → x ≤ y → ¬ (y ≤ x)
    excluded-middle-ord' {x} {y} ¬x==y x≤y y≤x = ¬x==y (antisym-ord x≤y y≤x)
  
  abstract
    antisym-ord' : {x y : A} → x == y → (x ≤ y) × (y ≤ x)
    antisym-ord' {x} {y} x==y with dec-ord x y | dec-ord y x
    antisym-ord' x==y | yes x≤y | yes y≤x = x≤y , y≤x
    antisym-ord' x==y | yes x≤y | no ¬y≤x = ⊥-elim (eq-contr x==y (inj₂ ¬y≤x))
    antisym-ord' x==y | no ¬x≤y | yes y≤x = ⊥-elim (eq-contr x==y (inj₁ ¬x≤y))
    antisym-ord' x==y | no ¬x≤y | no ¬y≤x = ⊥-elim (¬x≤y (excluded-middle-ord ¬y≤x))
  
  abstract
    ord-not-eq : {x y : A} → x ≤ y → ¬ (y ≤ x) → ¬ (x == y)
    ord-not-eq x≤y ¬y≤x x==y = ¬y≤x (eq-ord-comp (sym-eq x==y) (ord-eq-comp x≤y (sym-eq x==y)))

-------------------------------------------------------------------------------
-- Definition of predicates on lists
-------------------------------------------------------------------------------

private
  module StructuralEquality {ℓEq : Level} {A : Type} (EqA : EqInstance {ℓEq} A) where
    open EqInstance EqA
    
    IsStructuralEquality : Set (ℓ ⊔ ℓEq)
    IsStructuralEquality = (a b : A) → (a == b) → (a ≡ b)

    proof-irr-IsStructuralEquality : ProofIrrelevance IsStructuralEquality
    proof-irr-IsStructuralEquality struct-eq₀ struct-eq₁ 
      = fun-ext 
      $ λ a → fun-ext 
      $ λ b → fun-ext 
      $ λ a=b → proof-irr-≡ (struct-eq₀ a b a=b) (struct-eq₁ a b a=b)

open StructuralEquality public
    


module ListProperties {ℓEq ℓOrd : Level} {A : Type} (OrdA : OrdInstance {ℓEq} {ℓOrd} A) where
  
  open OrdInstance OrdA

  IsSortedList : List A → Set ℓOrd
  IsSortedList [] = Lift ⊤
  IsSortedList (x ∷ []) = Lift ⊤
  IsSortedList (x ∷ y ∷ xs) = (x ≤ y) × IsSortedList (y ∷ xs)

  IsSortedList-forget-elem : (x : A) → (xs : List A) → IsSortedList (x ∷ xs) → IsSortedList xs
  IsSortedList-forget-elem x [] (lift tt) = lift tt
  IsSortedList-forget-elem x (y ∷ xs) (x≤y , sorted) = sorted

  IsSortedList-replace-elem : (z x : A) → (xs : List A) 
                            → OrdInstance._≤_ OrdA x z → IsSortedList (z ∷ xs) → IsSortedList (x ∷ xs)
  IsSortedList-replace-elem z x [] x≤z (lift tt) = lift tt
  IsSortedList-replace-elem z x (y ∷ xs) x≤z (z≤y , sorted) = trans-ord x≤z z≤y , sorted

  IsSortedNoDupList : List A → Set (ℓ ⊔ ℓEq ⊔ ℓOrd)
  IsSortedNoDupList [] = Lift ⊤
  IsSortedNoDupList (x ∷ xs) = All (λ y → (x ≤ y) × ¬ (x == y)) xs × IsSortedNoDupList xs

  IsSortedNoDupList-forget : {x : A} {xs : List A} → IsSortedNoDupList (x ∷ xs) → IsSortedNoDupList xs
  IsSortedNoDupList-forget {x} {xs} (_ , sorted) = sorted
  
  IsSortedNoDupList-replace-eq' : {x y : A} {zs : List A} → x == y → All (λ z → x ≤ z × ¬ x == z) zs → All (λ z → y ≤ z × ¬ y == z) zs
  IsSortedNoDupList-replace-eq' x=y [] = []
  IsSortedNoDupList-replace-eq' x=y ((x≤z , x≠z) ∷ sorted)
    = (eq-ord-comp (sym-eq x=y) x≤z , (λ y=z → x≠z (trans-eq x=y y=z))) ∷ IsSortedNoDupList-replace-eq' x=y sorted
  
  IsSortedNoDupList-replace-eq : {x y : A} {zs : List A} → x == y → IsSortedNoDupList (x ∷ zs) → IsSortedNoDupList (y ∷ zs)
  IsSortedNoDupList-replace-eq {x} {y} {zs} x=y (x≤zs , sorted)
    = IsSortedNoDupList-replace-eq' x=y x≤zs , sorted
  
  IsSortedNoDupList-replace-ord' : {x y : A} {zs : List A} → y ≤ x → All (λ z → x ≤ z × ¬ x == z) zs → All (λ z → y ≤ z × ¬ y == z) zs
  IsSortedNoDupList-replace-ord' y≤x [] = []
  IsSortedNoDupList-replace-ord' y≤x ((x≤z , x≠z) ∷ sorted) 
    = (trans-ord y≤x x≤z , (λ y=z → x≠z (trans-eq (antisym-ord (ord-eq-comp x≤z (sym-eq y=z)) y≤x) y=z))) ∷ IsSortedNoDupList-replace-ord' y≤x sorted
  
  IsSortedNoDupList-replace-ord : {x y : A} {zs : List A} → y ≤ x → IsSortedNoDupList (x ∷ zs) → IsSortedNoDupList (y ∷ zs)
  IsSortedNoDupList-replace-ord {x} {y} {zs} y≤x (x≤zs , sorted)
    = IsSortedNoDupList-replace-ord' y≤x x≤zs , sorted
  
  -------------------------------------------------------------------------------
  -- Proof irrelevancy for sorted and no duplicate list
  -------------------------------------------------------------------------------

  proof-irr-IsSortedList : (xs : List A) → ProofIrrelevance (IsSortedList xs)
  proof-irr-IsSortedList [] sortedX sortedY = refl
  proof-irr-IsSortedList (x ∷ []) sortedX sortedY = refl
  proof-irr-IsSortedList (x ∷ y ∷ xs) (x≤y , sortedX) (x≤y' , sortedY) with OrdInstance.proof-irr-ord OrdA x≤y x≤y'
  proof-irr-IsSortedList (x ∷ y ∷ xs) (x≤y , sortedX) (.x≤y , sortedY) | refl = cong (λ X → x≤y , X) (proof-irr-IsSortedList (y ∷ xs) sortedX sortedY)
  
  proof-irr-IsSortedNoDupList : (xs : List A) → ProofIrrelevance (IsSortedNoDupList xs)
  proof-irr-IsSortedNoDupList [] (lift tt) (lift tt) = refl
  proof-irr-IsSortedNoDupList (x ∷ xs) (allX , sortedX) (allY , sortedY) 
    = Σ-eq (proof-irr-All xs (λ y → x ≤ y × ¬ (x == y)) (λ y p q → proof-irr-× (OrdInstance.proof-irr-ord OrdA) proof-irr-¬ p q) allX allY) 
           (≡-to-≅ (proof-irr-IsSortedNoDupList xs sortedX sortedY))

open ListProperties public

-------------------------------------------------------------------------------
-- Definition of monotonicity for function in relation to OrdInstances.
-------------------------------------------------------------------------------

private
  module Functions {ℓEqA ℓOrdA ℓEqB ℓOrdB : Level} {A B : Type} (OrdA : OrdInstance {ℓEqA} {ℓOrdA} A) (OrdB : OrdInstance {ℓEqB} {ℓOrdB} B) where
  
    private
      open ListProperties
      open OrdInstance
    
      _=A=_ = OrdInstance._==_ OrdA
      _=B=_ = OrdInstance._==_ OrdB
      _≤A_ = OrdInstance._≤_ OrdA
      _≤B_ = OrdInstance._≤_ OrdB
  
    
    -- What it means for a function to be monotonic in the context of 
    -- the Haskell Ord-instance.
    Monotonic : (f : A → B) → Set (ℓ ⊔ ℓOrdA ⊔ ℓOrdB)
    Monotonic f = (a b : A) → a ≤A b → f a ≤B f b
    
  -------------------------------------------------------------------------------
  -- Lemmas for monotonicity
  -------------------------------------------------------------------------------
    
    -- (monotonic-preserves-sorted OrdA OrdB f mon-f xs sorted)
    monotonic-preserves-sorted : (f : A → B) → Monotonic f
                               → (xs : List A) → IsSortedList OrdA xs → IsSortedList OrdB (map f xs)
    monotonic-preserves-sorted f mon-f [] sorted = lift tt
    monotonic-preserves-sorted f mon-f (x ∷ []) sorted = lift tt
    monotonic-preserves-sorted f mon-f (x ∷ y ∷ xs) (x≤y , sorted) = mon-f x y x≤y , monotonic-preserves-sorted f mon-f (y ∷ xs) sorted
    
    monotonic-preserves-equality : (f : A → B)
                                 → Monotonic f
                                 → (a b : A) → a =A= b → f a =B= f b
    monotonic-preserves-equality f mon-f a b a==b with dec-ord OrdA a b | dec-ord OrdA b a
    monotonic-preserves-equality f mon-f a b a==b | yes a≤b | yes b≤a = antisym-ord OrdB (mon-f a b a≤b) (mon-f b a b≤a)
    monotonic-preserves-equality f mon-f a b a==b | yes a≤b | no ¬b≤a = ⊥-elim (eq-contr OrdA a==b (inj₂ ¬b≤a))
    monotonic-preserves-equality f mon-f a b a==b | no ¬a≤b | yes b≤a = ⊥-elim (eq-contr OrdA a==b (inj₁ ¬a≤b))
    monotonic-preserves-equality f mon-f a b a==b | no ¬a≤b | no ¬b≤a = ⊥-elim (total-contr OrdA ¬a≤b ¬b≤a)
    
    proof-irr-monotonic : (f : A → B) → ProofIrrelevance (Monotonic f)
    proof-irr-monotonic f mon-f mon-f' = fun-ext (λ x → fun-ext (λ y → fun-ext (λ x≤y → proof-irr-ord OrdB (mon-f x y x≤y) (mon-f' x y x≤y))))
    
open Functions public
  
-- Composing two monotonic functions produces a monotonic function.
monotonic-composition : {ℓEqA ℓOrdA ℓEqB ℓOrdB ℓEqC ℓOrdC : Level} {A B C : Type} 
                      → (OrdA : OrdInstance {ℓEqA} {ℓOrdA} A) → (OrdB : OrdInstance {ℓEqB} {ℓOrdB} B) → (OrdC : OrdInstance {ℓEqC} {ℓOrdC} C)
                      → (f : B → C) → (g : A → B)
                      → Monotonic OrdB OrdC f → Monotonic OrdA OrdB g
                      → Monotonic OrdA OrdC (f ∘F g)
monotonic-composition OrdA OrdB OrdC f g mon-f mon-g a b a≤b = mon-f (g a) (g b) (mon-g a b a≤b)

monotonic-id : {ℓEq ℓOrd : Level} {A : Type} 
             → (OrdA : OrdInstance {ℓEq} {ℓOrd} A)
             → Monotonic OrdA OrdA idF
monotonic-id OrdA a b a≤b = a≤b

private
  module Congruence {ℓEqA ℓEqB : Level} {A B : Type} (EqA : EqInstance {ℓEqA} A) (EqB : EqInstance {ℓEqB} B) where
    private
      open ListProperties
      open EqInstance
    
      _=A=_ = EqInstance._==_ EqA
      _=B=_ = EqInstance._==_ EqB
    
    Congruent : (f : A → B) → Set (ℓ ⊔ ℓEqA ⊔ ℓEqB)
    Congruent f = (a b : A) → a =A= b → f a =B= f b
    
    IsStructuralEquality→Congruent : (f : A → B) → IsStructuralEquality EqA → Congruent f
    IsStructuralEquality→Congruent f struct-eqA a b a=b with struct-eqA a b a=b
    IsStructuralEquality→Congruent f struct-eqA a .a a=b | refl = EqInstance.refl-eq EqB
    
    proof-irr-Congruent : (f : A → B) → ProofIrrelevance (Congruent f)
    proof-irr-Congruent f cong-f cong-f' = fun-ext (λ a → fun-ext (λ b → fun-ext (λ a=b → proof-irr-eq EqB (cong-f a b a=b) (cong-f' a b a=b))))
    
open Congruence public

-------------------------------------------------------------------------------
-- Definition of ordered sets in form of lists
-------------------------------------------------------------------------------

open ListProperties

record LSet {ℓEq ℓOrd : Level} (A : Σ Type (OrdInstance {ℓEq} {ℓOrd})) : Set (ℓ ⊔ ℓEq ⊔ ℓOrd) where
  constructor lset
  field
    xs : List (proj₁ A) 
    sorted : IsSortedNoDupList (proj₂ A) xs

empty : {ℓEq ℓOrd : Level} → (A : Σ Type (OrdInstance {ℓEq} {ℓOrd})) → LSet A
empty A = lset [] (lift tt)

singleton : {ℓEq ℓOrd : Level} → (A : Σ Type (OrdInstance {ℓEq} {ℓOrd})) → (a : proj₁ A) → LSet A
singleton A a = lset (a ∷ []) ([] , (lift tt))

abstract
  lset-eq : {ℓEq ℓOrd : Level}
          → {A : Type} {OrdA : OrdInstance {ℓEq} {ℓOrd} A} 
          → (xs ys : List A)
          → (sortedX : IsSortedNoDupList OrdA xs) → (sortedY : IsSortedNoDupList OrdA ys)
          → xs ≡ ys
          → lset xs sortedX ≡ lset ys sortedY
  lset-eq {A = A} {OrdA} xs .xs sortedX sortedY refl with proof-irr-IsSortedNoDupList OrdA xs sortedX sortedY
  lset-eq {A = A} {OrdA} xs .xs sortedX .sortedX refl | refl = refl 
