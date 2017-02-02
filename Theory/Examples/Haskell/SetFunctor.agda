
-- TODO: Finish proofs
module Theory.Examples.Haskell.SetFunctor where

open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Level renaming ( suc to lsuc ; zero to lzero)
open import Data.Unit hiding ( _≤_ )
open import Data.Empty
open import Data.Bool
open import Data.List
open import Data.Nat renaming ( _>_ to _>ℕ_ ; _<_ to _<ℕ_ ; _≤_ to _≤ℕ_ ; _≥_ to _≥ℕ_ )
open import Data.Product
open import Data.Sum
open import Relation.Nullary
open import Relation.Binary using ( IsDecEquivalence ; IsEquivalence )
open import Relation.Binary.PropositionalEquality renaming ( refl to prefl ; sym to psym ; trans to ptrans )
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
open import Theory.InclusionFunctor
open import Theory.Examples.Category
open import Theory.Examples.HaskellFunctorToFunctor

Hask : Category
Hask = setCategory {lzero}

record EqDict (A : Type) : Type where
  field
    _==_ : A → A → Bool
    eqRefl : (a : A) → (a == a) ≡ true
    eqSym  : (a b : A) → (a == b) ≡ true → (b == a) ≡ true
    eqTrans : (a b c : A) → (a == b) ≡ true → (b == c) ≡ true → (a == c) ≡ true
    eqDec : (a b : A) → Dec ((a == b) ≡ true)
  
  _≠_ : A → A → Bool
  _≠_ a b = not $ a == b

record OrdDict (A : Type) (eq : EqDict A) : Type where
  _==_ = EqDict._==_ eq
  _≠_ = EqDict._≠_ eq
  field
    _≤_ : A → A → Bool
    ordRefl : (a : A) → (a ≤ a) ≡ true
    ordTrans : (a b c : A) → (a ≤ b) ≡ true → (b ≤ c) ≡ true → (a ≤ c) ≡ true
    ordAntiSym : (a b : A) → (a ≤ b) ≡ true → (b ≤ a) ≡ true → (a == b) ≡ true
    ordTotal : (a b : A) → ((a ≤ b) ≡ true) ⊎ ((b ≤ a) ≡ true)
    ordDec : (a b : A) → Dec ((a ≤ b) ≡ true)

  _>_ : A → A → Bool
  _>_ a b = not $ a ≤ b

  _≥_ : A → A → Bool
  _≥_ a b = (a > b) ∨ (a == b)
  
  _<_ : A → A → Bool
  _<_ a b = (a ≤ b) ∧ (a ≠ b)

-- Equality up to reordering or equal elements
data _=[_]=_ {A : Type} (x : A) (EqA : EqDict A) (y : A) : Type where
  refl : EqDict._==_ EqA x y ≡ true → x =[ EqA ]= y

HaskEquivalence : {A : Type} → (EqA : EqDict A) → IsDecEquivalence (λ a b → a =[ EqA ]= b)
HaskEquivalence {A} EqA = record 
  { isEquivalence = record 
    { refl = hrefl 
    ; sym = hsym
    ; trans = htrans
    }
  ; _≟_ = dec
  } where
    dec : (a b : A) → Dec (a =[ EqA ]= b)
    dec a b with EqDict.eqDec EqA a b
    dec a b | yes p = yes (refl p)
    dec a b | no ¬p = no q
      where q : ¬ (a =[ EqA ]= b)
            q (refl p) = ¬p p
    
    hrefl : {a : A} → (a =[ EqA ]= a)
    hrefl {a} = refl $ EqDict.eqRefl EqA a
    
    hsym : {a b : A} → (a =[ EqA ]= b) → (b =[ EqA ]= a)
    hsym {a} {b} (refl a==b) = refl $ EqDict.eqSym EqA a b a==b
    
    htrans : {a b c : A} → (a =[ EqA ]= b) → (b =[ EqA ]= c) → (a =[ EqA ]= c)
    htrans {a} {b} {c} (refl a==b) (refl b==c) = refl $ EqDict.eqTrans EqA a b c a==b b==c


split-∧ : {a b : Bool} → a ∧ b ≡ true → a ≡ true × b ≡ true
split-∧ {true} {true} a∧b = prefl , prefl
split-∧ {true} {false} ()
split-∧ {false} {true} ()
split-∧ {false} {false} ()

EqList : {A : Type} → EqDict A → EqDict (List A)
EqList {A} EqA = record
  { _==_ = _==_ 
  ; eqRefl = eqRefl 
  ; eqSym = eqSym 
  ; eqTrans = eqTrans 
  ; eqDec = eqDec
  } where
    _=A=_ = EqDict._==_ EqA
    
    _==_ : List A → List A → Bool
    [] == [] = true
    [] == (x ∷ ys) = false
    (x ∷ xs) == [] = false
    (x ∷ xs) == (y ∷ ys) = x =A= y ∧ xs == ys
    
    eqRefl : (a : List A) → a == a ≡ true
    eqRefl [] = prefl
    eqRefl (x ∷ xs) with EqDict.eqRefl EqA x | eqRefl xs
    eqRefl (x ∷ xs) | x==x | xs==xs = cong₂ _∧_ x==x xs==xs
    
    eqSym : (a b : List A) → a == b ≡ true → b == a ≡ true
    eqSym [] [] xs==ys = prefl
    eqSym [] (x ∷ ys) ()
    eqSym (x ∷ xs) [] ()
    eqSym (x ∷ xs) (y ∷ ys) xs==ys 
      = cong₂ _∧_ (EqDict.eqSym EqA x y (proj₁ (split-∧ xs==ys))) 
                  (eqSym xs ys (proj₂ (split-∧ {a = x =A= y} xs==ys)))

    eqTrans : (a b c : List A) → a == b ≡ true → b == c ≡ true → a == c ≡ true
    eqTrans [] [] [] xs==ys ys==zs = prefl
    eqTrans [] [] (z ∷ zs) xs==ys ()
    eqTrans [] (y ∷ ys) [] () ()
    eqTrans [] (y ∷ ys) (z ∷ zs) () ys==zs
    eqTrans (x ∷ xs) [] [] () ys==zs
    eqTrans (x ∷ xs) [] (z ∷ zs) () ()
    eqTrans (x ∷ xs) (y ∷ ys) [] xs==ys ()
    eqTrans (x ∷ xs) (y ∷ ys) (z ∷ zs) xs==ys ys==zs 
      = cong₂ _∧_ (EqDict.eqTrans EqA x y z (proj₁ (split-∧ xs==ys)) (proj₁ (split-∧ ys==zs))) 
                  (eqTrans xs ys zs (proj₂ (split-∧ {a = x =A= y} xs==ys)) (proj₂ (split-∧ {a = y =A= z} ys==zs)))
    
    eqDec : (a b : List A) → Dec (a == b ≡ true)
    eqDec [] [] = yes prefl
    eqDec [] (y ∷ ys) = no (λ ())
    eqDec (x ∷ xs) [] = no (λ ())
    eqDec (x ∷ xs) (y ∷ ys) with EqDict.eqDec EqA x y | eqDec xs ys
    eqDec (x ∷ xs) (y ∷ ys) | yes p | yes q = yes (cong₂ _∧_ p q)
    eqDec (x ∷ xs) (y ∷ ys) | yes p | no ¬q = no (λ xs==ys → ¬q (proj₂ (split-∧ {a = x =A= y} xs==ys)))
    eqDec (x ∷ xs) (y ∷ ys) | no ¬p | yes q = no (λ x==y → ¬p (proj₁ (split-∧ x==y)))
    eqDec (x ∷ xs) (y ∷ ys) | no ¬p | no ¬q = no (λ x==y → ¬p (proj₁ (split-∧ x==y)))

Eqℕ : EqDict ℕ
Eqℕ = record 
  { _==_ = _==_ 
  ; eqRefl = eqRefl
  ; eqSym = eqSym
  ; eqTrans = eqTrans
  ; eqDec = eqDec
  } where
    _==_ : ℕ → ℕ → Bool
    zero == zero = true
    zero == suc m = false
    suc n == zero = false
    suc n == suc m = n == m
    
    eqRefl : (a : ℕ) → a == a ≡ true
    eqRefl zero = prefl
    eqRefl (suc a) = eqRefl a

    eqSym : (a b : ℕ) → (a == b) ≡ true → (b == a) ≡ true
    eqSym zero zero prefl = prefl
    eqSym zero (suc b) ()
    eqSym (suc a) zero ()
    eqSym (suc a) (suc b) = eqSym a b
    
    eqTrans : (a b c : ℕ) → (a == b) ≡ true → (b == c) ≡ true → (a == c) ≡ true
    eqTrans zero zero zero prefl prefl = prefl
    eqTrans zero zero (suc c) prefl ()
    eqTrans zero (suc b) c ()
    eqTrans (suc a) zero c ()
    eqTrans (suc a) (suc b) zero a==b ()
    eqTrans (suc a) (suc b) (suc c) = eqTrans a b c
    
    eqDec : (a b : ℕ) → Dec (a == b ≡ true)
    eqDec zero zero = yes prefl
    eqDec zero (suc b) = no (λ ())
    eqDec (suc a) zero = no (λ ())
    eqDec (suc a) (suc b) = eqDec a b


Ordℕ : OrdDict ℕ Eqℕ
Ordℕ = record
  { _≤_ = _≤_
  ; ordRefl = ordRefl
  ; ordTrans = ordTrans
  ; ordAntiSym = ordAntiSym
  ; ordTotal = ordTotal
  ; ordDec = ordDec
  } where
    _==_ = EqDict._==_ Eqℕ
    
    _≤_ : ℕ → ℕ → Bool
    zero  ≤ _     = true
    suc a ≤ zero  = false
    suc a ≤ suc b = a ≤ b

    ordRefl : (a : ℕ) → a ≤ a ≡ true
    ordRefl zero = prefl
    ordRefl (suc a) = ordRefl a
    
    ordTrans : (a b c : ℕ) → (a ≤ b) ≡ true → (b ≤ c) ≡ true → (a ≤ c) ≡ true
    ordTrans zero zero zero prefl prefl = prefl
    ordTrans zero zero (suc c) prefl prefl = prefl
    ordTrans zero (suc b) zero prefl ()
    ordTrans zero (suc b) (suc c) prefl b≤c = prefl
    ordTrans (suc a) zero zero ()
    ordTrans (suc a) zero (suc c) ()
    ordTrans (suc a) (suc b) zero a≤b ()
    ordTrans (suc a) (suc b) (suc c) = ordTrans a b c
    
    ordAntiSym : (a b : ℕ) → (a ≤ b) ≡ true → (b ≤ a) ≡ true → (a == b) ≡ true
    ordAntiSym zero zero prefl prefl = prefl
    ordAntiSym zero (suc b) prefl ()
    ordAntiSym (suc a) zero ()
    ordAntiSym (suc a) (suc b) = ordAntiSym a b
    
    ordTotal : (a b : ℕ) → (a ≤ b) ≡ true ⊎ (b ≤ a) ≡ true
    ordTotal zero zero = inj₁ prefl
    ordTotal zero (suc b) = inj₁ prefl
    ordTotal (suc a) zero = inj₂ prefl
    ordTotal (suc a) (suc b) = ordTotal a b
    
    ordDec : (a b : ℕ) → Dec (a ≤ b ≡ true)
    ordDec zero zero = yes prefl
    ordDec zero (suc b) = yes prefl
    ordDec (suc a) zero = no (λ ())
    ordDec (suc a) (suc b) = ordDec a b



HaskOrd : Category
HaskOrd = record
  { Obj = Obj
  ; Hom = Hom
  ; _∘_ = λ {a} {b} {c} → _∘_ {a} {b} {c}
  ; id = λ {a} → id {a}
  ; assoc = prefl
  ; idL = prefl
  ; idR = prefl
  } where
    Obj : Set (lsuc lzero)
    Obj = ∃ λ (A : Type) → ∃ λ (Eq : EqDict A) → OrdDict A Eq
    
    Hom : Obj → Obj → Set lzero
    Hom (A , EqA , OrdA) (B , EqB , OrdB) = A → B

    _∘_ : {a b c : Obj} → Hom b c → Hom a b → Hom a c
    _∘_ f g = f ∘F g
    
    id : {a : Obj} → Hom a a
    id = idF

HaskOrdInclusionFunctor : Functor HaskOrd Hask
HaskOrdInclusionFunctor = record 
  { F₀ = λ OrdA → proj₁ OrdA 
  ; F₁ = idF
  ; id = prefl
  ; dist = prefl
  }


IsSorted : {A : Type} {EqA : EqDict A} → OrdDict A EqA → List A → Set lzero
IsSorted OrdA [] = ⊤
IsSorted OrdA (x ∷ []) = ⊤
IsSorted OrdA (x ∷ y ∷ xs) = (x ≤ y ≡ true) × IsSorted OrdA (y ∷ xs)
  where _≤_ = OrdDict._≤_ OrdA

data ListSet (A : Category.Obj HaskOrd) : Type where
  listSet : (xs : List (proj₁ A)) → IsSorted (proj₂ (proj₂ A)) xs → ListSet A


insert : {A : Type} {Eq : EqDict A} → OrdDict A Eq → A → List A → List A
insert ord x [] = x ∷ []
insert ord x (y ∷ ys) with OrdDict.ordDec ord x y
insert ord x (y ∷ ys) | yes x≤y = x ∷ y ∷ ys
insert ord x (y ∷ ys) | no ¬x≤y = y ∷ insert ord x ys

law-insert-length : {A : Type} {Eq : EqDict A} 
                  → (ord : OrdDict A Eq) → (x : A) → (xs : List A)
                  → length (insert ord x xs) ≡ suc (length xs) 
law-insert-length ord x [] = prefl
law-insert-length ord x (y ∷ ys) with OrdDict.ordDec ord x y
law-insert-length ord x (y ∷ ys) | yes p = prefl
law-insert-length ord x (y ∷ ys) | no ¬p = cong suc (law-insert-length ord x ys)

law-insert-length-cong : {A : Type} {Eq : EqDict A} 
                       → (ord : OrdDict A Eq) 
                       → (x : A) → (xs ys : List A)
                       → length (x ∷ xs) ≡ length ys → length (insert ord x xs) ≡ length ys
law-insert-length-cong ord x xs ys eq = ptrans (law-insert-length ord x xs) eq

law-sorted-insert' : {A : Type} {EqA : EqDict A}
                   → (ord : OrdDict A EqA)
                   → (x z : A) → (xs : List A)
                   → IsSorted ord (x ∷ xs)
                   → (IsSorted ord (x ∷ insert ord z xs)) 
                   ⊎ (IsSorted ord (z ∷ x ∷ xs))
law-sorted-insert' ord x z [] tt with OrdDict.ordDec ord x z 
law-sorted-insert' ord x z [] tt | yes x≤z = inj₁ $ x≤z , tt
law-sorted-insert' ord x z [] tt | no ¬x≤z with OrdDict.ordTotal ord x z
law-sorted-insert' ord x z [] tt | no ¬x≤z | inj₁ x≤z = ⊥-elim (¬x≤z x≤z)
law-sorted-insert' ord x z [] tt | no ¬x≤z | inj₂ z≤x = inj₂ $ z≤x , tt
law-sorted-insert' ord x z (y ∷ xs) (x≤y , sorted[y∷xs]) with OrdDict.ordDec ord x z
law-sorted-insert' ord x z (y ∷ xs) (x≤y , sorted[y∷xs]) | yes x≤z with OrdDict.ordDec ord z y
law-sorted-insert' ord x z (y ∷ xs) (x≤y , sorted[y∷xs]) | yes x≤z | yes z≤y = inj₁ $ x≤z , z≤y , sorted[y∷xs]
law-sorted-insert' ord x z (y ∷ xs) (x≤y , sorted[y∷xs]) | yes x≤z | no ¬z≤y with law-sorted-insert' ord y z xs sorted[y∷xs]
law-sorted-insert' ord x z (y ∷ xs) (x≤y , sorted[y∷xs]) | yes x≤z | no ¬z≤y | inj₁ p = inj₁ $ x≤y , p
law-sorted-insert' ord x z (y ∷ xs) (x≤y , sorted[y∷xs]) | yes x≤z | no ¬z≤y | inj₂ (z≤y , _) = ⊥-elim (¬z≤y z≤y)
law-sorted-insert' ord x z (y ∷ xs) (x≤y , sorted[y∷xs]) | no ¬x≤z with OrdDict.ordTotal ord x z
law-sorted-insert' ord x z (y ∷ xs) (x≤y , sorted[y∷xs]) | no ¬x≤z | inj₁ x≤z = ⊥-elim (¬x≤z x≤z)
law-sorted-insert' ord x z (y ∷ xs) (x≤y , sorted[y∷xs]) | no ¬x≤z | inj₂ z≤x = inj₂ $ z≤x , x≤y , sorted[y∷xs]

law-sorted-insert : {A : Type} {EqA : EqDict A}
                  → (ord : OrdDict A EqA)
                  → (x : A) → (xs : List A)
                  → IsSorted ord xs
                  → IsSorted ord (insert ord x xs)
law-sorted-insert ord x [] tt = tt
law-sorted-insert ord x (y ∷ []) tt with OrdDict.ordDec ord x y 
law-sorted-insert ord x (y ∷ []) tt | yes x≤y = x≤y , tt
law-sorted-insert ord x (y ∷ []) tt | no ¬x≤y with OrdDict.ordTotal ord y x
law-sorted-insert ord x (y ∷ []) tt | no ¬x≤y | inj₁ y≤x = y≤x , tt
law-sorted-insert ord x (y ∷ []) tt | no ¬x≤y | inj₂ x≤y = ⊥-elim (¬x≤y x≤y)
law-sorted-insert ord x (y ∷ z ∷ xs) (y≤z , sorted[z∷xs]) with OrdDict.ordDec ord x y
law-sorted-insert ord x (y ∷ z ∷ xs) (y≤z , sorted[z∷xs]) | yes x≤y = x≤y , y≤z , sorted[z∷xs]
law-sorted-insert ord x (y ∷ z ∷ xs) (y≤z , sorted[z∷xs]) | no ¬x≤y with OrdDict.ordTotal ord x y
law-sorted-insert ord x (y ∷ z ∷ xs) (y≤z , sorted[z∷xs]) | no ¬x≤y | inj₁ x≤y = ⊥-elim (¬x≤y x≤y)
law-sorted-insert ord x (y ∷ z ∷ xs) (y≤z , sorted[z∷xs]) | no ¬x≤y | inj₂ y≤x with OrdDict.ordDec ord x z
law-sorted-insert ord x (y ∷ z ∷ xs) (y≤z , sorted[z∷xs]) | no ¬x≤y | inj₂ y≤x | yes x≤z = y≤x , x≤z , sorted[z∷xs]
law-sorted-insert ord x (y ∷ z ∷ xs) (y≤z , sorted[z∷xs]) | no ¬x≤y | inj₂ y≤x | no ¬x≤z with law-sorted-insert' ord z x xs sorted[z∷xs]
law-sorted-insert ord x (y ∷ z ∷ xs) (y≤z , sorted[z∷xs]) | no ¬x≤y | inj₂ y≤x | no ¬x≤z | inj₁ p = y≤z , p
law-sorted-insert ord x (y ∷ z ∷ xs) (y≤z , sorted[z∷xs]) | no ¬x≤y | inj₂ y≤x | no ¬x≤z | inj₂ (x≤z , _) = ⊥-elim (¬x≤z x≤z)

law-sorted-forget : {A : Type} {EqA : EqDict A} 
                  → (OrdA : OrdDict A EqA) 
                  → (x : A) → (xs : List A) 
                  → IsSorted OrdA (x ∷ xs) → IsSorted OrdA xs
law-sorted-forget OrdA x [] tt = tt
law-sorted-forget OrdA x (y ∷ xs) (_ , sorted) = sorted

sort : {A : Type} {EqA : EqDict A} → OrdDict A EqA → List A → List A
sort ord [] = []
sort ord (x ∷ xs) = insert ord x (sort ord xs)

law-sort-length : {A : Type} {Eq : EqDict A} 
                → (OrdA : OrdDict A Eq) → (xs : List A)
                → length (sort OrdA xs) ≡ length xs
law-sort-length OrdA [] = prefl
law-sort-length OrdA (x ∷ xs) = law-insert-length-cong OrdA x (sort OrdA xs) (x ∷ xs) (cong suc (law-sort-length OrdA xs))


law-sort-sorted : {A : Type} {EqA : EqDict A} → (OrdA : OrdDict A EqA) → (xs : List A) → IsSorted OrdA (sort OrdA xs)
law-sort-sorted OrdA [] = tt
law-sort-sorted OrdA (x ∷ []) = tt
law-sort-sorted OrdA (x ∷ y ∷ xs) = law-sorted-insert OrdA x (insert OrdA y (sort OrdA xs)) (law-sorted-insert OrdA y (sort OrdA xs) (law-sort-sorted OrdA xs))

law-insert-sorted : {A : Type} {EqA : EqDict A} 
                  → (OrdA : OrdDict A EqA) 
                  → (x : A) → (xs : List A)
                  → IsSorted OrdA (x ∷ xs)
                  → insert OrdA x xs ≡ x ∷ xs
law-insert-sorted OrdA x [] sorted = prefl
law-insert-sorted OrdA x (y ∷ xs) sorted with OrdDict.ordDec OrdA x y 
law-insert-sorted OrdA x (y ∷ xs) sorted | yes _ = prefl
law-insert-sorted OrdA x (y ∷ xs) (x≤y , sorted) | no ¬x≤y = ⊥-elim (¬x≤y x≤y)

law-sort-idempotence : {A : Type} {EqA : EqDict A} → (OrdA : OrdDict A EqA) → (xs : List A) → IsSorted OrdA xs → sort OrdA xs ≡ xs
law-sort-idempotence OrdA [] sorted = prefl
law-sort-idempotence OrdA (x ∷ []) sorted = prefl
law-sort-idempotence OrdA (x ∷ y ∷ xs) (x≤y , sorted) = begin
  insert OrdA x (insert OrdA y (sort OrdA xs)) 
    ≡⟨ cong (λ X → insert OrdA x (insert OrdA y X)) (law-sort-idempotence OrdA xs (law-sorted-forget OrdA y xs sorted)) ⟩ 
  insert OrdA x (insert OrdA y xs) 
    ≡⟨ cong (insert OrdA x) (law-insert-sorted OrdA y xs sorted) ⟩ 
  insert OrdA x (y ∷ xs) 
    ≡⟨ law-insert-sorted OrdA x (y ∷ xs) (x≤y , sorted) ⟩ 
  x ∷ y ∷ xs ∎

mkListSet : {A : Category.Obj HaskOrd} → List (proj₁ A) → ListSet A
mkListSet {A} xs = listSet (sort (proj₂ (proj₂ A)) xs) (law-sort-sorted (proj₂ (proj₂ A)) xs)

unListSet : {A : Category.Obj HaskOrd} → ListSet A → List (proj₁ A)
unListSet (listSet xs _) = xs

proof-irr-sorted : {A : Type} {EqA : EqDict A} → (OrdA : OrdDict A EqA) → (xs : List A) → (sa sb : IsSorted OrdA xs) → sa ≡ sb 
proof-irr-sorted OrdA [] tt tt = prefl
proof-irr-sorted OrdA (x ∷ []) tt tt = prefl
proof-irr-sorted OrdA (x ∷ y ∷ xs) (p₁ , sa) (p₂ , sb) = cong₂ _,_ (proof-irrelevance p₁ p₂) (proof-irr-sorted OrdA (y ∷ xs) sa sb)



HaskEndomorphism : Category
HaskEndomorphism = endomorphismCategory Hask

HaskEndomorphismInclusionFunctor : Functor HaskEndomorphism Hask
HaskEndomorphismInclusionFunctor = record 
  { F₀ = idF
  ; F₁ = F₁
  ; id = prefl
  ; dist = λ {a} {b} {c} {f} {g} → dist {a} {b} {c} {f} {g}
  } where
    F₁ : {a b : Category.Obj HaskEndomorphism} 
       → Category.Hom HaskEndomorphism a b → Category.Hom Hask (idF a) (idF b)
    F₁ (f , prefl)= f
    
    _∘Hask_ = Category._∘_ Hask
    _∘Endo_ = Category._∘_ HaskEndomorphism
    
    dist : {a b c : Category.Obj HaskEndomorphism}
         → {f : Category.Hom HaskEndomorphism a b}
         → {g : Category.Hom HaskEndomorphism b c}
         → F₁ (g ∘Endo f) ≡ (F₁ g) ∘Hask (F₁ f)
    dist {f = f , prefl} {g , prefl} = prefl

ListFunctor = Applicative.functor $ Monad.applicative monadList

listMap = Functor.fmap ListFunctor

eqListSet : {A : Type} {EqA : EqDict A} 
          → (OrdA : OrdDict A EqA)
          → (s₀ s₁ : List A) 
          → (sorted₀ : IsSorted OrdA s₀) → (sorted₁ : IsSorted OrdA s₁)
          → (s₀ ≡ s₁)
          → listSet s₀ sorted₀ ≡ listSet s₁ sorted₁
eqListSet OrdA s₀ .s₀ sorted₀ sorted₁ prefl = cong (listSet s₀) (proof-irr-sorted OrdA s₀ sorted₀ sorted₁)

law-swap-insert-insert : {A : Type} {EqA : EqDict A} 
                       → (OrdA : OrdDict A EqA) 
                       → (x y : A) → (xs : List A) 
                       → insert OrdA x (insert OrdA y xs) ≡ insert OrdA y (insert OrdA x xs)
law-swap-insert-insert OrdA x y [] with OrdDict.ordDec OrdA x y
law-swap-insert-insert OrdA x y [] | yes x≤y with OrdDict.ordDec OrdA y x
law-swap-insert-insert OrdA x y [] | yes x≤y | yes y≤x = {!!}
law-swap-insert-insert OrdA x y [] | yes x≤y | no ¬y≤x = prefl
law-swap-insert-insert OrdA x y [] | no ¬x≤y with OrdDict.ordDec OrdA y x
law-swap-insert-insert OrdA x y [] | no ¬x≤y | yes y≤x = prefl
law-swap-insert-insert OrdA x y [] | no ¬x≤y | no ¬y≤x with OrdDict.ordTotal OrdA x y
law-swap-insert-insert OrdA x y [] | no ¬x≤y | no ¬y≤x | inj₁ x≤y = ⊥-elim (¬x≤y x≤y)
law-swap-insert-insert OrdA x y [] | no ¬x≤y | no ¬y≤x | inj₂ y≤x = ⊥-elim (¬y≤x y≤x)
law-swap-insert-insert OrdA x y (z ∷ xs) with OrdDict.ordDec OrdA x y | OrdDict.ordDec OrdA y x
law-swap-insert-insert OrdA x y (z ∷ xs) | yes x≤y | yes y≤x = {!!}
law-swap-insert-insert OrdA x y (z ∷ xs) | yes x≤y | no ¬y≤x with OrdDict.ordDec OrdA x z | OrdDict.ordDec OrdA y z 
law-swap-insert-insert OrdA x y (z ∷ xs) | yes x≤y | no ¬y≤x | yes x≤z | yes y≤z = {!!}
law-swap-insert-insert OrdA x y (z ∷ xs) | yes x≤y | no ¬y≤x | yes x≤z | no ¬y≤z = {!!}
law-swap-insert-insert OrdA x y (z ∷ xs) | yes x≤y | no ¬y≤x | no ¬x≤z | yes y≤z = ⊥-elim (¬x≤z (OrdDict.ordTrans OrdA x y z x≤y y≤z))
law-swap-insert-insert OrdA x y (z ∷ xs) | yes x≤y | no ¬y≤x | no ¬x≤z | no ¬y≤z = {!!}
law-swap-insert-insert OrdA x y (z ∷ xs) | no ¬x≤y | yes y≤x = {!!}
law-swap-insert-insert OrdA x y (z ∷ xs) | no ¬x≤y | no ¬y≤x with OrdDict.ordTotal OrdA x y
law-swap-insert-insert OrdA x y (z ∷ xs) | no ¬x≤y | no ¬y≤x | inj₁ x≤y = ⊥-elim (¬x≤y x≤y)
law-swap-insert-insert OrdA x y (z ∷ xs) | no ¬x≤y | no ¬y≤x | inj₂ y≤x = ⊥-elim (¬y≤x y≤x)


law-swap-insert-sort : {A : Type} {EqA : EqDict A} 
                     → (OrdA : OrdDict A EqA) 
                     → (x : A) → (xs : List A) 
                     → insert OrdA x (sort OrdA xs) ≡ sort OrdA (insert OrdA x xs)
law-swap-insert-sort OrdA x [] = prefl
law-swap-insert-sort OrdA x (y ∷ xs) with OrdDict.ordDec OrdA x y
law-swap-insert-sort OrdA x (y ∷ xs) | yes x≤y = prefl
law-swap-insert-sort OrdA x (y ∷ xs) | no ¬x≤y = begin
  insert OrdA x (insert OrdA y (sort OrdA xs))  
    ≡⟨ law-swap-insert-insert OrdA x y (sort OrdA xs) ⟩
  insert OrdA y (insert OrdA x (sort OrdA xs)) 
    ≡⟨ cong (insert OrdA y) (law-swap-insert-sort OrdA x xs) ⟩
  insert OrdA y (sort OrdA (insert OrdA x xs)) ∎

ListSetFunctor : Functor HaskOrd Hask
ListSetFunctor = functor F₀ F₁ (λ {a} → id {a}) (λ {a} {b} {c} {f} {g} → dist {a} {b} {c} {f} {g})
  where
    F₀ : Category.Obj HaskOrd → Category.Obj Hask
    F₀ A = ListSet A
    
    F₁ : {a b : Category.Obj HaskOrd} → Category.Hom HaskOrd a b → Category.Hom Hask (F₀ a) (F₀ b)
    F₁ f (listSet xs _) = mkListSet (listMap f xs)
    
    _∘H_ = Category._∘_ Hask

    id : {A : Category.Obj HaskOrd} → F₁ (Category.id HaskOrd {A}) ≡ Category.id Hask {F₀ A}
    id {A , EqA , OrdA} = funExt helperId
      where
        helperId : (s : ListSet (A , EqA , OrdA)) 
                 → F₁ (Category.id HaskOrd {A , EqA , OrdA}) s ≡ Category.id Hask {F₀ (A , EqA , OrdA)} s
        helperId (listSet s sorted) = begin
          F₁ (Category.id HaskOrd {A , EqA , OrdA}) (listSet s sorted) 
            ≡⟨ prefl ⟩
          F₁ idF (listSet s sorted) 
            ≡⟨ prefl ⟩
          mkListSet (listMap idF s)
            ≡⟨ cong mkListSet (cong (λ X → X s) (Functor.lawId ListFunctor)) ⟩
          mkListSet s
            ≡⟨ prefl ⟩
          listSet (sort OrdA s) (law-sort-sorted OrdA s)
            ≡⟨ eqListSet OrdA (sort OrdA s) s (law-sort-sorted OrdA s) sorted (law-sort-idempotence OrdA s sorted) ⟩
          listSet s sorted ∎ 
    
    dist : {A B C : Category.Obj HaskOrd} 
         → {f : Category.Hom HaskOrd A B} → {g : Category.Hom HaskOrd B C}
         → F₁ (g ∘H f) ≡ F₁ g ∘H F₁ f
    dist {A , EqA , OrdA} {B , EqB , OrdB} {C , EqC , OrdC} {f} {g} = funExt helper
      where
        helper' : (s : List A) → sort OrdC (listMap (g ∘H f) s) ≡ sort OrdC (listMap g (sort OrdB (listMap f s)))
        helper' [] = prefl
        helper' (x ∷ xs) = begin
          insert OrdC ((g ∘H f) x) (sort OrdC (listMap (g ∘H f) xs))
            ≡⟨ prefl ⟩
          insert OrdC (g (f x)) (sort OrdC (listMap (g ∘H f) xs))
            ≡⟨ cong (insert OrdC (g (f x))) (helper' xs) ⟩
          insert OrdC (g (f x)) (sort OrdC (listMap g (sort OrdB (listMap f xs))))
            ≡⟨ {!!} ⟩
          sort OrdC (listMap g (insert OrdB (f x) (sort OrdB (listMap f xs)))) ∎
        
        helper : (s : ListSet (A , EqA , OrdA)) → F₁ (g ∘H f) s ≡ (F₁ g ∘H F₁ f) s
        helper (listSet s sorted) = begin
          mkListSet (listMap (g ∘H f) s) 
            ≡⟨ prefl ⟩
          listSet (sort OrdC (listMap (g ∘H f) s)) (law-sort-sorted OrdC (listMap (g ∘H f) s))
            ≡⟨ eqListSet OrdC (sort OrdC (listMap (g ∘H f) s)) (sort OrdC (listMap g (sort OrdB (listMap f s)))) (law-sort-sorted OrdC (listMap (g ∘H f) s)) (law-sort-sorted OrdC (listMap g (sort OrdB (listMap f s)))) (helper' s) ⟩
          listSet (sort OrdC (listMap g (sort OrdB (listMap f s)))) (law-sort-sorted OrdC (listMap g (sort OrdB (listMap f s))))
            ≡⟨ prefl ⟩
          mkListSet (listMap g (sort OrdB (listMap f s)))
            ≡⟨ prefl ⟩
          F₁ g (listSet (sort OrdB (listMap f s)) (law-sort-sorted OrdB (listMap f s)))
            ≡⟨ prefl ⟩
          (F₁ g ∘H F₁ f) (listSet s sorted) ∎

listSetMap : {A B : Category.Obj HaskOrd} → (proj₁ A → proj₁ B) → ListSet A  → ListSet B
listSetMap = Functor.F₁ ListSetFunctor

-- law-sort-idempotence : {A : Type} {EqA : EqDict A} → (OrdA : OrdDict A EqA) → (xs : List A) → IsSorted OrdA xs → sort OrdA xs ≡ xs
-- proof-irr-sorted : {A : Type} {EqA : EqDict A} → (OrdA : OrdDict A EqA) → (xs : List A) → (sa sb : IsSorted OrdA xs) → sa ≡ sb
 
