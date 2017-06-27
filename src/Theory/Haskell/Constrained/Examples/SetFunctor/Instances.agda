 
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

open import Theory.Haskell.Constrained.Examples.SetFunctor.Base

module Theory.Haskell.Constrained.Examples.SetFunctor.Instances where 

-------------------------------------------------------------------------------
-- Instances of lists in Haskell
-------------------------------------------------------------------------------

EqList : {ℓ ℓEq : Level} {A : Set ℓ} → EqInstance {ℓ} {ℓEq} A → EqInstance {ℓ} {ℓEq} (List A)
EqList {ℓ} {ℓEq} {A} EqA = record 
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
    
    _==_ : List A → List A → Set ℓEq
    [] == [] = Lift ⊤
    [] == (x ∷ ys) = Lift ⊥
    (x ∷ xs) == [] = Lift ⊥
    (x ∷ xs) == (y ∷ ys) = (x =A= y) × (xs == ys)
    
    abstract
      lrefl : {xs : List A} → xs == xs
      lrefl {[]} = lift tt
      lrefl {x ∷ xs} = EqInstance.refl-eq EqA {x} , lrefl {xs}
    
    abstract
      lsym : {xs ys : List A} → xs == ys → ys == xs
      lsym {[]} {[]} (lift tt) = lift tt
      lsym {[]} {x ∷ ys} (lift ())
      lsym {x ∷ xs} {[]} (lift ())
      lsym {x ∷ xs} {y ∷ ys} (x==y , xs==ys) = EqInstance.sym-eq EqA x==y , lsym {xs} {ys} xs==ys
      
    abstract
      ltrans : {xs ys zs : List A} → xs == ys → ys == zs → xs == zs
      ltrans {[]} {[]} {[]} (lift tt) (lift tt) = lift tt
      ltrans {[]} {[]} {z ∷ zs} (lift tt) (lift ())
      ltrans {[]} {y ∷ ys} (lift ()) ys==zs
      ltrans {x ∷ xs} {[]} (lift ()) ys==zs
      ltrans {x ∷ xs} {y ∷ ys} {[]} (x==y , xs==ys) (lift ())
      ltrans {x ∷ xs} {y ∷ ys} {z ∷ zs} (x==y , xs==ys) (y==z , ys==zs) = EqInstance.trans-eq EqA x==y y==z , ltrans {xs} {ys} {zs} xs==ys ys==zs
    
    _=?=_ : (x y : List A) → Dec (x == y)
    [] =?= [] = yes (lift tt)
    [] =?= (x ∷ ys) = no lower
    (x ∷ xs) =?= [] = no lower
    (x ∷ xs) =?= (y ∷ ys) with EqInstance.dec-eq EqA x y | xs =?= ys
    (x ∷ xs) =?= (y ∷ ys) | yes x==y | yes xs==ys = yes (x==y , xs==ys)
    (x ∷ xs) =?= (y ∷ ys) | yes x==y | no ¬xs==ys = no (¬xs==ys ∘F proj₂)
    (x ∷ xs) =?= (y ∷ ys) | no ¬x==y | xs=?=ys    = no (¬x==y   ∘F proj₁)
    
    proof-irr : {xs ys : List A} → ProofIrrelevance (xs == ys)
    proof-irr {[]} {[]} (lift tt) (lift tt) = refl
    proof-irr {[]} {y ∷ ys} (lift ()) eqYs
    proof-irr {x ∷ xs} {[]} (lift ()) eqXs
    proof-irr {x ∷ xs} {y ∷ ys} (eqX , eqXs) (eqY , eqYs) with EqInstance.proof-irr-eq EqA eqX eqY | proof-irr {xs} {ys} eqXs eqYs
    proof-irr {x ∷ xs} {y ∷ ys} (eqX , eqXs) (.eqX , .eqXs) | refl | refl = refl

open EqInstance
open OrdInstance hiding ( dec-eq ; sym-eq ; trans-eq )

OrdList : {ℓ ℓEq ℓOrd : Level} {A : Set ℓ} → OrdInstance {ℓ} {ℓEq} {ℓOrd} A → OrdInstance {ℓ} {ℓEq} {ℓOrd} (List A)
OrdList {ℓ} {ℓEq} {ℓOrd} {A} OrdA = record
  { _≤_ = ord
  ; eqInstance = EqList (eqInstance OrdA)
  ; proof-irr-ord = λ {xs} {ys} → proof-irr {xs} {ys}
  ; isDecTotalOrder = record 
    { isTotalOrder = record 
      { isPartialOrder = record 
        { isPreorder = record 
          { isEquivalence = EqInstance.isEquivalence (EqList EqA)
          ; reflexive = λ {a} {b} → refl-transfer {a} {b}
          ; trans = λ {a} {b} {c} → trans' {a} {b} {c} }
        ; antisym = λ {xs} {ys} → antisym {xs} {ys}
        }
      ; total = total'
      }
    ; _≟_ = dec-eq (EqList (eqInstance OrdA))
    ; _≤?_ = dec
    }
  } where
    
    EqA = eqInstance OrdA
    _≤A_ = _≤_ OrdA
    eq = EqInstance._==_ (EqList EqA)
    
    ord : List A → List A → Set ℓOrd
    ord [] _ = Lift ⊤
    ord (x ∷ xs) [] = Lift ⊥
    ord (x ∷ xs) (y ∷ ys) with dec-eq EqA x y
    ord (x ∷ xs) (y ∷ ys) | yes x=y = ord xs ys
    ord (x ∷ xs) (y ∷ ys) | no ¬x=y with dec-ord OrdA x y
    ord (x ∷ xs) (y ∷ ys) | no ¬x=y | yes x≤y = Lift ⊤
    ord (x ∷ xs) (y ∷ ys) | no ¬x=y | no ¬x≤y = Lift ⊥
    
    proof-irr : {a b : List A} → ProofIrrelevance (ord a b)
    proof-irr {[]} {ys} (lift tt) (lift tt) = refl
    proof-irr {x ∷ xs} {[]} (lift ()) (lift ())
    proof-irr {x ∷ xs} {y ∷ ys} p q with dec-eq EqA x y | dec-eq EqA y x
    proof-irr {x ∷ xs} {y ∷ ys} p q | yes x=y | yes y=x = proof-irr {xs} {ys} p q
    proof-irr {x ∷ xs} {y ∷ ys} p q | yes x=y | no ¬y=x = ⊥-elim (¬y=x (sym-eq EqA x=y))
    proof-irr {x ∷ xs} {y ∷ ys} p q | no ¬x=y | yes y=x = ⊥-elim (¬x=y (sym-eq EqA y=x))
    proof-irr {x ∷ xs} {y ∷ ys} p q | no ¬x=y | no ¬y=x with dec-ord OrdA x y | dec-ord OrdA y x
    proof-irr {x ∷ xs} {y ∷ ys} p q | no ¬x=y | no ¬y=x | yes x≤y | yes y≤x = ⊥-elim (¬x=y (antisym-ord OrdA x≤y y≤x))
    proof-irr {x ∷ xs} {y ∷ ys} p q | no ¬x=y | no ¬y=x | yes x≤y | no ¬y≤x = refl
    proof-irr {x ∷ xs} {y ∷ ys} (lift ()) q | no ¬x=y | no ¬y=x | no ¬x≤y | yes y≤x
    proof-irr {x ∷ xs} {y ∷ ys} (lift ()) q | no ¬x=y | no ¬y=x | no ¬x≤y | no ¬y≤x
    
    dec : (xs ys : List A) → Dec (ord xs ys)
    dec [] ys = yes (lift tt)
    dec (x ∷ xs) [] = no lower
    dec (x ∷ xs) (y ∷ ys) with dec-eq EqA x y
    dec (x ∷ xs) (y ∷ ys) | yes x=y = dec xs ys
    dec (x ∷ xs) (y ∷ ys) | no ¬x=y with dec-ord OrdA x y
    dec (x ∷ xs) (y ∷ ys) | no ¬x=y | yes x≤y = yes (lift tt)
    dec (x ∷ xs) (y ∷ ys) | no ¬x=y | no ¬x≤y = no lower
    
    total' : (xs ys : List A) → ord xs ys ⊎ ord ys xs
    total' [] ys = inj₁ (lift tt)
    total' (x ∷ xs) [] = inj₂ (lift tt)
    total' (x ∷ xs) (y ∷ ys) with dec-eq EqA x y | dec-eq EqA y x
    total' (x ∷ xs) (y ∷ ys) | yes x=y | yes y=x = total' xs ys
    total' (x ∷ xs) (y ∷ ys) | yes x=y | no ¬y=x = ⊥-elim (¬y=x (sym-eq EqA x=y))
    total' (x ∷ xs) (y ∷ ys) | no ¬x=y | yes y=x = ⊥-elim (¬x=y (sym-eq EqA y=x))
    total' (x ∷ xs) (y ∷ ys) | no ¬x=y | no ¬y=x with dec-ord OrdA x y | dec-ord OrdA y x
    total' (x ∷ xs) (y ∷ ys) | no ¬x=y | no ¬y=x | yes x≤y | yes y≤x = ⊥-elim (¬x=y (antisym-ord OrdA x≤y y≤x))
    total' (x ∷ xs) (y ∷ ys) | no ¬x=y | no ¬y=x | yes x≤y | no ¬y≤x = inj₁ (lift tt)
    total' (x ∷ xs) (y ∷ ys) | no ¬x=y | no ¬y=x | no ¬x≤y | yes y≤x = inj₂ (lift tt)
    total' (x ∷ xs) (y ∷ ys) | no ¬x=y | no ¬y=x | no ¬x≤y | no ¬y≤x = ⊥-elim (total-contr OrdA ¬y≤x ¬x≤y)
    
    abstract
      antisym : {xs ys : List A} → ord xs ys → ord ys xs → eq xs ys
      antisym {[]} {[]} (lift tt) (lift tt) = lift tt
      antisym {[]} {y ∷ ys} (lift tt) (lift ())
      antisym {x ∷ xs} {[]} (lift ()) (lift tt)
      antisym {x ∷ xs} {y ∷ ys} xs≤ys ys≤xs with dec-eq EqA x y | dec-eq EqA y x
      antisym {x ∷ xs} {y ∷ ys} xs≤ys ys≤xs | yes x=y | yes y=x = x=y , antisym {xs} {ys} xs≤ys ys≤xs
      antisym {x ∷ xs} {y ∷ ys} xs≤ys ys≤xs | yes x=y | no ¬y=x = ⊥-elim (¬y=x (sym-eq EqA x=y))
      antisym {x ∷ xs} {y ∷ ys} xs≤ys ys≤xs | no ¬x=y | yes y=x = ⊥-elim (¬x=y (sym-eq EqA y=x))
      antisym {x ∷ xs} {y ∷ ys} xs≤ys ys≤xs | no ¬x=y | no ¬y=x with dec-ord OrdA x y | dec-ord OrdA y x
      antisym {x ∷ xs} {y ∷ ys} xs≤ys ys≤xs | no ¬x=y | no ¬y=x | yes x≤y | yes y≤x = ⊥-elim (¬x=y (antisym-ord OrdA x≤y y≤x))
      antisym {x ∷ xs} {y ∷ ys} xs≤ys (lift ()) | no ¬x=y | no ¬y=x | yes x≤y | no ¬y≤x
      antisym {x ∷ xs} {y ∷ ys} (lift ()) ys≤xs | no ¬x=y | no ¬y=x | no ¬x≤y | yes y≤x
      antisym {x ∷ xs} {y ∷ ys} xs≤ys ys≤xs | no ¬x=y | no ¬y=x | no ¬x≤y | no ¬y≤x = ⊥-elim (total-contr OrdA ¬x≤y ¬y≤x)
    
    abstract
      refl-transfer : {xs ys : List A} → eq xs ys → ord xs ys
      refl-transfer {[]} {[]} (lift tt) = lift tt
      refl-transfer {[]} {y ∷ ys} (lift ())
      refl-transfer {x ∷ xs} {[]} (lift ())
      refl-transfer {x ∷ xs} {y ∷ ys} eq with dec-eq EqA x y
      refl-transfer {x ∷ xs} {y ∷ ys} eq | yes x=y = refl-transfer {xs} {ys} (proj₂ eq)
      refl-transfer {x ∷ xs} {y ∷ ys} eq | no ¬x=y = ⊥-elim (¬x=y (proj₁ eq))
    
    abstract
      trans' : {xs ys zs : List A} → ord xs ys → ord ys zs → ord xs zs
      trans' {[]}     {ys}     {zs} (lift tt) ys≤zs = lift tt
      trans' {x ∷ xs} {[]}     {zs} (lift ()) (lift tt)
      trans' {x ∷ xs} {y ∷ ys} {[]} xs≤ys (lift ())
      trans' {x ∷ xs} {y ∷ ys} {z ∷ zs} xs≤ys ys≤zs with dec-eq EqA x y
      trans' {x ∷ xs} {y ∷ ys} {z ∷ zs} xs≤ys ys≤zs | yes x=y with dec-eq EqA y z 
      trans' {x ∷ xs} {y ∷ ys} {z ∷ zs} xs≤ys ys≤zs | yes x=y | yes y=z with dec-eq EqA x z
      trans' {x ∷ xs} {y ∷ ys} {z ∷ zs} xs≤ys ys≤zs | yes x=y | yes y=z | yes x=z = trans' {xs} {ys} {zs} xs≤ys ys≤zs
      trans' {x ∷ xs} {y ∷ ys} {z ∷ zs} xs≤ys ys≤zs | yes x=y | yes y=z | no ¬x=z = ⊥-elim (¬x=z (trans-eq EqA x=y y=z))
      trans' {x ∷ xs} {y ∷ ys} {z ∷ zs} xs≤ys ys≤zs | yes x=y | no ¬y=z with dec-ord OrdA y z
      trans' {x ∷ xs} {y ∷ ys} {z ∷ zs} xs≤ys (lift tt) | yes x=y | no ¬y=z | yes y≤z with dec-eq EqA x z
      trans' {x ∷ xs} {y ∷ ys} {z ∷ zs} xs≤ys (lift tt) | yes x=y | no ¬y=z | yes y≤z | yes x=z = ⊥-elim (¬y=z (trans-eq EqA (sym-eq EqA x=y) x=z))
      trans' {x ∷ xs} {y ∷ ys} {z ∷ zs} xs≤ys (lift tt) | yes x=y | no ¬y=z | yes y≤z | no ¬x=z with dec-ord OrdA x z
      trans' {x ∷ xs} {y ∷ ys} {z ∷ zs} xs≤ys (lift tt) | yes x=y | no ¬y=z | yes y≤z | no ¬x=z | yes x≤z = lift tt
      trans' {x ∷ xs} {y ∷ ys} {z ∷ zs} xs≤ys (lift tt) | yes x=y | no ¬y=z | yes y≤z | no ¬x=z | no ¬x≤z = ⊥-elim (¬x≤z (eq-ord-comp OrdA x=y y≤z))
      trans' {x ∷ xs} {y ∷ ys} {z ∷ zs} xs≤ys (lift ()) | yes x=y | no ¬y=z | no ¬y≤z
      trans' {x ∷ xs} {y ∷ ys} {z ∷ zs} xs≤ys ys≤zs | no ¬x=y with dec-ord OrdA x y
      trans' {x ∷ xs} {y ∷ ys} {z ∷ zs} xs≤ys ys≤zs | no ¬x=y | yes x≤y with dec-eq EqA y z
      trans' {x ∷ xs} {y ∷ ys} {z ∷ zs} xs≤ys ys≤zs | no ¬x=y | yes x≤y | yes y=z with dec-eq EqA x z
      trans' {x ∷ xs} {y ∷ ys} {z ∷ zs} xs≤ys ys≤zs | no ¬x=y | yes x≤y | yes y=z | yes x=z = ⊥-elim (¬x=y (trans-eq EqA x=z (sym-eq EqA y=z)))
      trans' {x ∷ xs} {y ∷ ys} {z ∷ zs} xs≤ys ys≤zs | no ¬x=y | yes x≤y | yes y=z | no ¬x=z with dec-ord OrdA x z
      trans' {x ∷ xs} {y ∷ ys} {z ∷ zs} xs≤ys ys≤zs | no ¬x=y | yes x≤y | yes y=z | no ¬x=z | yes x≤z = lift tt
      trans' {x ∷ xs} {y ∷ ys} {z ∷ zs} xs≤ys ys≤zs | no ¬x=y | yes x≤y | yes y=z | no ¬x=z | no ¬x≤z = ⊥-elim (¬x≤z (ord-eq-comp OrdA x≤y y=z))
      trans' {x ∷ xs} {y ∷ ys} {z ∷ zs} xs≤ys ys≤zs | no ¬x=y | yes x≤y | no ¬y=z with dec-ord OrdA y z
      trans' {x ∷ xs} {y ∷ ys} {z ∷ zs} (lift tt) (lift tt) | no ¬x=y | yes x≤y | no ¬y=z | yes y≤z with dec-eq EqA x z
      trans' {x ∷ xs} {y ∷ ys} {z ∷ zs} (lift tt) (lift tt) | no ¬x=y | yes x≤y | no ¬y=z | yes y≤z | yes x=z = ⊥-elim (¬x=y (antisym-ord OrdA x≤y (ord-eq-comp OrdA y≤z (sym-eq EqA x=z))))
      trans' {x ∷ xs} {y ∷ ys} {z ∷ zs} (lift tt) (lift tt) | no ¬x=y | yes x≤y | no ¬y=z | yes y≤z | no ¬x=z with dec-ord OrdA x z
      trans' {x ∷ xs} {y ∷ ys} {z ∷ zs} (lift tt) (lift tt) | no ¬x=y | yes x≤y | no ¬y=z | yes y≤z | no ¬x=z | yes x≤z = lift tt
      trans' {x ∷ xs} {y ∷ ys} {z ∷ zs} (lift tt) (lift tt) | no ¬x=y | yes x≤y | no ¬y=z | yes y≤z | no ¬x=z | no ¬x≤z = ⊥-elim (¬x≤z (trans-ord OrdA x≤y y≤z))
      trans' {x ∷ xs} {y ∷ ys} {z ∷ zs} (lift tt) (lift ()) | no ¬x=y | yes x≤y | no ¬y=z | no ¬y≤z
      trans' {x ∷ xs} {y ∷ ys} {z ∷ zs} (lift ()) ys≤zs | no ¬x=y | no ¬x≤y
    

IsStructuralEquality-List : {ℓ ℓEq : Level} {A : Set ℓ} → (EqA : EqInstance {ℓ} {ℓEq} A) → IsStructuralEquality EqA → IsStructuralEquality (EqList {ℓ} {ℓEq} EqA)
IsStructuralEquality-List EqA struct-eqA [] [] (lift tt) = refl
IsStructuralEquality-List EqA struct-eqA [] (y ∷ ys) (lift ())
IsStructuralEquality-List EqA struct-eqA (x ∷ xs) [] (lift ())
IsStructuralEquality-List EqA struct-eqA (x ∷ xs) (y ∷ ys) (x=y , xs=ys) = cong₂ _∷_ (struct-eqA x y x=y) (IsStructuralEquality-List EqA struct-eqA xs ys xs=ys)

-------------------------------------------------------------------------------
-- Instances of Set in Haskell
-------------------------------------------------------------------------------

EqLSet : {ℓ : Level} {A : Σ (Set ℓ) (OrdInstance {ℓ} {ℓ} {ℓ})} → EqInstance {ℓ} {ℓ} (LSet A)
EqLSet {ℓ} {A , OrdA} = record 
  { _==_ = λ x y → EqInstance._==_ (EqList (OrdInstance.eqInstance OrdA)) (LSet.xs x) (LSet.xs y)
  ; isDecEquivalence = record 
    { isEquivalence = record 
      { refl = λ {a} → EqInstance.refl-eq (EqList (OrdInstance.eqInstance OrdA)) {LSet.xs a}
      ; sym = λ {a} {b} x → EqInstance.sym-eq (EqList (OrdInstance.eqInstance OrdA)) {LSet.xs a} {LSet.xs b} x
      ; trans = λ {a} {b} {c} x y → EqInstance.trans-eq (EqList (OrdInstance.eqInstance OrdA)) {LSet.xs a} {LSet.xs b} {LSet.xs c} x y 
      }
    ; _≟_ = λ x y → EqInstance.dec-eq (EqList (OrdInstance.eqInstance OrdA)) (LSet.xs x) (LSet.xs y)
    }
  ; proof-irr-eq = λ {a} {b} x y → EqInstance.proof-irr-eq (EqList (OrdInstance.eqInstance OrdA)) {LSet.xs a} {LSet.xs b} x y
  }

OrdLSet : {ℓ : Level} {A : Σ (Set ℓ) (OrdInstance {ℓ} {ℓ} {ℓ})} → OrdInstance {ℓ} {ℓ} {ℓ} (LSet A)
OrdLSet {ℓ} {A , OrdA} = record
  { _≤_ = λ x y → OrdInstance._≤_ (OrdList OrdA) (LSet.xs x) (LSet.xs y)
  ; eqInstance = EqLSet {ℓ} {A , OrdA}
  ; proof-irr-ord = λ {a} {b} x y → OrdInstance.proof-irr-ord (OrdList OrdA) {LSet.xs a} {LSet.xs b} x y
  ; isDecTotalOrder = record 
    { isTotalOrder = record 
      { isPartialOrder = record 
        { isPreorder = record 
          { isEquivalence = EqInstance.isEquivalence (EqLSet {ℓ} {A , OrdA})
          ; reflexive = λ {a} x → OrdInstance.reflexive (OrdList OrdA) {LSet.xs a} x
          ; trans = λ {a} {b} {c} x y → OrdInstance.trans-ord (OrdList OrdA) {LSet.xs a} {LSet.xs b} {LSet.xs c} x y
          } 
        ; antisym = λ {a} {b} x y → OrdInstance.antisym-ord (OrdList OrdA) {LSet.xs a} {LSet.xs b} x y
        } 
      ; total = λ x y → OrdInstance.total (OrdList OrdA) (LSet.xs x) (LSet.xs y)
      }
    ; _≟_ = λ x y → OrdInstance.dec-eq (OrdList OrdA) (LSet.xs x) (LSet.xs y)
    ; _≤?_ = λ x y → OrdInstance.dec-ord (OrdList OrdA) (LSet.xs x) (LSet.xs y)
    }
  }

IsStructuralEquality-LSet : {ℓ : Level} {A : Set ℓ} → (OrdA : OrdInstance {ℓ} {ℓ} {ℓ} A) 
                          → IsStructuralEquality (eqInstance OrdA) → IsStructuralEquality (EqLSet {ℓ} {A , OrdA})
IsStructuralEquality-LSet {ℓ} {A} OrdA struct-eqA (lset x sortedX) (lset y sortedY) p 
  = lset-eq x y sortedX sortedY (IsStructuralEquality-List (eqInstance OrdA) struct-eqA x y p)

-------------------------------------------------------------------------------
-- Instances of unit in Haskell
-------------------------------------------------------------------------------

Eq-⊤ : {ℓ ℓEq : Level} → EqInstance {ℓ} {ℓEq} (Lift ⊤)
Eq-⊤ = record 
  { _==_ = λ _ _ → Lift ⊤ 
  ; isDecEquivalence = record 
    { isEquivalence = record 
      { refl = lift tt 
      ; sym = λ _ → lift tt 
      ; trans = λ _ _ → lift tt 
      }
    ; _≟_ = λ _ _ → yes (lift tt)
    } 
  ; proof-irr-eq = λ _ _ → refl
  }

Ord-⊤ : {ℓ ℓEq ℓOrd : Level} → OrdInstance {ℓ} {ℓEq} {ℓOrd} (Lift ⊤)
Ord-⊤ {ℓ} {ℓEq} {ℓOrd} = record
  { _≤_ = λ _ _ → Lift ⊤
  ; eqInstance = Eq-⊤
  ; proof-irr-ord = λ x y → refl
  ; isDecTotalOrder = record 
    { isTotalOrder = record 
      { isPartialOrder = record 
        { isPreorder = record 
          { isEquivalence = EqInstance.isEquivalence (Eq-⊤ {ℓ} {ℓEq}) 
          ; reflexive = λ _ → lift tt 
          ; trans = λ _ _ → lift tt
          }
        ; antisym = λ _ _ → lift tt 
        }
      ; total = λ _ _ → inj₁ (lift tt) 
      } 
    ; _≟_ = EqInstance.dec-eq (Eq-⊤ {ℓ} {ℓEq}) 
    ; _≤?_ = λ x y → yes (lift tt)
    }
  }

IsStructuralEquality-⊤ : {ℓ ℓEq : Level} → IsStructuralEquality (Eq-⊤ {ℓ} {ℓEq})
IsStructuralEquality-⊤ (lift tt) (lift tt) (lift tt) = refl

-------------------------------------------------------------------------------
-- Instances of empty in Haskell
-------------------------------------------------------------------------------

Eq-⊥ : {ℓ ℓEq : Level} → EqInstance {ℓ} {ℓEq} (Lift {ℓ = ℓ} ⊥)
Eq-⊥ {ℓ} {ℓEq} = record 
  { _==_ = eq
  ; isDecEquivalence = record 
    { isEquivalence = record 
      { refl = λ {a} → ⊥-elim (lower a)
      ; sym = λ {a} {b} x → ⊥-elim (lower a)
      ; trans = λ {a} {b} {c} x y → ⊥-elim (lower a)
      }
    ; _≟_ = λ x y → yes (⊥-elim (lower x))
    }
  ; proof-irr-eq = λ {a} {b} x y → ⊥-elim (lower a)
  } where
    eq : Lift {ℓ = ℓ} ⊥ → Lift {ℓ = ℓ} ⊥ → Set ℓEq
    eq (lift ()) (lift ())

Ord-⊥ : {ℓ ℓEq ℓOrd : Level} → OrdInstance {ℓ} {ℓEq} {ℓOrd} (Lift {ℓ = ℓ} ⊥)
Ord-⊥ {ℓ} {ℓEq} {ℓOrd} = record
  { _≤_ = ord
  ; eqInstance = Eq-⊥
  ; proof-irr-ord = λ {a} {b} x y → ⊥-elim (lower a)
  ; isDecTotalOrder = record 
    { isTotalOrder = record 
      { isPartialOrder = record 
        { isPreorder = record 
          { isEquivalence = EqInstance.isEquivalence Eq-⊥
          ; reflexive = λ {a} {b} x → ⊥-elim (lower a)
          ; trans = λ {a} {b} {c} x y → ⊥-elim (lower a)
          }
        ; antisym = λ {a} {b} x y → ⊥-elim (lower a)
        }
      ; total = λ x y → inj₁ (⊥-elim (lower x))
      }
    ; _≟_ = EqInstance.dec-eq Eq-⊥
    ; _≤?_ = λ x y → yes (⊥-elim (lower x))
    }
  } where
    ord : Lift {ℓ = ℓ} ⊥ → Lift {ℓ = ℓ} ⊥ → Set ℓOrd
    ord (lift ()) (lift ())

IsStructuralEquality-⊥ : {ℓ ℓEq : Level} → IsStructuralEquality (Eq-⊥ {ℓ} {ℓEq})
IsStructuralEquality-⊥ (lift ()) (lift ())
