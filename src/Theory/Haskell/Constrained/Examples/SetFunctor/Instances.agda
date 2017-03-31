 
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
-- Eq instance of lists in Haskell
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
    
    lrefl : {xs : List A} → xs == xs
    lrefl {[]} = lift tt
    lrefl {x ∷ xs} = EqInstance.refl-eq EqA {x} , lrefl {xs}
    
    lsym : {xs ys : List A} → xs == ys → ys == xs
    lsym {[]} {[]} (lift tt) = lift tt
    lsym {[]} {x ∷ ys} (lift ())
    lsym {x ∷ xs} {[]} (lift ())
    lsym {x ∷ xs} {y ∷ ys} (x==y , xs==ys) = EqInstance.sym-eq EqA x==y , lsym {xs} {ys} xs==ys
    
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

IsStructuralEquality-List : {ℓ ℓEq : Level} {A : Set ℓ} → (EqA : EqInstance {ℓ} {ℓEq} A) → IsStructuralEquality EqA → IsStructuralEquality (EqList {ℓ} {ℓEq} EqA)
IsStructuralEquality-List EqA struct-eqA [] [] (lift tt) = refl
IsStructuralEquality-List EqA struct-eqA [] (y ∷ ys) (lift ())
IsStructuralEquality-List EqA struct-eqA (x ∷ xs) [] (lift ())
IsStructuralEquality-List EqA struct-eqA (x ∷ xs) (y ∷ ys) (x=y , xs=ys) = cong₂ _∷_ (struct-eqA x y x=y) (IsStructuralEquality-List EqA struct-eqA xs ys xs=ys)

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
