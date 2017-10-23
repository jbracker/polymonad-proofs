
open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Level renaming ( suc to lsuc ; zero to lzero)

open import Data.Unit hiding ( _≤_ ; _≟_ ; total )
open import Data.Empty
open import Data.List
open import Data.Product hiding ( map )
open import Data.Sum hiding ( map )

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality using ( refl ; _≅_ ; ≡-to-≅ )
open import Relation.Binary

open import Extensionality
open import Equality
open import ProofIrrelevance
open import Haskell hiding ( Type )

open import Theory.Haskell.Constrained.Examples.LSet.Base

module Theory.Haskell.Constrained.Examples.LSet.Product {ℓA ℓB : Level} {A : Set ℓA} {B : Set ℓB} where 


private
  module Eq {ℓEqA ℓEqB : Level} (EqA : EqInstance {ℓEq = ℓEqA} A) (EqB : EqInstance {ℓEq = ℓEqB} B) where
    open EqInstance
    
    private
      _=A=_ = _==_ EqA
      _=B=_ = _==_ EqB
    
    dec-eq-× : Decidable (λ a b → (proj₁ a =A= proj₁ b) × (proj₂ a =B= proj₂ b))
    dec-eq-× (a₁ , a₂) (b₁ , b₂) with EqInstance.dec-eq EqA a₁ b₁ | EqInstance.dec-eq EqB a₂ b₂
    dec-eq-× (a₁ , a₂) (b₁ , b₂) | yes a₁=b₁ | yes a₂=b₂ = yes (a₁=b₁ , a₂=b₂)
    dec-eq-× (a₁ , a₂) (b₁ , b₂) | yes a₁=b₁ | no ¬a₂=b₂ = no (λ a=b → ¬a₂=b₂ (proj₂ a=b))
    dec-eq-× (a₁ , a₂) (b₁ , b₂) | no ¬a₁=b₁ | yes a₂=b₂ = no (λ a=b → ¬a₁=b₁ (proj₁ a=b))
    dec-eq-× (a₁ , a₂) (b₁ , b₂) | no ¬a₁=b₁ | no ¬a₂=b₂ = no (λ a=b → ¬a₁=b₁ (proj₁ a=b))
    
    Eq-× : EqInstance {ℓEq = ℓEqA ⊔ ℓEqB} (A × B)
    Eq-× = record 
      { _==_ = λ a b → (proj₁ a =A= proj₁ b) × (proj₂ a =B= proj₂ b)
      ; isDecEquivalence = record 
        { isEquivalence = record 
          { refl = EqInstance.refl-eq EqA , EqInstance.refl-eq EqB
          ; sym = λ a → EqInstance.sym-eq EqA (proj₁ a) , EqInstance.sym-eq EqB (proj₂ a)
          ; trans = λ a b → EqInstance.trans-eq EqA (proj₁ a) (proj₁ b) , EqInstance.trans-eq EqB (proj₂ a) (proj₂ b)
          }
        ; _≟_ = dec-eq-×
        }
      ; proof-irr-eq = proof-irr-× (proof-irr-eq EqA) (proof-irr-eq EqB)
      } where

open Eq public  

private
  module Ord {ℓEqA ℓEqB ℓOrdA ℓOrdB} (OrdA : OrdInstance {ℓEq = ℓEqA} {ℓOrdA} A) (OrdB : OrdInstance {ℓEq = ℓEqB} {ℓOrdB} B) where
    open OrdInstance
    
    private
      _≤A_ = _≤_ OrdA
      _≤B_ = _≤_ OrdB
      _=A=_ = _==_ OrdA
      _=B=_ = _==_ OrdB
      _=A×B=_ = EqInstance._==_ (Eq-× (eqInstance OrdA) (eqInstance OrdB))
    
    ordering-× : A × B → A × B → Set (ℓOrdA ⊔ ℓOrdB)
    ordering-× (a₁ , a₂) (b₁ , b₂) with dec-eq OrdA a₁ b₁
    ordering-× (a₁ , a₂) (b₁ , b₂) | yes a₁=b₁ = Lift {ℓ = ℓOrdA} (a₂ ≤B b₂)
    ordering-× (a₁ , a₂) (b₁ , b₂) | no ¬a₁=b₁ = Lift {ℓ = ℓOrdB} (a₁ ≤A b₁)
    
    dec-ord-× : Decidable ordering-×
    dec-ord-× (a₁ , a₂) (b₁ , b₂) with dec-eq OrdA a₁ b₁
    dec-ord-× (a₁ , a₂) (b₁ , b₂) | yes a₁=b₁ with dec-ord OrdB a₂ b₂ 
    dec-ord-× (a₁ , a₂) (b₁ , b₂) | yes a₁=b₁ | yes a₂≤b₂ = yes (lift a₂≤b₂)
    dec-ord-× (a₁ , a₂) (b₁ , b₂) | yes a₁=b₁ | no ¬a₂≤b₂ = no (λ a₂≤b₂ → ¬a₂≤b₂ (lower a₂≤b₂))
    dec-ord-× (a₁ , a₂) (b₁ , b₂) | no ¬a₁=b₁ with dec-ord OrdA a₁ b₁
    dec-ord-× (a₁ , a₂) (b₁ , b₂) | no ¬a₁=b₁ | yes a₁≤b₁ = yes (lift a₁≤b₁)
    dec-ord-× (a₁ , a₂) (b₁ , b₂) | no ¬a₁=b₁ | no ¬a₁≤b₁ = no (λ a₁≤b₁ → ¬a₁≤b₁ (lower a₁≤b₁))
    
    total-ord-× : Total ordering-×
    total-ord-× (a₁ , a₂) (b₁ , b₂) with dec-eq OrdA a₁ b₁ | dec-eq OrdA b₁ a₁
    total-ord-× (a₁ , a₂) (b₁ , b₂) | yes a₁=b₁ | yes b₁=a₁ with total OrdB a₂ b₂
    total-ord-× (a₁ , a₂) (b₁ , b₂) | yes a₁=b₁ | yes b₁=a₁ | inj₁ a₂≤b₂ = inj₁ (lift a₂≤b₂)
    total-ord-× (a₁ , a₂) (b₁ , b₂) | yes a₁=b₁ | yes b₁=a₁ | inj₂ b₂≤a₂ = inj₂ (lift b₂≤a₂)
    total-ord-× (a₁ , a₂) (b₁ , b₂) | yes a₁=b₁ | no ¬b₁=a₁ = ⊥-elim (¬b₁=a₁ (sym-eq OrdA a₁=b₁))
    total-ord-× (a₁ , a₂) (b₁ , b₂) | no ¬a₁=b₁ | yes b₁=a₁ = ⊥-elim (¬a₁=b₁ (sym-eq OrdA b₁=a₁))
    total-ord-× (a₁ , a₂) (b₁ , b₂) | no ¬a₁=b₁ | no ¬b₁=a₁ with total OrdA a₁ b₁
    total-ord-× (a₁ , a₂) (b₁ , b₂) | no ¬a₁=b₁ | no ¬b₁=a₁ | inj₁ a₁≤b₁ = inj₁ (lift a₁≤b₁)
    total-ord-× (a₁ , a₂) (b₁ , b₂) | no ¬a₁=b₁ | no ¬b₁=a₁ | inj₂ b₁≤a₁ = inj₂ (lift b₁≤a₁)
    
    proof-irr-ord-× : {a b : A × B} → ProofIrrelevance (ordering-× a b)
    proof-irr-ord-× {a₁ , a₂} {b₁ , b₂} a≤b a≤b' with dec-eq OrdA a₁ b₁
    proof-irr-ord-× {a₁ , a₂} {b₁ , b₂} a≤b a≤b' | yes a₁=b₁ = proof-irr-Lift (proof-irr-ord OrdB) a≤b a≤b'
    proof-irr-ord-× {a₁ , a₂} {b₁ , b₂} a≤b a≤b' | no ¬a₁=b₁ = proof-irr-Lift (proof-irr-ord OrdA) a≤b a≤b'
    
    antisym-ord-× : Antisymmetric _=A×B=_ ordering-×
    antisym-ord-× {a₁ , a₂} {b₁ , b₂} a≤b b≤a with dec-eq OrdA a₁ b₁ | dec-eq OrdA b₁ a₁ 
    antisym-ord-× {a₁ , a₂} {b₁ , b₂} a≤b b≤a | yes a₁=b₁ | yes b₁=a₁ with dec-eq OrdB a₂ b₂
    antisym-ord-× {a₁ , a₂} {b₁ , b₂} a≤b b≤a | yes a₁=b₁ | yes b₁=a₁ | yes a₂=b₂ = a₁=b₁ , a₂=b₂
    antisym-ord-× {a₁ , a₂} {b₁ , b₂} a≤b b≤a | yes a₁=b₁ | yes b₁=a₁ | no ¬a₂=b₂ = ⊥-elim (¬a₂=b₂ (antisym-ord OrdB (lower a≤b) (lower b≤a)))
    antisym-ord-× {a₁ , a₂} {b₁ , b₂} a≤b b≤a | yes a₁=b₁ | no ¬b₁=a₁ = ⊥-elim (¬b₁=a₁ (sym-eq OrdA a₁=b₁))
    antisym-ord-× {a₁ , a₂} {b₁ , b₂} a≤b b≤a | no ¬a₁=b₁ | yes b₁=a₁ = ⊥-elim (¬a₁=b₁ (sym-eq OrdA b₁=a₁))
    antisym-ord-× {a₁ , a₂} {b₁ , b₂} a≤b b≤a | no ¬a₁=b₁ | no ¬b₁=a₁ = ⊥-elim (¬a₁=b₁ (antisym-ord OrdA (lower a≤b) (lower b≤a)))
    
    wierd-reflexive-× : {a b : A × B} → (a =A×B= b) → ordering-× a b
    wierd-reflexive-× {a₁ , a₂} {b₁ , b₂} a=b with dec-eq OrdA a₁ b₁ | dec-eq OrdA b₁ a₁ 
    wierd-reflexive-× {a₁ , a₂} {b₁ , b₂} a=b | yes a₁=b₁ | yes b₁=a₁ with antisym-ord' OrdB (proj₂ a=b)
    wierd-reflexive-× {a₁ , a₂} {b₁ , b₂} a=b | yes a₁=b₁ | yes b₁=a₁ | a₂≤b₂ , _ = lift a₂≤b₂
    wierd-reflexive-× {a₁ , a₂} {b₁ , b₂} a=b | yes a₁=b₁ | no ¬b₁=a₁ = ⊥-elim (¬b₁=a₁ (sym-eq OrdA a₁=b₁))
    wierd-reflexive-× {a₁ , a₂} {b₁ , b₂} a=b | no ¬a₁=b₁ | _ = ⊥-elim (¬a₁=b₁ (proj₁ a=b))
    
    transitive-ord-× : Transitive ordering-×
    transitive-ord-× {a₁ , a₂} {b₁ , b₂} {c₁ , c₂} a≤b b≤c with dec-eq OrdA a₁ b₁ | dec-eq OrdA b₁ c₁ | dec-eq OrdA a₁ c₁
    transitive-ord-× {a₁ , a₂} {b₁ , b₂} {c₁ , c₂} a≤b b≤c | yes a₁=b₁ | yes b₁=c₁ | yes a₁=c₁ = lift (trans-ord OrdB (lower a≤b) (lower b≤c))
    transitive-ord-× {a₁ , a₂} {b₁ , b₂} {c₁ , c₂} a≤b b≤c | yes a₁=b₁ | yes b₁=c₁ | no ¬a₁=c₁ = ⊥-elim (¬a₁=c₁ (trans-eq OrdA a₁=b₁ b₁=c₁))
    transitive-ord-× {a₁ , a₂} {b₁ , b₂} {c₁ , c₂} a≤b b≤c | yes a₁=b₁ | no ¬b₁=c₁ | yes a₁=c₁ = ⊥-elim (¬b₁=c₁ (trans-eq OrdA (sym-eq OrdA a₁=b₁) a₁=c₁))
    transitive-ord-× {a₁ , a₂} {b₁ , b₂} {c₁ , c₂} a≤b b≤c | yes a₁=b₁ | no ¬b₁=c₁ | no ¬a₁=c₁ = lift (eq-ord-comp OrdA a₁=b₁ (lower b≤c))
    transitive-ord-× {a₁ , a₂} {b₁ , b₂} {c₁ , c₂} a≤b b≤c | no ¬a₁=b₁ | yes b₁=c₁ | yes a₁=c₁ = ⊥-elim (¬a₁=b₁ (trans-eq OrdA a₁=c₁ (sym-eq OrdA b₁=c₁)))
    transitive-ord-× {a₁ , a₂} {b₁ , b₂} {c₁ , c₂} a≤b b≤c | no ¬a₁=b₁ | yes b₁=c₁ | no ¬a₁=c₁ = lift (ord-eq-comp OrdA (lower a≤b) b₁=c₁)
    transitive-ord-× {a₁ , a₂} {b₁ , b₂} {c₁ , c₂} a≤b b≤c | no ¬a₁=b₁ | no ¬b₁=c₁ | yes a₁=c₁ = ⊥-elim (¬a₁=b₁ (antisym-ord OrdA (lower a≤b) (ord-eq-comp OrdA (lower b≤c) (sym-eq OrdA a₁=c₁))))
    transitive-ord-× {a₁ , a₂} {b₁ , b₂} {c₁ , c₂} a≤b b≤c | no ¬a₁=b₁ | no ¬b₁=c₁ | no ¬a₁=c₁ = lift (trans-ord OrdA (lower a≤b) (lower b≤c))
    
    OrdInstance-× : OrdInstance (A × B)
    OrdInstance-× = record
      { _≤_ = ordering-×
      ; eqInstance = Eq-× (eqInstance OrdA) (eqInstance OrdB)
      ; proof-irr-ord = proof-irr-ord-×
      ; isDecTotalOrder = record 
        { isTotalOrder = record 
          { isPartialOrder = record 
            { isPreorder = record 
              { isEquivalence = IsDecEquivalence.isEquivalence (EqInstance.isDecEquivalence (Eq-× (eqInstance OrdA) (eqInstance OrdB)))
              ; reflexive = wierd-reflexive-×
              ; trans = transitive-ord-×
              }
            ; antisym = antisym-ord-×
            }
          ; total =  total-ord-×
          }
        ; _≟_ = dec-eq-× (eqInstance OrdA) (eqInstance OrdB)
        ; _≤?_ = dec-ord-×
        }
      }
    
    IsStructuralEquality-× : IsStructuralEquality (eqInstance OrdA) → IsStructuralEquality (eqInstance OrdB) → IsStructuralEquality (eqInstance OrdInstance-×)
    IsStructuralEquality-× struct-eqA struct-eqB (a₁ , a₂) (b₁ , b₂) (a₁=b₁ , a₂=b₂) = Σ-eq (struct-eqA a₁ b₁ a₁=b₁) (≡-to-≅ (struct-eqB a₂ b₂ a₂=b₂))
    
open Ord using ( OrdInstance-× ; IsStructuralEquality-× ) public
