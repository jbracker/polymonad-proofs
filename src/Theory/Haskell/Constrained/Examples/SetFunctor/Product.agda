
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

module Theory.Haskell.Constrained.Examples.SetFunctor.Product {ℓA ℓB : Level} {A : Set ℓA} {B : Set ℓB} where 

open import Theory.Haskell.Constrained.Examples.SetFunctor.Base

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
     
    dec-ord-× : Decidable (λ a b → proj₁ a ≤A proj₁ b × proj₂ a ≤B proj₂ b)
    dec-ord-× (a₁ , a₂) (b₁ , b₂) with dec-ord OrdA a₁ b₁ | dec-ord OrdB a₂ b₂
    dec-ord-× (a₁ , a₂) (b₁ , b₂) | yes a₁≤b₁ | yes a₂≤b₂ = yes (a₁≤b₁ , a₂≤b₂)
    dec-ord-× (a₁ , a₂) (b₁ , b₂) | yes a₁≤b₁ | no ¬a₂≤b₂ = no (λ a≤b → ¬a₂≤b₂ (proj₂ a≤b))
    dec-ord-× (a₁ , a₂) (b₁ , b₂) | no ¬a₁≤b₁ | yes a₂≤b₂ = no (λ a≤b → ¬a₁≤b₁ (proj₁ a≤b))
    dec-ord-× (a₁ , a₂) (b₁ , b₂) | no ¬a₁≤b₁ | no ¬a₂≤b₂ = no (λ a≤b → ¬a₁≤b₁ (proj₁ a≤b))
    {-
    total-ord-× : Total (λ a b → proj₁ a ≤A proj₁ b × proj₂ a ≤B proj₂ b)
    total-ord-× a b with total OrdA (proj₁ a) (proj₁ b) | total OrdB (proj₂ a) (proj₂ b)
    total-ord-× a b | inj₁ a₁≤b₁ | inj₁ a₂≤b₂ = inj₁ (a₁≤b₁ , a₂≤b₂)
    total-ord-× a b | inj₁ a₁≤b₁ | inj₂ b₂≤a₂ = {!!}
    total-ord-× a b | inj₂ b₁≤a₁ | inj₁ a₂≤b₂ = {!!}
    total-ord-× a b | inj₂ b₁≤a₁ | inj₂ b₂≤a₂ = inj₂ (b₁≤a₁ , b₂≤a₂)
    
    OrdInstance-× : OrdInstance (A × B)
    OrdInstance-× = record
      { _≤_ = λ a b → Σ (proj₁ a ≤A proj₁ b) (λ a≤b → {!!}) --(proj₁ a ≤A proj₁ b) × (proj₂ a ≤B proj₂ b)
      ; eqInstance = Eq-× (eqInstance OrdA) (eqInstance OrdB)
      ; proof-irr-ord = {!!} --proof-irr-× (proof-irr-ord OrdA) (proof-irr-ord OrdB)
      ; isDecTotalOrder = record 
        { isTotalOrder = record 
          { isPartialOrder = record 
            { isPreorder = record 
              { isEquivalence = IsDecEquivalence.isEquivalence (EqInstance.isDecEquivalence (Eq-× (eqInstance OrdA) (eqInstance OrdB)))
              ; reflexive = λ {a} {b} a=b → {!!}
              ; trans = {!!} -- λ a≤b b≤c → trans-ord OrdA (proj₁ a≤b) (proj₁ b≤c) , trans-ord OrdB (proj₂ a≤b) (proj₂ b≤c)
              }
            ; antisym = {!!} -- λ a≤b b≤a → (antisym-ord OrdA (proj₁ a≤b) (proj₁ b≤a)) , (antisym-ord OrdB (proj₂ a≤b) (proj₂ b≤a))
            }
          ; total =  {!!} --total-ord-×
          }
        ; _≟_ = dec-eq-× (eqInstance OrdA) (eqInstance OrdB)
        ; _≤?_ = {!!} -- dec-ord-×
        }
      }
    
    IsStructuralEquality-× : IsStructuralEquality OrdA → IsStructuralEquality OrdB → IsStructuralEquality OrdInstance-×
    IsStructuralEquality-× struct-eqA struct-eqB a b = {!!}
    -}
open Ord public
