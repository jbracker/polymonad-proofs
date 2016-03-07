 
module Polymonad.Unionable where

-- Stdlib
open import Data.Product
open import Data.Sum
open import Data.Empty
open import Relation.Nullary -- ¬
open import Relation.Binary.PropositionalEquality -- ≡
open ≡-Reasoning -- begin ≡⟨⟩ ∎

-- Local
open import Utilities
open import Haskell
open import Identity
open import Polymonad

-- -----------------------------------------------------------------------------
-- Unionable Polymonad
-- -----------------------------------------------------------------------------

open Polymonad.Polymonad

-- Set of laws that need to hold in order for union of polymonads to work.
record UnionablePolymonad {TyCons : Set} (pm : Polymonad (IdTyCons ⊎ TyCons) idTC) : Set₁ where
  field
    -- Every bind operator that only involves the identity is equivalent to the identity bind operator.
    lawEqBindId : ∀ {α β : Type} → (b : B[ idTC , idTC ] pm ▷ idTC) → substBind (lawId pm) (lawId pm) (lawId pm) (pmBind pm b) {α} {β} ≡ bindId {α} {β}
    
    -- There is only one identity bind operators in this polymonad and it can be identified usind the IdBinds datatype.
    lawEqIdBinds : B[ idTC , idTC ] pm ▷ idTC ≡ IdBinds
    
    -- There a no bind operators aside of the identity bind operator that produce values inside of the identity monad.
    idMorph¬∃ : ∀ {M N : IdTyCons ⊎ TyCons} → (∃ λ(M' : TyCons) → M ≡ inj₂ M') ⊎ (∃ λ(N' : TyCons) → N ≡ inj₂ N') → ¬ (B[ M , N ] pm ▷ idTC)

-- -----------------------------------------------------------------------------
-- Unionable Polymonad Accessor Functions
-- -----------------------------------------------------------------------------

upmPolymonad : ∀ {TyCons : Set} {pm : Polymonad (IdTyCons ⊎ TyCons) idTC} → UnionablePolymonad pm → Polymonad (IdTyCons ⊎ TyCons) idTC
upmPolymonad {pm = pm} upm = pm

upmLawEqId : ∀ {TyCons : Set} {pm : Polymonad (IdTyCons ⊎ TyCons) idTC} → UnionablePolymonad pm → ⟨ pm ▷ idTC ⟩ ≡ Identity
upmLawEqId {pm = pm} upm = lawId pm

upmLawEqBindId = UnionablePolymonad.lawEqBindId
upmLawEqIdBinds = UnionablePolymonad.lawEqIdBinds
upmIdMorph¬∃ = UnionablePolymonad.idMorph¬∃

-- -----------------------------------------------------------------------------
-- Unionable Polymonad idMorph¬∃ Equivalence
-- -----------------------------------------------------------------------------
{-
[idMorph¬∃]↔[NM▷Id→NM≡Id] : {TyCons : Set} 
                          → (pm : Polymonad (IdTyCons ⊎ TyCons) idTC)
                          → ( (M N : IdTyCons ⊎ TyCons) → (∃ λ(M' : TyCons) → M ≡ inj₂ M') ⊎ (∃ λ(N' : TyCons) → N ≡ inj₂ N') → ¬ (B[ M , N ] pm ▷ idTC) )
                          ↔ ( (M N : IdTyCons ⊎ TyCons) → B[ M , N ] pm ▷ idTC → (M ≡ idTC × N ≡ idTC) )
[idMorph¬∃]↔[NM▷Id→NM≡Id] {TyCons = TyCons} pm = record
  { f = f pm
  ; f⁻¹ = f⁻¹ pm
    
  ; lawInjective  = {!!} -- : (a₁ a₂ : α) → f a₁ ≡ f a₂ → a₁ ≡ a₂
  ; lawSurjective = {!!} -- : (b : β) → f (f⁻¹ b) ≡ b
    
  ; lawInjective⁻¹  = {!!} -- : (b₁ b₂ : β) → f⁻¹ b₁ ≡ f⁻¹ b₂ → b₁ ≡ b₂
  ; lawSurjective⁻¹ = {!!} -- : (a : α) → f⁻¹ (f a) ≡ a
  } where
    f : {TyCons : Set} 
          → (pm : Polymonad (IdTyCons ⊎ TyCons) idTC)
          → ( (M N : IdTyCons ⊎ TyCons) → (∃ λ(M' : TyCons) → M ≡ inj₂ M') ⊎ (∃ λ(N' : TyCons) → N ≡ inj₂ N') → ¬ (B[ M , N ] pm ▷ idTC) )
          → ( (M N : IdTyCons ⊎ TyCons) → B[ M , N ] pm ▷ idTC → (M ≡ idTC × N ≡ idTC) )
    f pm idMorph¬∃ (inj₁ IdentTC) (inj₁ IdentTC) b = refl , refl
    f pm idMorph¬∃ (inj₁ IdentTC) (inj₂ N) b = ⊥-elim (idMorph¬∃ idTC (inj₂ N) (inj₂ (N , refl)) b)
    f pm idMorph¬∃ (inj₂ M) (inj₁ IdentTC) b = ⊥-elim (idMorph¬∃ (inj₂ M) idTC (inj₁ (M , refl)) b)
    f pm idMorph¬∃ (inj₂ M) (inj₂ N) b = ⊥-elim (idMorph¬∃ (inj₂ M) (inj₂ N) (inj₁ (M , refl)) b)

    f⁻¹ : {TyCons : Set} 
           → (pm : Polymonad (IdTyCons ⊎ TyCons) idTC)
           → ( (M N : IdTyCons ⊎ TyCons) → B[ M , N ] pm ▷ idTC → (M ≡ idTC × N ≡ idTC) )
           → ( (M N : IdTyCons ⊎ TyCons) → (∃ λ(M' : TyCons) → M ≡ inj₂ M') ⊎ (∃ λ(N' : TyCons) → N ≡ inj₂ N') → ¬ (B[ M , N ] pm ▷ idTC) )
    f⁻¹ pm ∀idMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ (P , ())) b
    f⁻¹ pm ∀idMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (P , ())) b
    f⁻¹ pm ∀idMorph (inj₁ IdentTC) (inj₂ N) (inj₁ (P , ())) b
    f⁻¹ pm ∀idMorph (inj₁ IdentTC) (inj₂ N) (inj₂ (.N , refl)) b with ∀idMorph idTC (inj₂ N) b
    f⁻¹ pm ∀idMorph (inj₁ IdentTC) (inj₂ N) (inj₂ (.N , refl)) b | refl , ()
    f⁻¹ pm ∀idMorph (inj₂ M) (inj₁ IdentTC) (inj₁ (.M , refl)) b with ∀idMorph (inj₂ M) idTC b
    f⁻¹ pm ∀idMorph (inj₂ M) (inj₁ IdentTC) (inj₁ (.M , refl)) b | () , refl
    f⁻¹ pm ∀idMorph (inj₂ M) (inj₁ IdentTC) (inj₂ (P , ())) b
    f⁻¹ pm ∀idMorph (inj₂ M) (inj₂ N) p b with ∀idMorph (inj₂ M) (inj₂ N) b
    f⁻¹ pm ∀idMorph (inj₂ M) (inj₂ N) p b | () , ()
    
    inj1 : (a₁ a₂ : (M N : IdTyCons ⊎ TyCons) → (∃ λ(M' : TyCons) → M ≡ inj₂ M') ⊎ (∃ λ(N' : TyCons) → N ≡ inj₂ N') → ¬ (B[ M , N ] pm ▷ idTC) ) 
         → f pm a₁ ≡ f pm a₂ → a₁ ≡ a₂
    inj1 a₁ a₂ p = funExt (λ M → funExt (λ N → funExt (λ ¬Id → funExt (λ b → {!!}))))
-}
