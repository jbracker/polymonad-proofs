
module Polymonad.Composition where

-- Stdlib
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Nullary.Core
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Local
open import Utilities
open import Haskell
open import Polymonad
open import Identity
open import Polymonad.Identity
open import Polymonad.Composable

--------------------------------------------------------------------------------
-- Polymonad Composition
--------------------------------------------------------------------------------

polymonadCompose : ∀ {TyCons₁ TyCons₂ : Set}
                 → {pm₁ : Polymonad (IdTyCons ⊎ TyCons₁) idTC}
                 → {pm₂ : Polymonad (IdTyCons ⊎ TyCons₂) idTC}
                 → ComposablePolymonad pm₁
                 → ComposablePolymonad pm₂
                 → Polymonad (IdTyCons ⊎ (TyCons₁ ⊎ TyCons₂)) idTC
polymonadCompose {TyCons₁} {TyCons₂} {pm₁} {pm₂} cpm₁ cpm₂ = record 
  { B[_,_]▷_ = B[_,_]▷_
  ; ⟨_⟩ = ⟨_⟩
  ; bind = λ {M} {N} {P} → bind {M} {N} {P}
  ; lawId = lawId
  ; lawFunctor = lawFunctor
  ; lawMorph1 = lawMorph1 
  ; lawMorph2 = lawMorph2
  ; lawMorph3 = lawMorph3
  ; lawDiamond1 = lawDiamond1 
  ; lawDiamond2 = lawDiamond2
  ; lawAssoc = lawAssoc
  ; lawClosure = lawClosure 
  } where
      TyCons = IdTyCons ⊎ (TyCons₁ ⊎ TyCons₂)

      Id : TyCons
      Id = inj₁ IdentTC
      
      eqId₁ = cpmLawEqId cpm₁
      eqId₂ = cpmLawEqId cpm₂

      eqIdBind : B[ idTC , idTC ] pm₁ ▷ idTC ≡ B[ idTC , idTC ] pm₂ ▷ idTC
      eqIdBind = trans (cpmLawEqIdBinds cpm₁) (sym (cpmLawEqIdBinds cpm₂))

      eqBindId₁ = cpmLawEqBindId cpm₁
      eqBindId₂ = cpmLawEqBindId cpm₂
      
      idMorph¬∃₁ = cpmIdMorph¬∃ cpm₁
      idMorph¬∃₂ = cpmIdMorph¬∃ cpm₂
      
      lawId₁ = pmLawId pm₁
      lawId₂ = pmLawId pm₂

      ⟨_⟩ : TyCons → TyCon
      ⟨ inj₁ IdentTC ⟩ = Identity
      ⟨ (inj₂ (inj₁ tc)) ⟩ = ⟨ pm₁ ▷ inj₂ tc ⟩
      ⟨ (inj₂ (inj₂ tc)) ⟩ = ⟨ pm₂ ▷ inj₂ tc ⟩

      injIdTC : ∀ {TCs : Set} → IdTyCons ⊎ TCs
      injIdTC = inj₁ IdentTC
      
      TC₁→TC : IdTyCons ⊎ TyCons₁ → TyCons
      TC₁→TC (inj₁ IdentTC) = inj₁ IdentTC
      TC₁→TC (inj₂ tc) = inj₂ (inj₁ tc)
      
      TC₂→TC : IdTyCons ⊎ TyCons₂ → TyCons
      TC₂→TC (inj₁ IdentTC) = inj₁ IdentTC
      TC₂→TC (inj₂ tc) = inj₂ (inj₂ tc)
      
      eqTC₁ : (M : IdTyCons ⊎ TyCons₁) → ⟨ pm₁ ▷ M ⟩ ≡ ⟨ TC₁→TC M ⟩
      eqTC₁ (inj₁ IdentTC) = eqId₁
      eqTC₁ (inj₂ tc) = refl
      
      eqTC₂ : (M : IdTyCons ⊎ TyCons₂) → ⟨ pm₂ ▷ M ⟩ ≡ ⟨ TC₂→TC M ⟩
      eqTC₂ (inj₁ IdentTC) = eqId₂
      eqTC₂ (inj₂ tc) = refl
      
      idBind1→2 : B[ idTC , idTC ] pm₁ ▷ idTC → B[ idTC , idTC ] pm₂ ▷ idTC
      idBind1→2 b = subst (λ X → X) eqIdBind b
      
      idBind2→1 : B[ idTC , idTC ] pm₂ ▷ idTC → B[ idTC , idTC ] pm₁ ▷ idTC
      idBind2→1 b = subst (λ X → X) (sym eqIdBind) b
      
      B[_,_]▷_ : (M N P : TyCons) → Set
      B[ inj₁ IdentTC   , inj₁ IdentTC   ]▷ inj₁ IdentTC   = B[ idTC , idTC ] pm₁ ▷ idTC
      B[ inj₁ IdentTC   , inj₁ IdentTC   ]▷ inj₂ (inj₁ P₁) = B[ inj₁ IdentTC , inj₁ IdentTC ] pm₁ ▷ inj₂ P₁
      B[ inj₁ IdentTC   , inj₁ IdentTC   ]▷ inj₂ (inj₂ P₂) = B[ inj₁ IdentTC , inj₁ IdentTC ] pm₂ ▷ inj₂ P₂
      B[ inj₁ IdentTC   , inj₂ (inj₁ N₁) ]▷ inj₁ IdentTC   = B[ inj₁ IdentTC , inj₂ N₁      ] pm₁ ▷ inj₁ IdentTC
      B[ inj₁ IdentTC   , inj₂ (inj₁ N₁) ]▷ inj₂ (inj₁ P₁) = B[ inj₁ IdentTC , inj₂ N₁      ] pm₁ ▷ inj₂ P₁
      B[ inj₁ IdentTC   , inj₂ (inj₁ N₁) ]▷ inj₂ (inj₂ P₂) = ⊥
      B[ inj₁ IdentTC   , inj₂ (inj₂ N₂) ]▷ inj₁ IdentTC   = B[ inj₁ IdentTC , inj₂ N₂      ] pm₂ ▷ inj₁ IdentTC
      B[ inj₁ IdentTC   , inj₂ (inj₂ N₂) ]▷ inj₂ (inj₁ P₁) = ⊥
      B[ inj₁ IdentTC   , inj₂ (inj₂ N₂) ]▷ inj₂ (inj₂ P₂) = B[ inj₁ IdentTC , inj₂ N₂      ] pm₂ ▷ inj₂ P₂
      B[ inj₂ (inj₁ M₁) , inj₁ IdentTC   ]▷ inj₁ IdentTC   = B[ inj₂ M₁      , inj₁ IdentTC ] pm₁ ▷ inj₁ IdentTC
      B[ inj₂ (inj₁ M₁) , inj₁ IdentTC   ]▷ inj₂ (inj₁ P₁) = B[ inj₂ M₁      , inj₁ IdentTC ] pm₁ ▷ inj₂ P₁
      B[ inj₂ (inj₁ M₁) , inj₁ IdentTC   ]▷ inj₂ (inj₂ P₂) = ⊥
      B[ inj₂ (inj₁ M₁) , inj₂ (inj₁ N₁) ]▷ inj₁ IdentTC   = B[ inj₂ M₁      , inj₂ N₁      ] pm₁ ▷ inj₁ IdentTC
      B[ inj₂ (inj₁ M₁) , inj₂ (inj₁ N₁) ]▷ inj₂ (inj₁ P₁) = B[ inj₂ M₁      , inj₂ N₁      ] pm₁ ▷ inj₂ P₁
      B[ inj₂ (inj₁ M₁) , inj₂ (inj₁ N₁) ]▷ inj₂ (inj₂ P₂) = ⊥
      B[ inj₂ (inj₁ M₁) , inj₂ (inj₂ N₂) ]▷ inj₁ IdentTC   = ⊥
      B[ inj₂ (inj₁ M₁) , inj₂ (inj₂ N₂) ]▷ inj₂ (inj₁ P₁) = ⊥
      B[ inj₂ (inj₁ M₁) , inj₂ (inj₂ N₂) ]▷ inj₂ (inj₂ P₂) = ⊥
      B[ inj₂ (inj₂ M₂) , inj₁ IdentTC   ]▷ inj₁ IdentTC   = B[ inj₂ M₂      , inj₁ IdentTC ] pm₂ ▷ inj₁ IdentTC
      B[ inj₂ (inj₂ M₂) , inj₁ IdentTC   ]▷ inj₂ (inj₁ P₁) = ⊥
      B[ inj₂ (inj₂ M₂) , inj₁ IdentTC   ]▷ inj₂ (inj₂ P₂) = B[ inj₂ M₂      , inj₁ IdentTC ] pm₂ ▷ inj₂ P₂
      B[ inj₂ (inj₂ M₂) , inj₂ (inj₁ N₁) ]▷ inj₁ IdentTC   = ⊥
      B[ inj₂ (inj₂ M₂) , inj₂ (inj₁ N₁) ]▷ inj₂ (inj₁ P₁) = ⊥
      B[ inj₂ (inj₂ M₂) , inj₂ (inj₁ N₁) ]▷ inj₂ (inj₂ P₂) = ⊥
      B[ inj₂ (inj₂ M₂) , inj₂ (inj₂ N₂) ]▷ inj₁ IdentTC   = B[ inj₂ M₂      , inj₂ N₂      ] pm₂ ▷ inj₁ IdentTC
      B[ inj₂ (inj₂ M₂) , inj₂ (inj₂ N₂) ]▷ inj₂ (inj₁ P₁) = ⊥
      B[ inj₂ (inj₂ M₂) , inj₂ (inj₂ N₂) ]▷ inj₂ (inj₂ P₂) = B[ inj₂ M₂      , inj₂ N₂      ] pm₂ ▷ inj₂ P₂
      
      bindConv₁ : ∀ (M N P : IdTyCons ⊎ TyCons₁) → B[ M , N ] pm₁ ▷ P → B[ TC₁→TC M , TC₁→TC N ]▷ TC₁→TC P
      bindConv₁ (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) b = b
      bindConv₁ (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ P) b = b
      bindConv₁ (inj₁ IdentTC) (inj₂ N) (inj₁ IdentTC) b = b
      bindConv₁ (inj₁ IdentTC) (inj₂ N) (inj₂ P) b = b
      bindConv₁ (inj₂ M) (inj₁ IdentTC) (inj₁ IdentTC) b = b
      bindConv₁ (inj₂ M) (inj₁ IdentTC) (inj₂ P) b = b
      bindConv₁ (inj₂ M) (inj₂ N) (inj₁ IdentTC) b = b
      bindConv₁ (inj₂ M) (inj₂ N) (inj₂ P) b = b
      
      bindConv₂ : ∀ (M N P : IdTyCons ⊎ TyCons₂) → B[ M , N ] pm₂ ▷ P → B[ TC₂→TC M , TC₂→TC N ]▷ TC₂→TC P
      bindConv₂ (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) b = idBind2→1 b
      bindConv₂ (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ P) b = b
      bindConv₂ (inj₁ IdentTC) (inj₂ N) (inj₁ IdentTC) b = b
      bindConv₂ (inj₁ IdentTC) (inj₂ N) (inj₂ P) b = b
      bindConv₂ (inj₂ M) (inj₁ IdentTC) (inj₁ IdentTC) b = b
      bindConv₂ (inj₂ M) (inj₁ IdentTC) (inj₂ P) b = b
      bindConv₂ (inj₂ M) (inj₂ N) (inj₁ IdentTC) b = b
      bindConv₂ (inj₂ M) (inj₂ N) (inj₂ P) b = b
      
      bind : ∀ {M N P : TyCons} → B[ M , N ]▷ P → [ ⟨ M ⟩ , ⟨ N ⟩ ]▷ ⟨ P ⟩
      bind {inj₁ IdentTC} {inj₁ IdentTC} {inj₁ IdentTC} b₁ = substBind eqId₁ eqId₁ eqId₁ (pmBind pm₁ b₁)
      bind {inj₁ IdentTC  } {inj₁ IdentTC  } {inj₂ (inj₁ P₁)} t  = substBind eqId₁ eqId₁ (eqTC₁ (inj₂ P₁)) (pmBind pm₁ t)
      bind {inj₁ IdentTC  } {inj₁ IdentTC  } {inj₂ (inj₂ P₂)} t  = substBind eqId₂ eqId₂ (eqTC₂ (inj₂ P₂)) (pmBind pm₂ t)
      bind {inj₁ IdentTC  } {inj₂ (inj₁ N₁)} {inj₁ IdentTC  } t  = substBind eqId₁ (eqTC₁ (inj₂ N₁)) eqId₁ (pmBind pm₁ t)
      bind {inj₁ IdentTC  } {inj₂ (inj₁ N₁)} {inj₂ (inj₁ P₁)} t  = substBind eqId₁ (eqTC₁ (inj₂ N₁)) (eqTC₁ (inj₂ P₁)) (pmBind pm₁ t)
      bind {inj₁ IdentTC  } {inj₂ (inj₁ N₁)} {inj₂ (inj₂ P₂)} ()
      bind {inj₁ IdentTC  } {inj₂ (inj₂ N₂)} {inj₁ IdentTC  } t  = substBind eqId₂ (eqTC₂ (inj₂ N₂)) eqId₂ (pmBind pm₂ t)
      bind {inj₁ IdentTC  } {inj₂ (inj₂ N₂)} {inj₂ (inj₁ P₁)} ()
      bind {inj₁ IdentTC  } {inj₂ (inj₂ N₂)} {inj₂ (inj₂ P₂)} t  = substBind eqId₂ (eqTC₂ (inj₂ N₂)) (eqTC₂ (inj₂ P₂)) (pmBind pm₂ t)
      bind {inj₂ (inj₁ M₁)} {inj₁ IdentTC  } {inj₁ IdentTC  } t  = substBind (eqTC₁ (inj₂ M₁)) eqId₁ eqId₁ (pmBind pm₁ t)
      bind {inj₂ (inj₁ M₁)} {inj₁ IdentTC  } {inj₂ (inj₁ P₁)} t  = substBind (eqTC₁ (inj₂ M₁)) eqId₁ (eqTC₁ (inj₂ P₁)) (pmBind pm₁ t)
      bind {inj₂ (inj₁ M₁)} {inj₁ IdentTC  } {inj₂ (inj₂ P₂)} ()
      bind {inj₂ (inj₁ M₁)} {inj₂ (inj₁ N₁)} {inj₁ IdentTC  } t  = substBind (eqTC₁ (inj₂ M₁)) (eqTC₁ (inj₂ N₁)) eqId₁ (pmBind pm₁ t)
      bind {inj₂ (inj₁ M₁)} {inj₂ (inj₁ N₁)} {inj₂ (inj₁ P₁)} t  = substBind (eqTC₁ (inj₂ M₁)) (eqTC₁ (inj₂ N₁)) (eqTC₁ (inj₂ P₁)) (pmBind pm₁ t)
      bind {inj₂ (inj₁ M₁)} {inj₂ (inj₁ N₁)} {inj₂ (inj₂ P₂)} ()
      bind {inj₂ (inj₁ M₁)} {inj₂ (inj₂ N₂)} {inj₁ IdentTC  } ()
      bind {inj₂ (inj₁ M₁)} {inj₂ (inj₂ N₂)} {inj₂ (inj₁ P₁)} ()
      bind {inj₂ (inj₁ M₁)} {inj₂ (inj₂ N₂)} {inj₂ (inj₂ P₂)} ()
      bind {inj₂ (inj₂ M₂)} {inj₁ IdentTC  } {inj₁ IdentTC  } t  = substBind (eqTC₂ (inj₂ M₂)) eqId₂ eqId₂ (pmBind pm₂ t)
      bind {inj₂ (inj₂ M₂)} {inj₁ IdentTC  } {inj₂ (inj₁ P₁)} ()
      bind {inj₂ (inj₂ M₂)} {inj₁ IdentTC  } {inj₂ (inj₂ P₂)} t  = substBind (eqTC₂ (inj₂ M₂)) eqId₂ (eqTC₂ (inj₂ P₂)) (pmBind pm₂ t)
      bind {inj₂ (inj₂ M₂)} {inj₂ (inj₁ N₁)} {inj₁ IdentTC  } ()
      bind {inj₂ (inj₂ M₂)} {inj₂ (inj₁ N₁)} {inj₂ (inj₁ P₁)} ()
      bind {inj₂ (inj₂ M₂)} {inj₂ (inj₁ N₁)} {inj₂ (inj₂ P₂)} ()
      bind {inj₂ (inj₂ M₂)} {inj₂ (inj₂ N₂)} {inj₁ IdentTC  } t  = substBind (eqTC₂ (inj₂ M₂)) (eqTC₂ (inj₂ N₂)) eqId₂ (pmBind pm₂ t)
      bind {inj₂ (inj₂ M₂)} {inj₂ (inj₂ N₂)} {inj₂ (inj₁ P₁)} () 
      bind {inj₂ (inj₂ M₂)} {inj₂ (inj₂ N₂)} {inj₂ (inj₂ P₂)} t  = substBind (eqTC₂ (inj₂ M₂)) (eqTC₂ (inj₂ N₂)) (eqTC₂ (inj₂ P₂)) (pmBind pm₂ t)
      
      lawId : ⟨ Id ⟩ ≡ Identity
      lawId = pmLawId polymonadId

      eqIdSubst : {Id : TyCon}
                → {α : Type}
                → (eqId' : Id ≡ Identity)
                → id lawId ≡ subst (λ N → (α → N α)) eqId' (id eqId')
      eqIdSubst refl = refl
      
      lawFunctor : (M : TyCons) 
                  → ∃ λ (b : B[ M , Id ]▷ M) 
                  → {α : Type} (m : ⟨ M ⟩ α) 
                  → bind {M} {Id} {M} b m (id lawId) ≡ m
      lawFunctor (inj₁ IdentTC  ) = 
        let b₁ , proof₁ = pmLawFunctor pm₁ idTC
            M = inj₁ IdentTC
            eqM = eqId₁
            proof : ∀ {α : Type} → (m : ⟨ M ⟩ α) → bind {M} {Id} {M} b₁ m (id lawId) ≡ m
            proof {α} m = begin
              bind {M} {Id} {M} b₁ m (id lawId)  
                ≡⟨ cong (λ x → x m (id lawId)) (eqBindId₁ b₁) ⟩
              bindId m (id lawId) 
                ≡⟨ refl ⟩
              m ∎
        in b₁ , proof
      lawFunctor (inj₂ (inj₁ M₁)) = 
        let b₁ , proof₁ = pmLawFunctor pm₁ (inj₂ M₁)
            M = inj₂ (inj₁ M₁)
            eqM = eqTC₁ (inj₂ M₁)
            proof : ∀ {α : Type} → (m : ⟨ M ⟩ α) → bind {M} {Id} {M} b₁ m (id lawId) ≡ m
            proof {α} m = begin
              bind {M} {Id} {M} b₁ m (id lawId)
                ≡⟨ cong (λ x → bind {M} {Id} {M} b₁ m x) (eqIdSubst eqId₁) ⟩
              bind {M} {Id} {M} b₁ m (subst (λ N → (α → N α)) eqId₁ (id lawId₁)) 
                ≡⟨ refl ⟩
              substBind refl eqId₁ refl (pmBind pm₁ b₁) m (subst (λ N → (α → N α)) eqId₁ (id lawId₁)) 
                ≡⟨ substBindInwardEq (pmBind pm₁ b₁) eqM eqId₁ eqM m (subst (λ N → (α → N α)) eqId₁ (id lawId₁)) ⟩
              subst (λ P → P α) eqM (pmBind pm₁ b₁ (subst (λ M → M α) eqM m) (subst (λ N → (α → N α)) (sym eqId₁) (subst (λ N → (α → N α)) eqId₁ (id lawId₁)) ) )
                ≡⟨ cong (λ q → subst (λ P → P α) eqM (pmBind pm₁ b₁ (subst (λ M → M α) eqM m) q)) (sym (f≡subst²f eqId₁)) ⟩
              subst (λ P → P α) eqM (pmBind pm₁ b₁ (subst (λ M → M α) eqM m) (id lawId₁))
                ≡⟨ cong (λ x → subst (λ P → P α) eqM x) (proof₁ (subst (λ M → M α) eqM m)) ⟩ -- pmBind pm₁ b₁ m (pmId→ pm₁) ≡ m
              subst (λ P → P α) eqM (subst (λ M → M α) eqM m)
                ≡⟨ refl ⟩
              m ∎
        in b₁ , proof
      lawFunctor (inj₂ (inj₂ M₂)) = 
        let b₂ , proof₂ = pmLawFunctor pm₂ (inj₂ M₂)
            M = inj₂ (inj₂ M₂)
            eqM = eqTC₂ (inj₂ M₂)
            proof : ∀ {α : Type} → (m : ⟨ M ⟩ α) → bind {M} {Id} {M} b₂ m (id lawId) ≡ m
            proof {α} m = begin
              bind {M} {Id} {M} b₂ m (id lawId) 
                ≡⟨ cong (λ x → bind {M} {Id} {M} b₂ m x) (eqIdSubst eqId₂) ⟩
              bind {M} {Id} {M} b₂ m (subst (λ N → (α → N α)) eqId₂ (id lawId₂)) 
                ≡⟨ refl ⟩
              substBind refl eqId₂ refl (pmBind pm₂ b₂) m (subst (λ N → (α → N α)) eqId₂ (id lawId₂)) 
                ≡⟨ substBindInwardEq (pmBind pm₂ b₂) eqM eqId₂ eqM m (subst (λ N → (α → N α)) eqId₂ (id lawId₂)) ⟩
              subst (λ P → P α) eqM (pmBind pm₂ b₂ (subst (λ M → M α) eqM m) (subst (λ N → (α → N α)) (sym eqId₂) (subst (λ N → (α → N α)) eqId₂ (id lawId₂)) ) )
                ≡⟨ cong (λ q → subst (λ P → P α) eqM (pmBind pm₂ b₂ (subst (λ M → M α) eqM m) q)) (sym (f≡subst²f eqId₂)) ⟩
              subst (λ P → P α) eqM (pmBind pm₂ b₂ (subst (λ M → M α) eqM m) (id lawId₂))
                ≡⟨ cong (λ x → subst (λ P → P α) eqM x) (proof₂ (subst (λ M → M α) eqM m)) ⟩ -- pmBind pm₂ b₂ m (pmId→ pm₂) ≡ m
              subst (λ P → P α) eqM (subst (λ M → M α) eqM m)
                ≡⟨ refl ⟩
              m ∎
        in b₂ , proof

      lawMorph1 : ∀ (M P : TyCons) 
                → (B[ M , Id ]▷ P → B[ Id , M ]▷ P)
      lawMorph1 (inj₁ IdentTC  ) (inj₁ IdentTC  ) b = pmLawMorph1 pm₁ (inj₁ IdentTC) idTC b
      lawMorph1 (inj₁ IdentTC  ) (inj₂ (inj₁ P₁)) b = pmLawMorph1 pm₁ (inj₁ IdentTC) (inj₂ P₁) b
      lawMorph1 (inj₁ IdentTC  ) (inj₂ (inj₂ P₂)) b = pmLawMorph1 pm₂ (inj₁ IdentTC) (inj₂ P₂) b
      lawMorph1 (inj₂ (inj₁ M₁)) (inj₁ IdentTC  ) b = pmLawMorph1 pm₁ (inj₂ M₁) (inj₁ IdentTC) b
      lawMorph1 (inj₂ (inj₁ M₁)) (inj₂ (inj₁ P₁)) b = pmLawMorph1 pm₁ (inj₂ M₁) (inj₂ P₁) b
      lawMorph1 (inj₂ (inj₁ M₁)) (inj₂ (inj₂ P₁)) ()
      lawMorph1 (inj₂ (inj₂ M₂)) (inj₁ IdentTC  ) b = pmLawMorph1 pm₂ (inj₂ M₂) (inj₁ IdentTC) b
      lawMorph1 (inj₂ (inj₂ M₂)) (inj₂ (inj₁ P₁)) ()
      lawMorph1 (inj₂ (inj₂ M₂)) (inj₂ (inj₂ P₂)) b = pmLawMorph1 pm₂ (inj₂ M₂) (inj₂ P₂) b
      
      lawMorph2 : ∀ (M P : TyCons) 
                → (B[ Id , M ]▷ P → B[ M , Id ]▷ P)
      lawMorph2 (inj₁ IdentTC  ) (inj₁ IdentTC  ) b = pmLawMorph2 pm₁ (inj₁ IdentTC) idTC b
      lawMorph2 (inj₁ IdentTC  ) (inj₂ (inj₁ P₁)) b = pmLawMorph2 pm₁ (inj₁ IdentTC) (inj₂ P₁) b
      lawMorph2 (inj₁ IdentTC  ) (inj₂ (inj₂ P₂)) b = pmLawMorph2 pm₂ (inj₁ IdentTC) (inj₂ P₂) b
      lawMorph2 (inj₂ (inj₁ M₁)) (inj₁ IdentTC  ) b = pmLawMorph2 pm₁ (inj₂ M₁) (inj₁ IdentTC) b
      lawMorph2 (inj₂ (inj₁ M₁)) (inj₂ (inj₁ P₁)) b = pmLawMorph2 pm₁ (inj₂ M₁) (inj₂ P₁) b
      lawMorph2 (inj₂ (inj₁ M₁)) (inj₂ (inj₂ P₁)) ()
      lawMorph2 (inj₂ (inj₂ M₂)) (inj₁ IdentTC  ) b = pmLawMorph2 pm₂ (inj₂ M₂) (inj₁ IdentTC) b
      lawMorph2 (inj₂ (inj₂ M₂)) (inj₂ (inj₁ P₁)) ()
      lawMorph2 (inj₂ (inj₂ M₂)) (inj₂ (inj₂ P₂)) b = pmLawMorph2 pm₂ (inj₂ M₂) (inj₂ P₂) b
    
      lawMorph3Proof₁ : (M P : IdTyCons ⊎ TyCons₁)
                      → (b₁ : B[ TC₁→TC M , TC₁→TC injIdTC ]▷ TC₁→TC P) 
                      → (b₂ : B[ TC₁→TC injIdTC , TC₁→TC M ]▷ TC₁→TC P)
                      → (eqBind₁ : B[ TC₁→TC M , TC₁→TC injIdTC ]▷ TC₁→TC P ≡ B[ M , injIdTC ] pm₁ ▷ P)
                      → (eqBind₂ : B[ TC₁→TC injIdTC , TC₁→TC M ]▷ TC₁→TC P ≡ B[ injIdTC , M ] pm₁ ▷ P)
                      → ∀ {α β : Type} (v : α) (f : α → ⟨ TC₁→TC M ⟩ β) 
                      → ( bind {TC₁→TC M} {TC₁→TC injIdTC} {TC₁→TC P} b₁ (f v) (subst (λ X → (β → X β)) eqId₁ (id lawId₁)) 
                        ≡ substBind (eqTC₁ M) eqId₁ (eqTC₁ P) (pmBind pm₁ (subst (λ x → x) eqBind₁ b₁)) (f v) (subst (λ X → (β → X β)) eqId₁ (id lawId₁)) )
                      → ( substBind eqId₁ (eqTC₁ M) (eqTC₁ P) (pmBind pm₁ (subst (λ x → x) eqBind₂ b₂)) ((subst (λ X → (α → X α)) eqId₁ (id lawId₁)) v) f 
                        ≡ bind {TC₁→TC injIdTC} {TC₁→TC M} {TC₁→TC P} b₂ ((subst (λ X → (α → X α)) eqId₁ (id lawId₁)) v) f )
                      → ( (bind {TC₁→TC M} {TC₁→TC injIdTC} {TC₁→TC P} b₁) (f v) (id lawId)
                        ≡ (bind {TC₁→TC injIdTC} {TC₁→TC M} {TC₁→TC P} b₂) (id lawId v) f )
      lawMorph3Proof₁ M P b₁ b₂ eqBind₁ eqBind₂ {α = α} {β = β} v f eqSubstBind₁ eqSubstBind₂ =
        let bind₁ = bind {TC₁→TC M} {TC₁→TC injIdTC} {TC₁→TC P} b₁
            bind₂ = bind {TC₁→TC injIdTC} {TC₁→TC M} {TC₁→TC P} b₂
            eqM = eqTC₁ M
            eqP = eqTC₁ P
            eqId = eqId₁
            pm = pm₁
            pmb₁ = pmBind pm (subst (λ x → x) eqBind₁ b₁)
            pmb₂ = pmBind pm (subst (λ x → x) eqBind₂ b₂)
        in begin
          bind₁ (f v) (id lawId)
            ≡⟨ cong (bind₁ (f v)) (eqIdSubst eqId) ⟩
          bind₁ (f v) (subst (λ X → (β → X β)) eqId (id lawId₁))
            ≡⟨ eqSubstBind₁ ⟩
          substBind eqM eqId eqP pmb₁ (f v) (subst (λ X → (β → X β)) eqId (id lawId₁)) 
            ≡⟨ substBindInwardEq pmb₁ eqM eqId eqP (f v) (subst (λ X → (β → X β)) eqId (id lawId₁)) ⟩
          subst (λ X → X β) eqP (pmb₁ (subst (λ X → X β) (sym eqM) (f v)) (subst (λ N → (β → N β)) (sym eqId) (subst (λ X → (β → X β)) eqId (id lawId₁))) ) 
            ≡⟨ cong (λ x → subst (λ X → X β) eqP (pmb₁ (subst (λ X → X β) (sym eqM) (f v)) x )) (sym (f≡subst²f eqId)) ⟩
          subst (λ X → X β) eqP (pmb₁ (subst (λ X → X β) (sym eqM) (f v)) (id lawId₁) )
            ≡⟨ cong (subst (λ X → X β) eqP) (pmLawMorph3 pm M P (subst (λ x → x) eqBind₁ b₁) (subst (λ x → x) eqBind₂ b₂) v ((λ x → subst (λ M → M β) (sym eqM) (f x)))) ⟩
          subst (λ X → X β) eqP (pmb₂ ((id lawId₁) v) (λ x → subst (λ X → X β) (sym eqM) (f x)) )
            ≡⟨ cong (λ x → subst (λ X → X β) eqP (pmb₂ ((id lawId₁) v) x) ) (shiftFunSubst (sym eqM) f) ⟩
          subst (λ X → X β) eqP (pmb₂ ((id lawId₁) v) (subst (λ X → (α → X β)) (sym eqM) f)) 
            ≡⟨ cong (λ x → subst (λ X → X β) eqP (pmb₂ x (subst (λ X → (α → X β)) (sym eqM) f))) (x≡subst²x eqId) ⟩
          subst (λ X → X β) eqP (pmb₂ (subst (λ X → X α) (sym eqId) (subst (λ X → (X α)) eqId ((id lawId₁) v))) (subst (λ X → (α → X β)) (sym eqM) f)) 
            ≡⟨ cong (λ x → subst (λ X → X β) eqP (pmb₂ (subst (λ X → X α) (sym eqId) x) (subst (λ X → (α → X β)) (sym eqM) f)) ) (sym (shiftApplySubst eqId v (id lawId₁))) ⟩
          subst (λ X → X β) eqP (pmb₂ (subst (λ X → X α) (sym eqId) ((subst (λ X → (α → X α)) eqId (id lawId₁)) v)) (subst (λ X → (α → X β)) (sym eqM) f)) 
            ≡⟨ sym (substBindInwardEq pmb₂ eqId eqM eqP ((subst (λ X → (α → X α)) eqId (id lawId₁)) v) f) ⟩
          substBind eqId eqM eqP pmb₂ ((subst (λ X → (α → X α)) eqId (id lawId₁)) v) f 
            ≡⟨ eqSubstBind₂ ⟩
          bind₂ ((subst (λ X → (α → X α)) eqId (id lawId₁)) v) f
            ≡⟨ cong (λ x → bind₂ (x v) f) (sym (eqIdSubst eqId)) ⟩
          bind₂ (id lawId v) f ∎

      lawMorph3Proof₂ : (M P : IdTyCons ⊎ TyCons₂)
                      → (b₁ : B[ TC₂→TC M , TC₂→TC injIdTC ]▷ TC₂→TC P) 
                      → (b₂ : B[ TC₂→TC injIdTC , TC₂→TC M ]▷ TC₂→TC P)
                      → (eqBind₁ : B[ TC₂→TC M , TC₂→TC injIdTC ]▷ TC₂→TC P ≡ B[ M , injIdTC ] pm₂ ▷ P)
                      → (eqBind₂ : B[ TC₂→TC injIdTC , TC₂→TC M ]▷ TC₂→TC P ≡ B[ injIdTC , M ] pm₂ ▷ P)
                      → ∀ {α β : Type} (v : α) (f : α → ⟨ TC₂→TC M ⟩ β) 
                      → ( bind {TC₂→TC M} {TC₂→TC injIdTC} {TC₂→TC P} b₁ (f v) (subst (λ X → (β → X β)) eqId₂ (id lawId₂)) 
                        ≡ substBind (eqTC₂ M) eqId₂ (eqTC₂ P) (pmBind pm₂ (subst (λ x → x) eqBind₁ b₁)) (f v) (subst (λ X → (β → X β)) eqId₂ (id lawId₂)) )
                      → ( substBind eqId₂ (eqTC₂ M) (eqTC₂ P) (pmBind pm₂ (subst (λ x → x) eqBind₂ b₂)) ((subst (λ X → (α → X α)) eqId₂ (id lawId₂)) v) f 
                        ≡ bind {TC₂→TC injIdTC} {TC₂→TC M} {TC₂→TC P} b₂ ((subst (λ X → (α → X α)) eqId₂ (id lawId₂)) v) f )
                      → ( (bind {TC₂→TC M} {TC₂→TC injIdTC} {TC₂→TC P} b₁) (f v) (id lawId)
                        ≡ (bind {TC₂→TC injIdTC} {TC₂→TC M} {TC₂→TC P} b₂) (id lawId v) f )
      lawMorph3Proof₂ M P b₁ b₂ eqBind₁ eqBind₂ {α = α} {β = β} v f eqSubstBind₁ eqSubstBind₂ =
        let bind₁ = bind {TC₂→TC M} {TC₂→TC injIdTC} {TC₂→TC P} b₁
            bind₂ = bind {TC₂→TC injIdTC} {TC₂→TC M} {TC₂→TC P} b₂
            eqM = eqTC₂ M
            eqP = eqTC₂ P
            eqId = eqId₂
            pm = pm₂
            pmb₁ = pmBind pm (subst (λ x → x) eqBind₁ b₁)
            pmb₂ = pmBind pm (subst (λ x → x) eqBind₂ b₂)
        in begin
          bind₁ (f v) (id lawId)
            ≡⟨ cong (bind₁ (f v)) (eqIdSubst eqId) ⟩
          bind₁ (f v) (subst (λ X → (β → X β)) eqId (id lawId₂))
            ≡⟨ eqSubstBind₁ ⟩
          substBind eqM eqId eqP pmb₁ (f v) (subst (λ X → (β → X β)) eqId (id lawId₂)) 
            ≡⟨ substBindInwardEq pmb₁ eqM eqId eqP (f v) (subst (λ X → (β → X β)) eqId (id lawId₂)) ⟩
          subst (λ X → X β) eqP (pmb₁ (subst (λ X → X β) (sym eqM) (f v)) (subst (λ N → (β → N β)) (sym eqId) (subst (λ X → (β → X β)) eqId (id lawId₂))) ) 
            ≡⟨ cong (λ x → subst (λ X → X β) eqP (pmb₁ (subst (λ X → X β) (sym eqM) (f v)) x )) (sym (f≡subst²f eqId)) ⟩
          subst (λ X → X β) eqP (pmb₁ (subst (λ X → X β) (sym eqM) (f v)) (id lawId₂) )
            ≡⟨ cong (subst (λ X → X β) eqP) (pmLawMorph3 pm M P (subst (λ x → x) eqBind₁ b₁) (subst (λ x → x) eqBind₂ b₂) v ((λ x → subst (λ M → M β) (sym eqM) (f x)))) ⟩
          subst (λ X → X β) eqP (pmb₂ ((id lawId₂) v) (λ x → subst (λ X → X β) (sym eqM) (f x)) )
            ≡⟨ cong (λ x → subst (λ X → X β) eqP (pmb₂ ((id lawId₂) v) x) ) (shiftFunSubst (sym eqM) f) ⟩
          subst (λ X → X β) eqP (pmb₂ ((id lawId₂) v) (subst (λ X → (α → X β)) (sym eqM) f)) 
            ≡⟨ cong (λ x → subst (λ X → X β) eqP (pmb₂ x (subst (λ X → (α → X β)) (sym eqM) f))) (x≡subst²x eqId) ⟩
          subst (λ X → X β) eqP (pmb₂ (subst (λ X → X α) (sym eqId) (subst (λ X → (X α)) eqId ((id lawId₂) v))) (subst (λ X → (α → X β)) (sym eqM) f)) 
            ≡⟨ cong (λ x → subst (λ X → X β) eqP (pmb₂ (subst (λ X → X α) (sym eqId) x) (subst (λ X → (α → X β)) (sym eqM) f)) ) (sym (shiftApplySubst eqId v (id lawId₂))) ⟩
          subst (λ X → X β) eqP (pmb₂ (subst (λ X → X α) (sym eqId) ((subst (λ X → (α → X α)) eqId (id lawId₂)) v)) (subst (λ X → (α → X β)) (sym eqM) f)) 
            ≡⟨ sym (substBindInwardEq pmb₂ eqId eqM eqP ((subst (λ X → (α → X α)) eqId (id lawId₂)) v) f) ⟩
          substBind eqId eqM eqP pmb₂ ((subst (λ X → (α → X α)) eqId (id lawId₂)) v) f 
            ≡⟨ eqSubstBind₂ ⟩
          bind₂ ((subst (λ X → (α → X α)) eqId (id lawId₂)) v) f
            ≡⟨ cong (λ x → bind₂ (x v) f) (sym (eqIdSubst eqId)) ⟩
          bind₂ (id lawId v) f ∎

      lawMorph3 : ∀ (M P : TyCons) (b₁ : B[ M , Id ]▷ P) (b₂ : B[ Id , M ]▷ P)
                → ∀ {α β : Type} (v : α) (f : α → ⟨ M ⟩ β) 
                → (bind {M} {Id} {P} b₁) (f v) (id lawId) ≡ (bind {Id} {M} {P} b₂) (id lawId v) f
      lawMorph3 (inj₁ IdentTC  ) (inj₁ IdentTC  ) b₁ b₂ {α = α} {β = β} v f = lawMorph3Proof₁ idTC   idTC         b₁ b₂ refl refl {α = α} {β = β} v f refl refl
      lawMorph3 (inj₁ IdentTC  ) (inj₂ (inj₁ P₁)) b₁ b₂ {α = α} {β = β} v f = lawMorph3Proof₁ idTC   (inj₂ P₁)    b₁ b₂ refl refl {α = α} {β = β} v f refl refl 
      lawMorph3 (inj₁ IdentTC  ) (inj₂ (inj₂ P₂)) b₁ b₂ {α = α} {β = β} v f = lawMorph3Proof₂ idTC   (inj₂ P₂)    b₁ b₂ refl refl {α = α} {β = β} v f refl refl
      lawMorph3 (inj₂ (inj₁ M₁)) (inj₁ IdentTC  ) b₁ b₂ {α = α} {β = β} v f = lawMorph3Proof₁ (inj₂ M₁) idTC      b₁ b₂ refl refl {α = α} {β = β} v f refl refl
      lawMorph3 (inj₂ (inj₁ M₁)) (inj₂ (inj₁ P₁)) b₁ b₂ {α = α} {β = β} v f = lawMorph3Proof₁ (inj₂ M₁) (inj₂ P₁) b₁ b₂ refl refl {α = α} {β = β} v f refl refl
      lawMorph3 (inj₂ (inj₁ M₁)) (inj₂ (inj₂ P₂)) () () v f
      lawMorph3 (inj₂ (inj₂ M₂)) (inj₁ IdentTC  ) b₁ b₂ {α = α} {β = β} v f = lawMorph3Proof₂ (inj₂ M₂) idTC      b₁ b₂ refl refl {α = α} {β = β} v f refl refl
      lawMorph3 (inj₂ (inj₂ M₂)) (inj₂ (inj₁ P₁)) () () v f
      lawMorph3 (inj₂ (inj₂ M₂)) (inj₂ (inj₂ P₂)) b₁ b₂ {α = α} {β = β} v f = lawMorph3Proof₂ (inj₂ M₂) (inj₂ P₂) b₁ b₂ refl refl {α = α} {β = β} v f refl refl
      
      lawDiamond1Proof₁ : ∀ {M N R T : IdTyCons ⊎ TyCons₁}
                        → (∃ λ(P : IdTyCons ⊎ TyCons₁) → B[ M , N ] pm₁ ▷ P × B[ P , R ] pm₁ ▷ T)
                        → (∃ λ(S : TyCons) → B[ TC₁→TC N , TC₁→TC R ]▷ S × B[ TC₁→TC M , S ]▷ TC₁→TC T)
      lawDiamond1Proof₁ {M} {N} {R} {T} (P , b₁ , b₂) with pmLawDiamond1 pm₁ M N R T (P , b₁ , b₂)
      lawDiamond1Proof₁ {M} {N} {R} {T} (P , b₁ , b₂) | S , b₃ , b₄ = TC₁→TC S , bindConv₁ N R S b₃ , bindConv₁ M S T b₄
      
      lawDiamond1Proof₂ : ∀ {M N R T : IdTyCons ⊎ TyCons₂}
                        → (∃ λ(P : IdTyCons ⊎ TyCons₂) → B[ M , N ] pm₂ ▷ P × B[ P , R ] pm₂ ▷ T)
                        → (∃ λ(S : TyCons) → B[ TC₂→TC N , TC₂→TC R ]▷ S × B[ TC₂→TC M , S ]▷ TC₂→TC T)
      lawDiamond1Proof₂ {M} {N} {R} {T} (P , b₁ , b₂) with pmLawDiamond1 pm₂ M N R T (P , b₁ , b₂)
      lawDiamond1Proof₂ {M} {N} {R} {T} (P , b₁ , b₂) | S , b₃ , b₄ = TC₂→TC S , bindConv₂ N R S b₃ , bindConv₂ M S T b₄

      lawDiamond1 : ∀ (M N R T : TyCons)
                → (∃ λ(P : TyCons) → B[ M , N ]▷ P × B[ P , R ]▷ T)
                → (∃ λ(S : TyCons) → B[ N , R ]▷ S × B[ M , S ]▷ T)
      lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC , b₁ , b₂) = lawDiamond1Proof₁ (idTC , b₁ , b₂)
      lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ P₁) , b₁ , b₂) = lawDiamond1Proof₁ (inj₂ P₁ , b₁ , b₂)
      lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ P₂) , b₁ , b₂) = lawDiamond1Proof₂ (inj₂ P₂ , b₁ , b₂)
      lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₁ IdentTC , b₁ , b₂) = lawDiamond1Proof₁ (idTC , b₁ , b₂)
      lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₂ (inj₁ P₁) , b₁ , b₂) = lawDiamond1Proof₁ (inj₂ P₁ , b₁ , b₂)
      lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₂ (inj₂ P₂) , b₁ , ())
      lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₁ IdentTC , b₁ , b₂) = lawDiamond1Proof₂ (idTC , idBind1→2 b₁ , b₂)
      lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₂ (inj₁ P₁) , b₁ , ())
      lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₂ (inj₂ P₂) , b₁ , b₂) = lawDiamond1Proof₂ (inj₂ P₂ , b₁ , b₂)
      lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₁ IdentTC , b₁ , b₂) = lawDiamond1Proof₁ (idTC , b₁ , b₂)
      lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₂ (inj₁ T₁)) (inj₁ IdentTC , b₁ , b₂) = lawDiamond1Proof₁ (idTC , b₁ , b₂)
      lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₂ (inj₂ T₂)) (inj₁ IdentTC , b₁ , ())
      lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₂ (inj₁ P₁) , b₁ , b₂) = lawDiamond1Proof₁ (inj₂ P₁ , b₁ , b₂)
      lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₂ (inj₂ P₂) , b₁ , ())
      lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₂ (inj₁ T₁)) (inj₂ (inj₁ P₁) , b₁ , b₂) = lawDiamond1Proof₁ (inj₂ P₁ , b₁ , b₂)
      lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₂ (inj₁ T₁)) (inj₂ (inj₂ P₂) , b₁ , ())
      lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₂ (inj₂ T₂)) (inj₂ (inj₁ P₁) , b₁ , ())
      lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₂ (inj₂ T₂)) (inj₂ (inj₂ P₂) , b₁ , ())
      lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₁ IdentTC , b₁ , b₂) = lawDiamond1Proof₂ (idTC , idBind1→2 b₁ , b₂)
      lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₂ (inj₁ P₁) , b₁ , ())
      lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₂ (inj₂ P₂) , b₁ , b₂) = lawDiamond1Proof₂ (inj₂ P₂ , b₁ , b₂)
      lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₂ (inj₁ T₁)) (inj₁ IdentTC , b₁ , ())
      lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₂ (inj₁ T₁)) (inj₂ (inj₁ P₁) , b₁ , ())
      lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₂ (inj₁ T₁)) (inj₂ (inj₂ P₂) , b₁ , ())
      lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₂ (inj₂ T₂)) (inj₁ IdentTC , b₁ , b₂) = lawDiamond1Proof₂ (inj₁ IdentTC , idBind1→2 b₁ , b₂)
      lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₂ (inj₂ T₂)) (inj₂ (inj₁ P₁) , b₁ , ())
      lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₂ (inj₂ T₂)) (inj₂ (inj₂ P₂) , b₁ , b₂) = lawDiamond1Proof₂ (inj₂ P₂ , b₁ , b₂)
      lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC , b₁ , b₂) = lawDiamond1Proof₁ (idTC , b₁ , b₂)
      lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ P₁) , b₁ , b₂) = lawDiamond1Proof₁ (inj₂ P₁ , b₁ , b₂)
      lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₁ IdentTC , b₁ , b₂) = lawDiamond1Proof₁ (inj₁ IdentTC , b₁ , b₂)
      lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₂ (inj₁ P₁) , b₁ , b₂) = lawDiamond1Proof₁ (inj₂ P₁ , b₁ , b₂)
      lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₁ IdentTC , b₁ , b₂) = 
        inj₁ IdentTC , pmLawMorph2 pm₁ (inj₂ N₁) (inj₁ IdentTC) b₁ , b₂
      lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₂ (inj₁ P₁) , b₁ , ())
      lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₁ IdentTC , b₁ , b₂) = lawDiamond1Proof₁ (inj₁ IdentTC , b₁ , b₂)
      lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₂ (inj₁ P₁) , b₁ , b₂) = lawDiamond1Proof₁ (inj₂ P₁ , b₁ , b₂)
      lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ R₁)) (inj₂ (inj₁ T₁)) (inj₁ IdentTC , b₁ , b₂) = lawDiamond1Proof₁ (inj₁ IdentTC , b₁ , b₂)
      lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ R₁)) (inj₂ (inj₁ T₁)) (inj₂ (inj₁ P₁) , b₁ , b₂) = lawDiamond1Proof₁ (inj₂ P₁ , b₁ , b₂)
      lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ R₁)) (inj₂ (inj₁ T₁)) (inj₂ (inj₂ P₂) , () , ())
      lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ R₁)) (inj₂ (inj₂ T₂)) (inj₁ IdentTC , b₁ , ())
      lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ R₁)) (inj₂ (inj₂ T₂)) (inj₂ (inj₁ P₁) , b₁ , ())
      lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ R₁)) (inj₂ (inj₂ T₂)) (inj₂ (inj₂ P₂) , () , ())
      lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₁ IdentTC , b₁ , b₂) with idMorph¬∃₁ (inj₂ (N₁ , refl)) b₁
      lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₁ IdentTC , b₁ , b₂) | () -- mixed
      lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₂ (inj₂ R₂)) (inj₂ (inj₁ T₁)) (inj₁ IdentTC , b₁ , ())
      lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₂ (inj₂ R₂)) (inj₂ (inj₂ T₂)) (inj₁ IdentTC , b₁ , b₂) with idMorph¬∃₁ (inj₂ (N₁ , refl)) b₁
      lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₂ (inj₂ R₂)) (inj₂ (inj₂ T₂)) (inj₁ IdentTC , b₁ , b₂) | () -- mixed
      lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₂ (inj₁ P₁) , b₁ , ())
      lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₂ (inj₂ R₂)) (inj₂ (inj₁ T₁)) (inj₂ (inj₁ P₁) , b₁ , ())
      lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₂ (inj₂ R₂)) (inj₂ (inj₂ T₂)) (inj₂ (inj₁ P₁) , b₁ , ())
      lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₁ N₁)) R T (inj₂ (inj₂ P₂) , () , b₂)
      lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC , b₁ , b₂) = lawDiamond1Proof₂ (idTC , b₁ , idBind1→2 b₂)
      lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₁ IdentTC , b₁ , b₂) = inj₁ IdentTC , pmLawMorph2 pm₂ (inj₂ N₂) (inj₁ IdentTC) b₁ , b₂
      lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₁ IdentTC , b₁ , b₂) = lawDiamond1Proof₂ (inj₁ IdentTC , b₁ , b₂)
      lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₁ IdentTC , b₁ , b₂) with idMorph¬∃₂ (inj₂ (N₂ , refl)) b₁
      lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₁ IdentTC , b₁ , b₂) | () -- mixed
      lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₁ R₁)) (inj₂ (inj₁ T₁)) (inj₁ IdentTC , b₁ , b₂) with idMorph¬∃₂ (inj₂ (N₂ , refl)) b₁
      lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₁ R₁)) (inj₂ (inj₁ T₁)) (inj₁ IdentTC , b₁ , b₂) | () -- mixed
      lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₁ R₁)) (inj₂ (inj₂ T₂)) (inj₁ IdentTC , b₁ , ())
      lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₁ IdentTC , b₁ , b₂) = lawDiamond1Proof₂ (inj₁ IdentTC , b₁ , b₂)
      lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ R₂)) (inj₂ (inj₁ T₁)) (inj₁ IdentTC , b₁ , ())
      lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ R₂)) (inj₂ (inj₂ T₂)) (inj₁ IdentTC , b₁ , b₂) = lawDiamond1Proof₂ (inj₁ IdentTC , b₁ , b₂)
      lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₂ N₂)) R T (inj₂ (inj₁ P₁) , () , b₂)
      lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ P₂) , b₁ , b₂) = lawDiamond1Proof₂ (inj₂ P₂ , b₁ , b₂)
      lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₂ (inj₂ P₂) , b₁ , ())
      lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₂ (inj₂ P₂) , b₁ , b₂) = lawDiamond1Proof₂ (inj₂ P₂ , b₁ , b₂)
      lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₂ (inj₂ P₂) , b₁ , ())
      lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₁ R₁)) (inj₂ (inj₁ T₁)) (inj₂ (inj₂ P₂) , b₁ , ())
      lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₁ R₁)) (inj₂ (inj₂ T₂)) (inj₂ (inj₂ P₂) , b₁ , ())
      lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₂ (inj₂ P₂) , b₁ , b₂) = lawDiamond1Proof₂ (inj₂ P₂ , b₁ , b₂)
      lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ R₂)) (inj₂ (inj₁ T₁)) (inj₂ (inj₂ P₂) , b₁ , ())
      lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ R₂)) (inj₂ (inj₂ T₂)) (inj₂ (inj₂ P₂) , b₁ , b₂) = lawDiamond1Proof₂ (inj₂ P₂ , b₁ , b₂)
      lawDiamond1 (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC , b₁ , b₂) = lawDiamond1Proof₁ (idTC , b₁ , b₂)
      lawDiamond1 (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₁ IdentTC , b₁ , b₂) = lawDiamond1Proof₁ (inj₁ IdentTC , b₁ , b₂)
      lawDiamond1 (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₁ IdentTC , b₁ , b₂) with idMorph¬∃₁ (inj₁ (M₁ , refl)) b₁ 
      lawDiamond1 (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₁ IdentTC , b₁ , b₂) | () -- mixed
      lawDiamond1 (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₁ IdentTC , b₁ , b₂) = lawDiamond1Proof₁ (inj₁ IdentTC , b₁ , b₂)
      lawDiamond1 (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₂ (inj₁ T₁)) (inj₁ IdentTC , b₁ , b₂) = lawDiamond1Proof₁ (inj₁ IdentTC , b₁ , b₂)
      lawDiamond1 (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₂ (inj₂ T₂)) (inj₁ IdentTC , b₁ , ())
      lawDiamond1 (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₁ IdentTC , b₁ , b₂) = inj₁ IdentTC , b₂ , b₁
      lawDiamond1 (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₂ (inj₁ T₁)) (inj₁ IdentTC , b₁ , ())
      lawDiamond1 (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₂ (inj₂ T₂)) (inj₁ IdentTC , b₁ , b₂) with idMorph¬∃₁ (inj₁ (M₁ , refl)) b₁
      lawDiamond1 (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₂ (inj₂ T₂)) (inj₁ IdentTC , b₁ , b₂) | () -- mixed
      lawDiamond1 (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC , b₁ , b₂) = lawDiamond1Proof₁ (idTC , b₁ , b₂)
      lawDiamond1 (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₁ IdentTC , b₁ , b₂) = lawDiamond1Proof₁ (inj₁ IdentTC , b₁ , b₂)
      lawDiamond1 (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₁ IdentTC , b₁ , b₂) with idMorph¬∃₁ (inj₁ (M₁ , refl)) b₁
      lawDiamond1 (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₁ IdentTC , b₁ , b₂) | () -- mixed
      lawDiamond1 (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₁ IdentTC , b₁ , b₂) = lawDiamond1Proof₁ (inj₁ IdentTC , b₁ , b₂)
      lawDiamond1 (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ R₁)) (inj₂ (inj₁ T₁)) (inj₁ IdentTC , b₁ , b₂) = lawDiamond1Proof₁ (inj₁ IdentTC , b₁ , b₂)
      lawDiamond1 (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ R₁)) (inj₂ (inj₂ T₂)) (inj₁ IdentTC , b₁ , ())
      lawDiamond1 (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₁ IdentTC , b₁ , b₂) with idMorph¬∃₁ (inj₁ (M₁ , refl)) b₁
      lawDiamond1 (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₁ IdentTC , b₁ , b₂) | () -- mixed
      lawDiamond1 (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₂ (inj₂ R₂)) (inj₂ (inj₁ T₁)) (inj₁ IdentTC , b₁ , ())
      lawDiamond1 (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₂ (inj₂ R₂)) (inj₂ (inj₂ T₂)) (inj₁ IdentTC , b₁ , b₂) with idMorph¬∃₁ (inj₁ (M₁ , refl)) b₁ 
      lawDiamond1 (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₂ (inj₂ R₂)) (inj₂ (inj₂ T₂)) (inj₁ IdentTC , b₁ , b₂) | () -- mixed
      lawDiamond1 (inj₂ (inj₁ M₁)) (inj₂ (inj₂ N₂)) R T (inj₁ IdentTC , () , b₂)
      lawDiamond1 (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ P₁) , b₁ , b₂) = lawDiamond1Proof₁ (inj₂ P₁ , b₁ , b₂)
      lawDiamond1 (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₂ (inj₁ P₁) , b₁ , b₂) = lawDiamond1Proof₁ (inj₂ P₁ , b₁ , b₂)
      lawDiamond1 (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₂ (inj₁ P₁) , b₁ , ())
      lawDiamond1 (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₂ (inj₁ P₁) , b₁ , b₂) = lawDiamond1Proof₁ (inj₂ P₁ , b₁ , b₂)
      lawDiamond1 (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₂ (inj₁ T₁)) (inj₂ (inj₁ P₁) , b₁ , b₂) = lawDiamond1Proof₁ (inj₂ P₁ , b₁ , b₂)
      lawDiamond1 (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₂ (inj₂ T₂)) (inj₂ (inj₁ P₁) , b₁ , ())
      lawDiamond1 (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₂ (inj₁ P₁) , b₁ , ())
      lawDiamond1 (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₂ (inj₁ T₁)) (inj₂ (inj₁ P₁) , b₁ , ())
      lawDiamond1 (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₂ (inj₂ T₂)) (inj₂ (inj₁ P₁) , b₁ , ())
      lawDiamond1 (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ P₁) , b₁ , b₂) = lawDiamond1Proof₁ (inj₂ P₁ , b₁ , b₂)
      lawDiamond1 (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₂ (inj₁ P₁) , b₁ , b₂) = lawDiamond1Proof₁ (inj₂ P₁ , b₁ , b₂)
      lawDiamond1 (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₂ (inj₁ P₁) , b₁ , ())
      lawDiamond1 (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₂ (inj₁ P₁) , b₁ , b₂) = lawDiamond1Proof₁ (inj₂ P₁ , b₁ , b₂)
      lawDiamond1 (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ R₁)) (inj₂ (inj₁ T₁)) (inj₂ (inj₁ P₁) , b₁ , b₂) = lawDiamond1Proof₁ (inj₂ P₁ , b₁ , b₂)
      lawDiamond1 (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ R₁)) (inj₂ (inj₂ T₂)) (inj₂ (inj₁ P₁) , b₁ , ())
      lawDiamond1 (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₂ (inj₁ P₁) , b₁ , ())
      lawDiamond1 (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₂ (inj₂ R₂)) (inj₂ (inj₁ T₁)) (inj₂ (inj₁ P₁) , b₁ , ())
      lawDiamond1 (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₂ (inj₂ R₂)) (inj₂ (inj₂ T₂)) (inj₂ (inj₁ P₁) , b₁ , ())
      lawDiamond1 (inj₂ (inj₁ M₁)) (inj₂ (inj₂ N₂)) R T (inj₂ (inj₁ P₁) , () , b₂)
      lawDiamond1 (inj₂ (inj₁ M₁)) (inj₁ IdentTC) R T (inj₂ (inj₂ P₂) , () , b₂)
      lawDiamond1 (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) R T (inj₂ (inj₂ P₂) , () , b₂)
      lawDiamond1 (inj₂ (inj₁ M₁)) (inj₂ (inj₂ N₂)) R T (inj₂ (inj₂ P₂) , () , b₂)
      lawDiamond1 (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC , b₁ , b₂) = lawDiamond1Proof₂ (idTC , b₁ , idBind1→2 b₂)
      lawDiamond1 (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₁ IdentTC , b₁ , b₂) with idMorph¬∃₂ (inj₁ (M₂ , refl)) b₁
      lawDiamond1 (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₁ IdentTC , b₁ , b₂) | () -- mixed
      lawDiamond1 (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₁ IdentTC , b₁ , b₂) = lawDiamond1Proof₂ (inj₁ IdentTC , b₁ , b₂)
      lawDiamond1 (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₁ IdentTC , b₁ , b₂) = inj₁ IdentTC , b₂ , b₁
      lawDiamond1 (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₂ (inj₁ T₁)) (inj₁ IdentTC , b₁ , b₂) with idMorph¬∃₂ (inj₁ (M₂ , refl)) b₁
      lawDiamond1 (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₂ (inj₁ T₁)) (inj₁ IdentTC , b₁ , b₂) | () -- mixed
      lawDiamond1 (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₂ (inj₂ T₂)) (inj₁ IdentTC , b₁ , ())
      lawDiamond1 (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₁ IdentTC , b₁ , b₂) = lawDiamond1Proof₂ (inj₁ IdentTC , b₁ , b₂)
      lawDiamond1 (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₂ (inj₁ T₁)) (inj₁ IdentTC , b₁ , ())
      lawDiamond1 (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₂ (inj₂ T₂)) (inj₁ IdentTC , b₁ , b₂) = lawDiamond1Proof₂ (inj₁ IdentTC , b₁ , b₂)
      lawDiamond1 (inj₂ (inj₂ M₂)) (inj₂ (inj₁ N₁)) R T (inj₁ IdentTC , () , b₂)
      lawDiamond1 (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC , b₁ , b₂) = lawDiamond1Proof₂ (idTC , b₁ , idBind1→2 b₂)
      lawDiamond1 (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₁ IdentTC , b₁ , b₂) with idMorph¬∃₂ (inj₁ (M₂ , refl)) b₁
      lawDiamond1 (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₁ IdentTC , b₁ , b₂) | () -- mixed
      lawDiamond1 (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₁ IdentTC , b₁ , b₂) = lawDiamond1Proof₂ (inj₁ IdentTC , b₁ , b₂)
      lawDiamond1 (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₁ IdentTC , b₁ , b₂) with idMorph¬∃₂ (inj₁ (M₂ , refl)) b₁
      lawDiamond1 (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₁ IdentTC , b₁ , b₂) | () -- mixed
      lawDiamond1 (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₂ (inj₁ R₁)) (inj₂ (inj₁ T₁)) (inj₁ IdentTC , b₁ , b₂) with idMorph¬∃₂ (inj₁ (M₂ , refl)) b₁ 
      lawDiamond1 (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₂ (inj₁ R₁)) (inj₂ (inj₁ T₁)) (inj₁ IdentTC , b₁ , b₂) | () -- mixed
      lawDiamond1 (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₂ (inj₁ R₁)) (inj₂ (inj₂ T₂)) (inj₁ IdentTC , b₁ , ())
      lawDiamond1 (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₁ IdentTC , b₁ , b₂) = lawDiamond1Proof₂ (inj₁ IdentTC , b₁ , b₂)
      lawDiamond1 (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ R₂)) (inj₂ (inj₁ T₁)) (inj₁ IdentTC , b₁ , ())
      lawDiamond1 (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ R₂)) (inj₂ (inj₂ T₂)) (inj₁ IdentTC , b₁ , b₂) = lawDiamond1Proof₂ (inj₁ IdentTC , b₁ , b₂)
      lawDiamond1 (inj₂ (inj₂ M₂)) (inj₁ IdentTC) R T (inj₂ (inj₁ P₁) , () , b₂)
      lawDiamond1 (inj₂ (inj₂ M₂)) (inj₂ (inj₁ N₁)) R T (inj₂ (inj₁ P₁) , () , b₂)
      lawDiamond1 (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) R T (inj₂ (inj₁ P₁) , () , b₂)
      lawDiamond1 (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ P₂) , b₁ , b₂) = lawDiamond1Proof₂ (inj₂ P₂ , b₁ , b₂)
      lawDiamond1 (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₂ (inj₂ P₂) , b₁ , ())
      lawDiamond1 (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₂ (inj₂ P₂) , b₁ , b₂) = lawDiamond1Proof₂ (inj₂ P₂ , b₁ , b₂)
      lawDiamond1 (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₂ (inj₂ P₂) , b₁ , ())
      lawDiamond1 (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₂ (inj₁ T₁)) (inj₂ (inj₂ P₂) , b₁ , ())
      lawDiamond1 (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₂ (inj₂ T₂)) (inj₂ (inj₂ P₂) , b₁ , ())
      lawDiamond1 (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₂ (inj₂ P₂) , b₁ , b₂) = lawDiamond1Proof₂ (inj₂ P₂ , b₁ , b₂)
      lawDiamond1 (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₂ (inj₁ T₁)) (inj₂ (inj₂ P₂) , b₁ , ())
      lawDiamond1 (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₂ (inj₂ T₂)) (inj₂ (inj₂ P₂) , b₁ , b₂) = lawDiamond1Proof₂ (inj₂ P₂ , b₁ , b₂)
      lawDiamond1 (inj₂ (inj₂ M₂)) (inj₂ (inj₁ N₁)) R T (inj₂ (inj₂ P₂) , () , b₂)
      lawDiamond1 (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ P₂) , b₁ , b₂) = lawDiamond1Proof₂ (inj₂ P₂ , b₁ , b₂)
      lawDiamond1 (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₂ (inj₂ P₂) , b₁ , ())
      lawDiamond1 (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₂ (inj₂ P₂) , b₁ , b₂) = lawDiamond1Proof₂ (inj₂ P₂ , b₁ , b₂)
      lawDiamond1 (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₂ (inj₂ P₂) , b₁ , ())
      lawDiamond1 (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₂ (inj₁ R₁)) (inj₂ (inj₁ T₁)) (inj₂ (inj₂ P₂) , b₁ , ())
      lawDiamond1 (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₂ (inj₁ R₁)) (inj₂ (inj₂ T₂)) (inj₂ (inj₂ P₂) , b₁ , ())
      lawDiamond1 (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₂ (inj₂ P₂) , b₁ , b₂) = lawDiamond1Proof₂ (inj₂ P₂ , b₁ , b₂)
      lawDiamond1 (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ R₂)) (inj₂ (inj₁ T₁)) (inj₂ (inj₂ P₂) , b₁ , ())
      lawDiamond1 (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ R₂)) (inj₂ (inj₂ T₂)) (inj₂ (inj₂ P₂) , b₁ , b₂) = lawDiamond1Proof₂ (inj₂ P₂ , b₁ , b₂)

      lawDiamond2Proof₁ : ∀ {M N R T : IdTyCons ⊎ TyCons₁}
                        → (∃ λ(S : IdTyCons ⊎ TyCons₁) → B[ N , R ] pm₁ ▷ S × B[ M , S ] pm₁ ▷ T)
                        → (∃ λ(P : TyCons) → B[ TC₁→TC M , TC₁→TC N ]▷ P × B[ P , TC₁→TC R ]▷ TC₁→TC T)
      lawDiamond2Proof₁ {M} {N} {R} {T} (S , b₁ , b₂) with pmLawDiamond2 pm₁ M N R T (S , b₁ , b₂)
      lawDiamond2Proof₁ {M} {N} {R} {T} (S , b₁ , b₂) | P , b₃ , b₄ = TC₁→TC P , bindConv₁ M N P b₃ , bindConv₁ P R T b₄
      
      lawDiamond2Proof₂ : ∀ {M N R T : IdTyCons ⊎ TyCons₂}
                        → (∃ λ(S : IdTyCons ⊎ TyCons₂) → B[ N , R ] pm₂ ▷ S × B[ M , S ] pm₂ ▷ T)
                        → (∃ λ(P : TyCons) → B[ TC₂→TC M , TC₂→TC N ]▷ P × B[ P , TC₂→TC R ]▷ TC₂→TC T)
      lawDiamond2Proof₂ {M} {N} {R} {T} (S , b₁ , b₂) with pmLawDiamond2 pm₂ M N R T (S , b₁ , b₂)
      lawDiamond2Proof₂ {M} {N} {R} {T} (S , b₁ , b₂) | P , b₃ , b₄ = TC₂→TC P , bindConv₂ M N P b₃ , bindConv₂ P R T b₄

      lawDiamond2 : ∀ (M N R T : TyCons)
                  → (∃ λ(S : TyCons) → B[ N , R ]▷ S × B[ M , S ]▷ T)
                  → (∃ λ(P : TyCons) → B[ M , N ]▷ P × B[ P , R ]▷ T)
      lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC , b₁ , b₂) = idTC , b₁ , b₂
      lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ S₁) , b₁ , b₂) = lawDiamond2Proof₁ (inj₂ S₁ , b₁ , b₂)
      lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ S₂) , b₁ , b₂) = lawDiamond2Proof₂ (inj₂ S₂ , b₁ , b₂)
      lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₁ IdentTC , b₁ , b₂) = lawDiamond2Proof₁ (idTC , b₁ , b₂)
      lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₂ (inj₁ S₁) , b₁ , b₂) = lawDiamond2Proof₁ (inj₂ S₁ , b₁ , b₂)
      lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₂ (inj₂ S₂) , b₁ , ())
      lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₁ IdentTC , b₁ , b₂) = lawDiamond2Proof₂ (idTC , idBind1→2 b₁ , b₂)
      lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₂ (inj₁ S₁) , b₁ , ())
      lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₂ (inj₂ S₂) , b₁ , b₂) = lawDiamond2Proof₂ (inj₂ S₂ , b₁ , b₂)
      lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₁ IdentTC , b₁ , b₂) = lawDiamond2Proof₁ (idTC , b₁ , b₂)
      lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₂ (inj₁ T₁)) (inj₁ IdentTC , b₁ , b₂) = lawDiamond2Proof₁ (idTC , b₁ , b₂)
      lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₂ (inj₂ T₂)) (inj₁ IdentTC , b₁ , b₂) with idMorph¬∃₁ (inj₂ (R₁ , refl)) b₁
      lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₂ (inj₂ T₂)) (inj₁ IdentTC , b₁ , b₂) | () -- mixed
      lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₂ (inj₁ S₁) , b₁ , b₂) = lawDiamond2Proof₁ (inj₂ S₁ , b₁ , b₂)
      lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₂ (inj₁ T₁)) (inj₂ (inj₁ S₁) , b₁ , b₂) = lawDiamond2Proof₁ (inj₂ S₁ , b₁ , b₂)
      lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₂ (inj₂ T₂)) (inj₂ (inj₁ S₁) , b₁ , ())
      lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) T (inj₂ (inj₂ S₂) , () , b₂)
      lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₁ IdentTC , b₁ , b₂) = lawDiamond2Proof₂ (idTC , b₁ , idBind1→2 b₂)
      lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₂ (inj₁ T₁)) (inj₁ IdentTC , b₁ , b₂) with idMorph¬∃₂ (inj₂ (R₂ , refl)) b₁
      lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₂ (inj₁ T₁)) (inj₁ IdentTC , b₁ , b₂) | () -- mixed
      lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₂ (inj₂ T₂)) (inj₁ IdentTC , b₁ , b₂) = lawDiamond2Proof₂ (idTC , b₁ , b₂)
      lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) T (inj₂ (inj₁ S₁) , () , b₂)
      lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₂ (inj₂ S₂) , b₁ , b₂) = lawDiamond2Proof₂ (inj₂ S₂ , b₁ , b₂)
      lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₂ (inj₁ T₁)) (inj₂ (inj₂ S₂) , b₁ , ())
      lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₂ (inj₂ T₂)) (inj₂ (inj₂ S₂) , b₁ , b₂) = lawDiamond2Proof₂ (inj₂ S₂ , b₁ , b₂)
      lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC , b₁ , b₂) =  lawDiamond2Proof₁ (inj₁ IdentTC , b₁ , b₂)
      lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₁ IdentTC , b₁ , b₂) = lawDiamond2Proof₁ (idTC , b₁ , b₂)
      lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₁ IdentTC , b₁ , b₂) with idMorph¬∃₁ (inj₁ (N₁ , refl)) b₁
      lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₁ IdentTC , b₁ , b₂) | () -- mixed
      lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₁ IdentTC , b₁ , b₂) = lawDiamond2Proof₁ (idTC , b₁ , b₂)
      lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ R₁)) (inj₂ (inj₁ T₁)) (inj₁ IdentTC , b₁ , b₂) = lawDiamond2Proof₁ (idTC , b₁ , b₂)
      lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ R₁)) (inj₂ (inj₂ T₂)) (inj₁ IdentTC , b₁ , b₂) with idMorph¬∃₁ (inj₂ (R₁ , refl)) b₁
      lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ R₁)) (inj₂ (inj₂ T₂)) (inj₁ IdentTC , b₁ , b₂) | () -- mixed
      lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₂ (inj₂ R₂)) T (inj₁ IdentTC , () , b₂)
      lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ S₁) , b₁ , b₂) = lawDiamond2Proof₁ (inj₂ S₁ , b₁ , b₂)
      lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₂ (inj₁ S₁) , b₁ , b₂) = lawDiamond2Proof₁ (inj₂ S₁ , b₁ , b₂)
      lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₂ (inj₁ S₁) , b₁ , ())
      lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₂ (inj₁ S₁) , b₁ , b₂) = lawDiamond2Proof₁ (inj₂ S₁ , b₁ , b₂)
      lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ R₁)) (inj₂ (inj₁ T₁)) (inj₂ (inj₁ S₁) , b₁ , b₂) = lawDiamond2Proof₁ (inj₂ S₁ , b₁ , b₂)
      lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ R₁)) (inj₂ (inj₂ T₂)) (inj₂ (inj₁ S₁) , b₁ , ())
      lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₂ (inj₂ R₂)) T (inj₂ (inj₁ S₁) , () , b₂)
      lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) T (inj₂ (inj₂ S₂) , () , b₂)
      lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ R₁)) T (inj₂ (inj₂ S₂) , () , b₂)
      lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₂ (inj₂ R₂)) T (inj₂ (inj₂ S₂) , () , b₂)
      lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC , b₁ , b₂) =  lawDiamond2Proof₂ (inj₁ IdentTC , b₁ , idBind1→2 b₂)
      lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₁ IdentTC , b₁ , b₂) with idMorph¬∃₂ (inj₁ (N₂ , refl)) b₁
      lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₁ IdentTC , b₁ , b₂) | () -- mixed
      lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₁ IdentTC , b₁ , b₂) = lawDiamond2Proof₂ (idTC , b₁ , b₂)
      lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₁ R₁)) T (inj₁ IdentTC , () , b₂)
      lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₁ IdentTC , b₁ , b₂) = lawDiamond2Proof₂ (idTC , b₁ , idBind1→2 b₂)
      lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ R₂)) (inj₂ (inj₁ T₁)) (inj₁ IdentTC , b₁ , b₂) with idMorph¬∃₂ (inj₂ (R₂ , refl)) b₁
      lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ R₂)) (inj₂ (inj₁ T₁)) (inj₁ IdentTC , b₁ , b₂) | () -- mixed
      lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ R₂)) (inj₂ (inj₂ T₂)) (inj₁ IdentTC , b₁ , b₂) = lawDiamond2Proof₂ (idTC , b₁ , b₂)
      lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) T (inj₂ (inj₁ S₁) , () , b₂)
      lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₁ R₁)) T (inj₂ (inj₁ S₁) , () , b₂)
      lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ R₂)) T (inj₂ (inj₁ S₁) , () , b₂)
      lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ S₂) , b₁ , b₂) = lawDiamond2Proof₂ (inj₂ S₂ , b₁ , b₂)
      lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₂ (inj₂ S₂) , b₁ , ())
      lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₂ (inj₂ S₂) , b₁ , b₂) = lawDiamond2Proof₂ (inj₂ S₂ , b₁ , b₂)
      lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₁ R₁)) T (inj₂ (inj₂ S₂) , () , b₂)
      lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₂ (inj₂ S₂) , b₁ , b₂) = lawDiamond2Proof₂ (inj₂ S₂ , b₁ , b₂)
      lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ R₂)) (inj₂ (inj₁ T₁)) (inj₂ (inj₂ S₂) , b₁ , ())
      lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ R₂)) (inj₂ (inj₂ T₂)) (inj₂ (inj₂ S₂) , b₁ , b₂) = lawDiamond2Proof₂ (inj₂ S₂ , b₁ , b₂)
      lawDiamond2 (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC , b₁ , b₂) = lawDiamond2Proof₁ (inj₁ IdentTC , b₁ , b₂)
      lawDiamond2 (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₁ IdentTC , b₁ , b₂) = lawDiamond2Proof₁ (idTC , b₁ , b₂)
      lawDiamond2 (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₁ IdentTC , b₁ , b₂) with idMorph¬∃₂ (inj₂ (R₂ , refl)) b₁
      lawDiamond2 (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₁ IdentTC , b₁ , b₂) | () -- mixed
      lawDiamond2 (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC , b₁ , b₂) = lawDiamond2Proof₁ (idTC , b₁ , b₂)
      lawDiamond2 (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₁ IdentTC , b₁ , b₂) = lawDiamond2Proof₁ (idTC , b₁ , b₂)
      lawDiamond2 (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₁ IdentTC , () , b₂)
      lawDiamond2 (inj₂ (inj₁ M₁)) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC , b₁ , b₂) with idMorph¬∃₂ (inj₁ (N₂ , refl)) b₁ 
      lawDiamond2 (inj₂ (inj₁ M₁)) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC , b₁ , b₂) | () -- mixed
      lawDiamond2 (inj₂ (inj₁ M₁)) (inj₂ (inj₂ N₂)) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₁ IdentTC , () , b₂)
      lawDiamond2 (inj₂ (inj₁ M₁)) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₁ IdentTC , b₁ , b₂) with idMorph¬∃₂ (inj₂ (R₂ , refl)) b₁ 
      lawDiamond2 (inj₂ (inj₁ M₁)) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₁ IdentTC , b₁ , b₂) | () -- mixed
      lawDiamond2 (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ S₁) , b₁ , b₂) = lawDiamond2Proof₁ (inj₂ S₁ , b₁ , b₂)
      lawDiamond2 (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₂ (inj₁ S₁) , b₁ , b₂) = lawDiamond2Proof₁ (inj₂ S₁ , b₁ , b₂)
      lawDiamond2 (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₂ (inj₁ S₁) , () , b₂)
      lawDiamond2 (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ S₁) , b₁ , b₂) = lawDiamond2Proof₁ (inj₂ S₁ , b₁ , b₂)
      lawDiamond2 (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₂ (inj₁ S₁) , b₁ , b₂) = lawDiamond2Proof₁ (inj₂ S₁ , b₁ , b₂)
      lawDiamond2 (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₂ (inj₁ S₁) , () , b₂)
      lawDiamond2 (inj₂ (inj₁ M₁)) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ S₁) , () , b₂)
      lawDiamond2 (inj₂ (inj₁ M₁)) (inj₂ (inj₂ N₂)) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₂ (inj₁ S₁) , () , b₂)
      lawDiamond2 (inj₂ (inj₁ M₁)) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₂ (inj₁ S₁) , () , b₂)
      lawDiamond2 (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ S₂) , b₁ , ())
      lawDiamond2 (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₂ (inj₂ S₂) , () , ())
      lawDiamond2 (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₂ (inj₂ S₂) , b₁ , ())
      lawDiamond2 (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ S₂) , () , ())
      lawDiamond2 (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₂ (inj₂ S₂) , () , ())
      lawDiamond2 (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₂ (inj₂ S₂) , () , ())
      lawDiamond2 (inj₂ (inj₁ M₁)) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ S₂) , b₁ , ())
      lawDiamond2 (inj₂ (inj₁ M₁)) (inj₂ (inj₂ N₂)) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₂ (inj₂ S₂) , () , ())
      lawDiamond2 (inj₂ (inj₁ M₁)) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₂ (inj₂ S₂) , b₁ , ())
      lawDiamond2 (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₁ IdentTC , b₁ , b₂) = lawDiamond2Proof₁ (inj₁ IdentTC , b₁ , b₂)
      lawDiamond2 (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₂ (inj₁ T₁)) (inj₁ IdentTC , b₁ , b₂) = lawDiamond2Proof₁ (idTC , b₁ , b₂)
      lawDiamond2 (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₂ (inj₁ T₁)) (inj₁ IdentTC , b₁ , b₂) with idMorph¬∃₂ (inj₂ (R₂ , refl)) b₁
      lawDiamond2 (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₂ (inj₁ T₁)) (inj₁ IdentTC , b₁ , b₂) | () -- mixed
      lawDiamond2 (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₁ IdentTC , b₁ , b₂) = lawDiamond2Proof₁ (idTC , b₁ , b₂)
      lawDiamond2 (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ R₁)) (inj₂ (inj₁ T₁)) (inj₁ IdentTC , b₁ , b₂) = lawDiamond2Proof₁ (idTC , b₁ , b₂)
      lawDiamond2 (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₂ (inj₂ R₂)) (inj₂ (inj₁ T₁)) (inj₁ IdentTC , () , b₂)
      lawDiamond2 (inj₂ (inj₁ M₁)) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₁ IdentTC , b₁ , b₂) with idMorph¬∃₂ (inj₁ (N₂ , refl)) b₁
      lawDiamond2 (inj₂ (inj₁ M₁)) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₁ IdentTC , b₁ , b₂) | () -- mixed
      lawDiamond2 (inj₂ (inj₁ M₁)) (inj₂ (inj₂ N₂)) (inj₂ (inj₁ R₁)) (inj₂ (inj₁ T₁)) (inj₁ IdentTC , () , b₂)
      lawDiamond2 (inj₂ (inj₁ M₁)) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ R₂)) (inj₂ (inj₁ T₁)) (inj₁ IdentTC , b₁ , b₂) with idMorph¬∃₂ (inj₂ (R₂ , refl)) b₁
      lawDiamond2 (inj₂ (inj₁ M₁)) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ R₂)) (inj₂ (inj₁ T₁)) (inj₁ IdentTC , b₁ , b₂) | () -- mixed
      lawDiamond2 (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₂ (inj₁ S₁) , b₁ , b₂) = lawDiamond2Proof₁ (inj₂ S₁ , b₁ , b₂)
      lawDiamond2 (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₂ (inj₁ T₁)) (inj₂ (inj₁ S₁) , b₁ , b₂) = lawDiamond2Proof₁ (inj₂ S₁ , b₁ , b₂)
      lawDiamond2 (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₂ (inj₁ T₁)) (inj₂ (inj₁ S₁) , () , b₂)
      lawDiamond2 (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₂ (inj₁ S₁) , b₁ , b₂) = lawDiamond2Proof₁ (inj₂ S₁ , b₁ , b₂)
      lawDiamond2 (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ R₁)) (inj₂ (inj₁ T₁)) (inj₂ (inj₁ S₁) , b₁ , b₂) = lawDiamond2Proof₁ (inj₂ S₁ , b₁ , b₂)
      lawDiamond2 (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₂ (inj₂ R₂)) (inj₂ (inj₁ T₁)) (inj₂ (inj₁ S₁) , () , b₂)
      lawDiamond2 (inj₂ (inj₁ M₁)) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₂ (inj₁ S₁) , () , b₂)
      lawDiamond2 (inj₂ (inj₁ M₁)) (inj₂ (inj₂ N₂)) (inj₂ (inj₁ R₁)) (inj₂ (inj₁ T₁)) (inj₂ (inj₁ S₁) , () , b₂)
      lawDiamond2 (inj₂ (inj₁ M₁)) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ R₂)) (inj₂ (inj₁ T₁)) (inj₂ (inj₁ S₁) , () , b₂)
      lawDiamond2 (inj₂ (inj₁ M₁)) N R (inj₂ (inj₁ T₁)) (inj₂ (inj₂ S₂) , b₁ , ())
      lawDiamond2 (inj₂ (inj₁ M₁)) N R (inj₂ (inj₂ T₂)) (inj₁ IdentTC , b₁ , ())
      lawDiamond2 (inj₂ (inj₁ M₁)) N R (inj₂ (inj₂ T₂)) (inj₂ (inj₁ S₁) , b₁ , ())
      lawDiamond2 (inj₂ (inj₁ M₁)) N R (inj₂ (inj₂ T₂)) (inj₂ (inj₂ S₂) , b₁ , ())
      lawDiamond2 (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC , b₁ , b₂) = lawDiamond2Proof₂ (inj₁ IdentTC , idBind1→2 b₁ , b₂)
      lawDiamond2 (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₁ IdentTC , b₁ , b₂) with idMorph¬∃₁ (inj₂ (R₁ , refl)) b₁
      lawDiamond2 (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₁ IdentTC , b₁ , b₂) | () -- mixed
      lawDiamond2 (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₁ IdentTC , b₁ , b₂) = lawDiamond2Proof₂ (idTC , b₁ , b₂)
      lawDiamond2 (inj₂ (inj₂ M₂)) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC , b₁ , b₂) with idMorph¬∃₁ (inj₁ (N₁ , refl)) b₁
      lawDiamond2 (inj₂ (inj₂ M₂)) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC , b₁ , b₂) | () -- mixed
      lawDiamond2 (inj₂ (inj₂ M₂)) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₁ IdentTC , b₁ , b₂) with idMorph¬∃₂ (inj₁ (M₂ , refl)) b₂
      lawDiamond2 (inj₂ (inj₂ M₂)) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₁ IdentTC , b₁ , b₂) | () -- mixed
      lawDiamond2 (inj₂ (inj₂ M₂)) (inj₂ (inj₁ N₁)) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₁ IdentTC , () , b₂)
      lawDiamond2 (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC , b₁ , b₂) = lawDiamond2Proof₂ (idTC , b₁ , b₂)
      lawDiamond2 (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₁ IdentTC , () , b₂)
      lawDiamond2 (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₁ IdentTC , b₁ , b₂) = lawDiamond2Proof₂ (idTC , b₁ , b₂)
      lawDiamond2 (inj₂ (inj₂ M₂)) N R (inj₁ IdentTC) (inj₂ (inj₁ S₁) , b₁ , ())
      lawDiamond2 (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ S₂) , b₁ , b₂) = lawDiamond2Proof₂ (inj₂ S₂ , b₁ , b₂)
      lawDiamond2 (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₂ (inj₂ S₂) , () , b₂)
      lawDiamond2 (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₂ (inj₂ S₂) , b₁ , b₂) = lawDiamond2Proof₂ (inj₂ S₂ , b₁ , b₂)
      lawDiamond2 (inj₂ (inj₂ M₂)) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ S₂) , () , b₂)
      lawDiamond2 (inj₂ (inj₂ M₂)) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₂ (inj₂ S₂) , () , b₂)
      lawDiamond2 (inj₂ (inj₂ M₂)) (inj₂ (inj₁ N₁)) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₂ (inj₂ S₂) , () , b₂)
      lawDiamond2 (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ S₂) , b₁ , b₂) = lawDiamond2Proof₂ (inj₂ S₂ , b₁ , b₂)
      lawDiamond2 (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₂ (inj₂ S₂) , () , b₂)
      lawDiamond2 (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₂ (inj₂ S₂) , b₁ , b₂) = lawDiamond2Proof₂ (inj₂ S₂ , b₁ , b₂)
      lawDiamond2 (inj₂ (inj₂ M₂)) N R (inj₂ (inj₁ T₁)) (inj₁ IdentTC , b₁ , ())
      lawDiamond2 (inj₂ (inj₂ M₂)) N R (inj₂ (inj₁ T₁)) (inj₂ (inj₁ S₁) , b₁ , ())
      lawDiamond2 (inj₂ (inj₂ M₂)) N R (inj₂ (inj₁ T₁)) (inj₂ (inj₂ S₂) , b₁ , ())
      lawDiamond2 (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₁ IdentTC , b₁ , b₂) = lawDiamond2Proof₂ (inj₁ IdentTC , idBind1→2 b₁ , b₂)
      lawDiamond2 (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₂ (inj₂ T₂)) (inj₁ IdentTC , b₁ , b₂) with idMorph¬∃₁ (inj₂ (R₁ , refl)) b₁
      lawDiamond2 (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₂ (inj₂ T₂)) (inj₁ IdentTC , b₁ , b₂) | () -- mixed
      lawDiamond2 (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₂ (inj₂ T₂)) (inj₁ IdentTC , b₁ , b₂) = lawDiamond2Proof₂ (idTC , b₁ , b₂)
      lawDiamond2 (inj₂ (inj₂ M₂)) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₁ IdentTC , b₁ , b₂) with idMorph¬∃₁ (inj₁ (N₁ , refl)) b₁
      lawDiamond2 (inj₂ (inj₂ M₂)) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₁ IdentTC , b₁ , b₂) | () -- mixed
      lawDiamond2 (inj₂ (inj₂ M₂)) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ R₁)) (inj₂ (inj₂ T₂)) (inj₁ IdentTC , b₁ , b₂) with idMorph¬∃₁ (inj₂ (R₁ , refl)) b₁
      lawDiamond2 (inj₂ (inj₂ M₂)) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ R₁)) (inj₂ (inj₂ T₂)) (inj₁ IdentTC , b₁ , b₂) | () -- mixed
      lawDiamond2 (inj₂ (inj₂ M₂)) (inj₂ (inj₁ N₁)) (inj₂ (inj₂ R₂)) (inj₂ (inj₂ T₂)) (inj₁ IdentTC , () , b₂)
      lawDiamond2 (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₁ IdentTC , b₁ , b₂) = lawDiamond2Proof₂ (idTC , b₁ , b₂)
      lawDiamond2 (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₂ (inj₁ R₁)) (inj₂ (inj₂ T₂)) (inj₁ IdentTC , () , b₂)
      lawDiamond2 (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ R₂)) (inj₂ (inj₂ T₂)) (inj₁ IdentTC , b₁ , b₂) = lawDiamond2Proof₂ (idTC , b₁ , b₂)
      lawDiamond2 (inj₂ (inj₂ M₂)) N R (inj₂ (inj₂ T₂)) (inj₂ (inj₁ S₁) , b₁ , ())
      lawDiamond2 (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₂ (inj₂ S₂) , b₁ , b₂) = lawDiamond2Proof₂ (inj₂ S₂ , b₁ , b₂)
      lawDiamond2 (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₂ (inj₂ T₂)) (inj₂ (inj₂ S₂) , () , b₂)
      lawDiamond2 (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₂ (inj₂ T₂)) (inj₂ (inj₂ S₂) , b₁ , b₂) = lawDiamond2Proof₂ (inj₂ S₂ , b₁ , b₂)
      lawDiamond2 (inj₂ (inj₂ M₂)) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₂ (inj₂ S₂) , () , b₂)
      lawDiamond2 (inj₂ (inj₂ M₂)) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ R₁)) (inj₂ (inj₂ T₂)) (inj₂ (inj₂ S₂) , () , b₂)
      lawDiamond2 (inj₂ (inj₂ M₂)) (inj₂ (inj₁ N₁)) (inj₂ (inj₂ R₂)) (inj₂ (inj₂ T₂)) (inj₂ (inj₂ S₂) , () , b₂)
      lawDiamond2 (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₂ (inj₂ S₂) , b₁ , b₂) = lawDiamond2Proof₂ (inj₂ S₂ , b₁ , b₂)
      lawDiamond2 (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₂ (inj₁ R₁)) (inj₂ (inj₂ T₂)) (inj₂ (inj₂ S₂) , () , b₂)
      lawDiamond2 (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ R₂)) (inj₂ (inj₂ T₂)) (inj₂ (inj₂ S₂) , b₁ , b₂) = lawDiamond2Proof₂ (inj₂ S₂ , b₁ , b₂)
      
      lawClosureProof₁ : ∀ {M N P S T U : IdTyCons ⊎ TyCons₁}
               → ( B[ M , N ] pm₁ ▷ P × B[ S , idTC ] pm₁ ▷ M × B[ T , idTC ] pm₁ ▷ N × B[ P , idTC ] pm₁ ▷ U )
               → B[ TC₁→TC S , TC₁→TC T ]▷ TC₁→TC U
      lawClosureProof₁ {M} {N} {P} {S} {T} {U} bs = bindConv₁ S T U (pmLawClosure pm₁ M N P S T U bs) 

      lawClosureProof₂ : ∀ {M N P S T U : IdTyCons ⊎ TyCons₂}
               → ( B[ M , N ] pm₂ ▷ P × B[ S , idTC ] pm₂ ▷ M × B[ T , idTC ] pm₂ ▷ N × B[ P , idTC ] pm₂ ▷ U )
               → B[ TC₂→TC S , TC₂→TC T ]▷ TC₂→TC U
      lawClosureProof₂ {M} {N} {P} {S} {T} {U} bs = bindConv₂ S T U (pmLawClosure pm₂ M N P S T U bs) 
      
      lawClosure : ∀ (M N P S T U : TyCons)
               → ( B[ M , N ]▷ P × B[ S , Id ]▷ M × B[ T , Id ]▷ N × B[ P , Id ]▷ U )
               → B[ S , T ]▷ U
      lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (b₁ , b₂ , b₃ , b₄) = b₁
      lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ U₁)) (b₁ , b₂ , b₃ , b₄) = b₄
      lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ U₂)) (b₁ , b₂ , b₃ , b₄) = b₄
      lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) U (b₁ , b₂ , b₃ , b₄) with idMorph¬∃₁ (inj₁ (T₁ , refl)) b₃
      lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) U (b₁ , b₂ , b₃ , b₄) | ()
      lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) U (b₁ , b₂ , b₃ , b₄) with idMorph¬∃₂ (inj₁ (T₂ , refl)) b₃
      lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) U (b₁ , b₂ , b₃ , b₄) | ()
      lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ S₁)) T U (b₁ , b₂ , b₃ , b₄) with idMorph¬∃₁ (inj₁ (S₁ , refl)) b₂
      lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ S₁)) T U (b₁ , b₂ , b₃ , b₄) | ()
      lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ S₂)) T U (b₁ , b₂ , b₃ , b₄) with idMorph¬∃₂ (inj₁ (S₂ , refl)) b₂
      lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ S₂)) T U (b₁ , b₂ , b₃ , b₄) | ()
      lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) S T (inj₁ IdentTC) (b₁ , b₂ , b₃ , b₄) with idMorph¬∃₁ (inj₁ (P₁ , refl)) b₄
      lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) S T (inj₁ IdentTC) (b₁ , b₂ , b₃ , b₄) | ()
      lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ U₁)) (b₁ , b₂ , b₃ , b₄) = lawClosureProof₁ (b₁ , b₂ , b₃ , b₄)
      lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₂ (inj₁ U₁)) (b₁ , b₂ , b₃ , b₄) with idMorph¬∃₁ (inj₁ (T₁ , refl)) b₃
      lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₂ (inj₁ U₁)) (b₁ , b₂ , b₃ , b₄) | ()
      lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₂ (inj₁ U₁)) (b₁ , b₂ , b₃ , b₄) with idMorph¬∃₂ (inj₁ (T₂ , refl)) b₃
      lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₂ (inj₁ U₁)) (b₁ , b₂ , b₃ , b₄) | ()
      lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) (inj₂ (inj₁ S₁)) T (inj₂ (inj₁ U₁)) (b₁ , b₂ , b₃ , b₄) with idMorph¬∃₁ (inj₁ (S₁ , refl)) b₂
      lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) (inj₂ (inj₁ S₁)) T (inj₂ (inj₁ U₁)) (b₁ , b₂ , b₃ , b₄) | ()
      lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) (inj₂ (inj₂ S₂)) T (inj₂ (inj₁ U₁)) (b₁ , b₂ , b₃ , b₄) with idMorph¬∃₂ (inj₁ (S₂ , refl)) b₂
      lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) (inj₂ (inj₂ S₂)) T (inj₂ (inj₁ U₁)) (b₁ , b₂ , b₃ , b₄) | ()
      lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) S T (inj₂ (inj₂ U₂)) (b₁ , b₂ , b₃ , ())
      lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) S T (inj₁ IdentTC) (b₁ , b₂ , b₃ , b₄) with idMorph¬∃₂ (inj₁ (P₂ , refl)) b₄ 
      lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) S T (inj₁ IdentTC) (b₁ , b₂ , b₃ , b₄) | ()
      lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) S T (inj₂ (inj₁ U₁)) (b₁ , b₂ , b₃ , ())
      lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ U₂)) (b₁ , b₂ , b₃ , b₄) = lawClosureProof₂ (b₁ , idBind1→2 b₂ , idBind1→2 b₃ , b₄)
      lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₂ (inj₂ U₂)) (b₁ , b₂ , b₃ , b₄) with idMorph¬∃₁ (inj₁ (T₁ , refl)) b₃
      lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₂ (inj₂ U₂)) (b₁ , b₂ , b₃ , b₄) | ()
      lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₂ (inj₂ U₂)) (b₁ , b₂ , b₃ , b₄) with idMorph¬∃₂ (inj₁ (T₂ , refl)) b₃
      lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₂ (inj₂ U₂)) (b₁ , b₂ , b₃ , b₄) | ()
      lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) (inj₂ (inj₁ S₁)) T (inj₂ (inj₂ U₂)) (b₁ , b₂ , b₃ , b₄) with idMorph¬∃₁ (inj₁ (S₁ , refl)) b₂
      lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) (inj₂ (inj₁ S₁)) T (inj₂ (inj₂ U₂)) (b₁ , b₂ , b₃ , b₄) | ()
      lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) (inj₂ (inj₂ S₂)) T (inj₂ (inj₂ U₂)) (b₁ , b₂ , b₃ , b₄) with idMorph¬∃₂ (inj₁ (S₂ , refl)) b₂
      lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) (inj₂ (inj₂ S₂)) T (inj₂ (inj₂ U₂)) (b₁ , b₂ , b₃ , b₄) | ()
      lawClosure (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) S T U (b₁ , b₂ , b₃ , b₄) with idMorph¬∃₁ (inj₂ (N₁ , refl)) b₁
      lawClosure (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) S T U (b₁ , b₂ , b₃ , b₄) | ()
      lawClosure (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ P₁)) S T (inj₁ IdentTC) (b₁ , b₂ , b₃ , b₄) with idMorph¬∃₁ (inj₁ (P₁ , refl)) b₄
      lawClosure (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ P₁)) S T (inj₁ IdentTC) (b₁ , b₂ , b₃ , b₄) | ()
      lawClosure (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ P₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ U₁)) (b₁ , b₂ , b₃ , b₄) = lawClosureProof₁ (b₁ , b₂ , b₃ , b₄)
      lawClosure (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ P₁)) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₂ (inj₁ U₁)) (b₁ , b₂ , b₃ , b₄) = lawClosureProof₁ (b₁ , b₂ , b₃ , b₄)
      lawClosure (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ P₁)) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₂ (inj₁ U₁)) (b₁ , b₂ , () , b₄)
      lawClosure (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ P₁)) (inj₂ (inj₁ S₁)) T (inj₂ (inj₁ U₁)) (b₁ , b₂ , b₃ , b₄) with idMorph¬∃₁ (inj₁ (S₁ , refl)) b₂
      lawClosure (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ P₁)) (inj₂ (inj₁ S₁)) T (inj₂ (inj₁ U₁)) (b₁ , b₂ , b₃ , b₄) | ()
      lawClosure (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ P₁)) (inj₂ (inj₂ S₂)) T (inj₂ (inj₁ U₁)) (b₁ , b₂ , b₃ , b₄) with idMorph¬∃₂ (inj₁ (S₂ , refl)) b₂
      lawClosure (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ P₁)) (inj₂ (inj₂ S₂)) T (inj₂ (inj₁ U₁)) (b₁ , b₂ , b₃ , b₄) | ()
      lawClosure (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ P₁)) S T (inj₂ (inj₂ U₂)) (b₁ , b₂ , b₃ , ())
      lawClosure (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₂ (inj₂ P₂)) S T U (() , b₂ , b₃ , b₄)
      lawClosure (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) S T U (b₁ , b₂ , b₃ , b₄) with idMorph¬∃₂ (inj₂ (N₂ , refl)) b₁
      lawClosure (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) S T U (b₁ , b₂ , b₃ , b₄) | ()
      lawClosure (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₁ P₁)) S T U (() , b₂ , b₃ , b₄)
      lawClosure (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) S T (inj₁ IdentTC) (b₁ , b₂ , b₃ , b₄) with idMorph¬∃₂ (inj₁ (P₂ , refl)) b₄
      lawClosure (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) S T (inj₁ IdentTC) (b₁ , b₂ , b₃ , b₄) | ()
      lawClosure (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) S T (inj₂ (inj₁ U₁)) (b₁ , b₂ , b₃ , ())
      lawClosure (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ U₂)) (b₁ , b₂ , b₃ , b₄) = lawClosureProof₂ (b₁ , idBind1→2 b₂ , b₃ , b₄)
      lawClosure (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₂ (inj₁ S₁)) (inj₁ IdentTC) (inj₂ (inj₂ U₂)) (b₁ , b₂ , b₃ , b₄) = idMorph¬∃₁ (inj₁ (S₁ , refl)) b₂
      lawClosure (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₂ (inj₂ S₂)) (inj₁ IdentTC) (inj₂ (inj₂ U₂)) (b₁ , b₂ , b₃ , b₄) = lawClosureProof₂ (b₁ , b₂ , b₃ , b₄)
      lawClosure (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) S (inj₂ (inj₁ T₁)) (inj₂ (inj₂ U₂)) (b₁ , b₂ , () , b₄)
      lawClosure (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₂ (inj₂ U₂)) (b₁ , b₂ , b₃ , b₄) = lawClosureProof₂ (b₁ , idBind1→2 b₂ , b₃ , b₄)
      lawClosure (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₂ (inj₁ S₁)) (inj₂ (inj₂ T₂)) (inj₂ (inj₂ U₂)) (b₁ , b₂ , b₃ , b₄) = idMorph¬∃₁ (inj₁ (S₁ , refl)) b₂
      lawClosure (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₂ (inj₂ S₂)) (inj₂ (inj₂ T₂)) (inj₂ (inj₂ U₂)) (b₁ , b₂ , b₃ , b₄) = lawClosureProof₂ (b₁ , b₂ , b₃ , b₄)
      lawClosure (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₁ IdentTC) S T U (b₁ , b₂ , b₃ , b₄) with idMorph¬∃₁ (inj₁ (M₁ , refl)) b₁
      lawClosure (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₁ IdentTC) S T U (b₁ , b₂ , b₃ , b₄) | ()
      lawClosure (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) S T (inj₁ IdentTC) (b₁ , b₂ , b₃ , b₄) with idMorph¬∃₁ (inj₁ (P₁ , refl)) b₄
      lawClosure (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) S T (inj₁ IdentTC) (b₁ , b₂ , b₃ , b₄) | ()
      lawClosure (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ U₁)) (b₁ , b₂ , b₃ , b₄) = lawClosureProof₁ (b₁ , b₂ , b₃ , b₄)
      lawClosure (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) (inj₂ (inj₁ S₁)) (inj₁ IdentTC) (inj₂ (inj₁ U₁)) (b₁ , b₂ , b₃ , b₄) = lawClosureProof₁ (b₁ , b₂ , b₃ , b₄)
      lawClosure (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) (inj₂ (inj₂ S₂)) (inj₁ IdentTC) (inj₂ (inj₁ U₁)) (b₁ , () , b₃ , b₄)
      lawClosure (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) S (inj₂ (inj₁ T₁)) (inj₂ (inj₁ U₁)) (b₁ , b₂ , b₃ , b₄) with idMorph¬∃₁ (inj₁ (T₁ , refl)) b₃
      lawClosure (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) S (inj₂ (inj₁ T₁)) (inj₂ (inj₁ U₁)) (b₁ , b₂ , b₃ , b₄) | ()
      lawClosure (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) S (inj₂ (inj₂ T₂)) (inj₂ (inj₁ U₁)) (b₁ , b₂ , b₃ , b₄) with idMorph¬∃₂ (inj₁ (T₂ , refl)) b₃
      lawClosure (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) S (inj₂ (inj₂ T₂)) (inj₂ (inj₁ U₁)) (b₁ , b₂ , b₃ , b₄) | ()
      lawClosure (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) S T (inj₂ (inj₂ U₂)) (b₁ , b₂ , b₃ , ())
      lawClosure (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) S T U (() , b₂ , b₃ , b₄)
      lawClosure (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) S T U (b₁ , b₂ , b₃ , b₄) with idMorph¬∃₁ (inj₁ (M₁ , refl)) b₁
      lawClosure (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) S T U (b₁ , b₂ , b₃ , b₄) | ()
      lawClosure (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ P₁)) S T (inj₁ IdentTC) (b₁ , b₂ , b₃ , b₄) with idMorph¬∃₁ (inj₁ (P₁ , refl)) b₄
      lawClosure (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ P₁)) S T (inj₁ IdentTC) (b₁ , b₂ , b₃ , b₄) | ()
      lawClosure (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ P₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ U₁)) (b₁ , b₂ , b₃ , b₄) = lawClosureProof₁ (b₁ , b₂ , b₃ , b₄)
      lawClosure (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ P₁)) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₂ (inj₁ U₁)) (b₁ , b₂ , b₃ , b₄) = lawClosureProof₁ (b₁ , b₂ , b₃ , b₄)
      lawClosure (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ P₁)) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₂ (inj₁ U₁)) (b₁ , b₂ , () , b₄)
      lawClosure (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ P₁)) (inj₂ (inj₁ S₁)) (inj₁ IdentTC) (inj₂ (inj₁ U₁)) (b₁ , b₂ , b₃ , b₄) = lawClosureProof₁ (b₁ , b₂ , b₃ , b₄)
      lawClosure (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ P₁)) (inj₂ (inj₁ S₁)) (inj₂ (inj₁ T₁)) (inj₂ (inj₁ U₁)) (b₁ , b₂ , b₃ , b₄) = lawClosureProof₁ (b₁ , b₂ , b₃ , b₄)
      lawClosure (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ P₁)) (inj₂ (inj₁ S₁)) (inj₂ (inj₂ T₂)) (inj₂ (inj₁ U₁)) (b₁ , b₂ , () , b₄)
      lawClosure (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ P₁)) (inj₂ (inj₂ S₂)) T (inj₂ (inj₁ U₁)) (b₁ , () , b₃ , b₄)
      lawClosure (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ P₁)) S T (inj₂ (inj₂ U₂)) (b₁ , b₂ , b₃ , ())
      lawClosure (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₂ (inj₂ P₂)) S T U (() , b₂ , b₃ , b₄)
      lawClosure (inj₂ (inj₁ M₁)) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) S T U (() , b₂ , b₃ , b₄)
      lawClosure (inj₂ (inj₁ M₁)) (inj₂ (inj₂ N₂)) (inj₂ (inj₁ P₁)) S T U (() , b₂ , b₃ , b₄)
      lawClosure (inj₂ (inj₁ M₁)) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) S T U (() , b₂ , b₃ , b₄)
      lawClosure (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₁ IdentTC) S T U (b₁ , b₂ , b₃ , b₄) with idMorph¬∃₂ (inj₁ (M₂ , refl)) b₁
      lawClosure (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₁ IdentTC) S T U (b₁ , b₂ , b₃ , b₄) | ()
      lawClosure (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) S T U (() , b₂ , b₃ , b₄)
      lawClosure (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) S T (inj₁ IdentTC) (b₁ , b₂ , b₃ , b₄) with idMorph¬∃₂ (inj₁ (P₂ , refl)) b₄
      lawClosure (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) S T (inj₁ IdentTC) (b₁ , b₂ , b₃ , b₄) | ()
      lawClosure (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) S T (inj₂ (inj₁ U₁)) (b₁ , b₂ , b₃ , ())
      lawClosure (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ U₂)) (b₁ , b₂ , b₃ , b₄) = lawClosureProof₂ (b₁ , b₂ , idBind1→2 b₃ , b₄)
      lawClosure (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) (inj₂ (inj₁ S₁)) (inj₁ IdentTC) (inj₂ (inj₂ U₂)) (b₁ , () , b₃ , b₄)
      lawClosure (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) (inj₂ (inj₂ S₂)) (inj₁ IdentTC) (inj₂ (inj₂ U₂)) (b₁ , b₂ , b₃ , b₄) = lawClosureProof₂ (b₁ , b₂ , idBind1→2 b₃ , b₄)
      lawClosure (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) S (inj₂ (inj₁ T₁)) (inj₂ (inj₂ U₂)) (b₁ , b₂ , b₃ , b₄) with idMorph¬∃₁ (inj₁ (T₁ , refl)) b₃
      lawClosure (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) S (inj₂ (inj₁ T₁)) (inj₂ (inj₂ U₂)) (b₁ , b₂ , b₃ , b₄) | ()
      lawClosure (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) S (inj₂ (inj₂ T₂)) (inj₂ (inj₂ U₂)) (b₁ , b₂ , b₃ , b₄) with idMorph¬∃₂ (inj₁ (T₂ , refl)) b₃
      lawClosure (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) S (inj₂ (inj₂ T₂)) (inj₂ (inj₂ U₂)) (b₁ , b₂ , b₃ , b₄) | ()
      lawClosure (inj₂ (inj₂ M₂)) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) S T U (() , b₂ , b₃ , b₄)
      lawClosure (inj₂ (inj₂ M₂)) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ P₁)) S T U (() , b₂ , b₃ , b₄)
      lawClosure (inj₂ (inj₂ M₂)) (inj₂ (inj₁ N₁)) (inj₂ (inj₂ P₂)) S T U (() , b₂ , b₃ , b₄)
      lawClosure (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) S T U (b₁ , b₂ , b₃ , b₄) with idMorph¬∃₂ (inj₁ (M₂ , refl)) b₁
      lawClosure (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) S T U (b₁ , b₂ , b₃ , b₄) | ()
      lawClosure (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₂ (inj₁ P₁)) S T U (() , b₂ , b₃ , b₄)
      lawClosure (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (b₁ , b₂ , b₃ , b₄) = lawClosureProof₂ (b₁ , b₂ , b₃ , b₄)
      lawClosure (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ U₁)) (b₁ , b₂ , b₃ , ())
      lawClosure (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ U₂)) (b₁ , b₂ , b₃ , b₄) = lawClosureProof₂ (b₁ , b₂ , b₃ , b₄)
      lawClosure (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) U (b₁ , b₂ , () , b₄)
      lawClosure (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₁ IdentTC) (b₁ , b₂ , b₃ , b₄) = lawClosureProof₂ (b₁ , b₂ , b₃ , b₄)
      lawClosure (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₂ (inj₁ U₁)) (b₁ , b₂ , b₃ , ())
      lawClosure (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₂ (inj₂ U₂)) (b₁ , b₂ , b₃ , b₄) = lawClosureProof₂ (b₁ , b₂ , b₃ , b₄)
      lawClosure (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₂ (inj₁ S₁)) T U (b₁ , () , b₃ , b₄)
      lawClosure (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₂ (inj₂ S₂)) (inj₁ IdentTC) (inj₁ IdentTC) (b₁ , b₂ , b₃ , b₄) = lawClosureProof₂ (b₁ , b₂ , b₃ , b₄)
      lawClosure (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₂ (inj₂ S₂)) (inj₁ IdentTC) (inj₂ (inj₁ U₁)) (b₁ , b₂ , b₃ , ())
      lawClosure (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₂ (inj₂ S₂)) (inj₁ IdentTC) (inj₂ (inj₂ U₂)) (b₁ , b₂ , b₃ , b₄) = lawClosureProof₂ (b₁ , b₂ , b₃ , b₄)
      lawClosure (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₂ (inj₂ S₂)) (inj₂ (inj₁ T₁)) U (b₁ , b₂ , () , b₄)
      lawClosure (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₂ (inj₂ S₂)) (inj₂ (inj₂ T₂)) (inj₁ IdentTC) (b₁ , b₂ , b₃ , b₄) = lawClosureProof₂ (b₁ , b₂ , b₃ , b₄)
      lawClosure (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₂ (inj₂ S₂)) (inj₂ (inj₂ T₂)) (inj₂ (inj₁ U₁)) (b₁ , b₂ , b₃ , ())
      lawClosure (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₂ (inj₂ S₂)) (inj₂ (inj₂ T₂)) (inj₂ (inj₂ U₂)) (b₁ , b₂ , b₃ , b₄) = lawClosureProof₂ (b₁ , b₂ , b₃ , b₄)
      
      abstract
        lawAssocProof₁ :  ∀ (M N P R T S : IdTyCons ⊎ TyCons₁)
                       → (b₁ : B[ TC₁→TC M , TC₁→TC N ]▷ TC₁→TC P) (b₂ : B[ TC₁→TC P , TC₁→TC R ]▷ TC₁→TC T) 
                       → (b₃ : B[ TC₁→TC N , TC₁→TC R ]▷ TC₁→TC S) (b₄ : B[ TC₁→TC M , TC₁→TC S ]▷ TC₁→TC T)
                       → (eqBind₁ : B[ TC₁→TC M , TC₁→TC N ]▷ TC₁→TC P ≡ B[ M , N ] pm₁ ▷ P)
                       → (eqBind₂ : B[ TC₁→TC P , TC₁→TC R ]▷ TC₁→TC T ≡ B[ P , R ] pm₁ ▷ T)
                       → (eqBind₃ : B[ TC₁→TC N , TC₁→TC R ]▷ TC₁→TC S ≡ B[ N , R ] pm₁ ▷ S)
                       → (eqBind₄ : B[ TC₁→TC M , TC₁→TC S ]▷ TC₁→TC T ≡ B[ M , S ] pm₁ ▷ T)
                       → ∀ {α β γ : Type} (m : ⟨ TC₁→TC M ⟩ α) (f : α → ⟨ TC₁→TC N ⟩ β) (g : β → ⟨ TC₁→TC R ⟩ γ)
                       → (eqSubstBind₁ : bind {TC₁→TC M} {TC₁→TC N} {TC₁→TC P} b₁ m f
                                       ≡ substBind (eqTC₁ M) (eqTC₁ N) (eqTC₁ P) (pmBind pm₁ (subst (λ x → x) eqBind₁ b₁)) m f)
                       → (eqSubstBind₂ : (x : ⟨ TC₁→TC P ⟩ β) → bind {TC₁→TC P} {TC₁→TC R} {TC₁→TC T} b₂ x g
                                       ≡ substBind (eqTC₁ P) (eqTC₁ R) (eqTC₁ T) (pmBind pm₁ (subst (λ x → x) eqBind₂ b₂)) x g)
                       → (eqSubstBind₃ : (λ x → bind {TC₁→TC N} {TC₁→TC R} {TC₁→TC S} b₃ (f x) g)
                                       ≡ (λ x → substBind (eqTC₁ N) (eqTC₁ R) (eqTC₁ S) (pmBind pm₁ (subst (λ x → x) eqBind₃ b₃)) (f x) g))
                       → (eqSubstBind₄ : (x : α → ⟨ TC₁→TC S ⟩ γ) → bind {TC₁→TC M} {TC₁→TC S} {TC₁→TC T} b₄ m x
                                       ≡ substBind (eqTC₁ M) (eqTC₁ S) (eqTC₁ T) (pmBind pm₁ (subst (λ x → x) eqBind₄ b₄)) m x)
                       → (bind {TC₁→TC P} {TC₁→TC R} {TC₁→TC T} b₂) ((bind {TC₁→TC M} {TC₁→TC N} {TC₁→TC P} b₁) m f) g 
                       ≡ (bind {TC₁→TC M} {TC₁→TC S} {TC₁→TC T} b₄) m (λ x → (bind {TC₁→TC N} {TC₁→TC R} {TC₁→TC S}  b₃) (f x) g)
        lawAssocProof₁ M N P R T S b₁ b₂ b₃ b₄ eqBind₁ eqBind₂ eqBind₃ eqBind₄ {α = α} {β = β} {γ = γ} m f g eqSubstBind₁ eqSubstBind₂ eqSubstBind₃ eqSubstBind₄ =
          let bind₁ = bind {TC₁→TC M} {TC₁→TC N} {TC₁→TC P} b₁
              bind₂ = bind {TC₁→TC P} {TC₁→TC R} {TC₁→TC T} b₂
              bind₃ = bind {TC₁→TC N} {TC₁→TC R} {TC₁→TC S} b₃
              bind₄ = bind {TC₁→TC M} {TC₁→TC S} {TC₁→TC T} b₄
              eqM = eqTC₁ M
              eqN = eqTC₁ N
              eqP = eqTC₁ P
              eqR = eqTC₁ R
              eqT = eqTC₁ T
              eqS = eqTC₁ S
              pb₁ = subst (λ X → X) eqBind₁ b₁
              pb₂ = subst (λ X → X) eqBind₂ b₂
              pb₃ = subst (λ X → X) eqBind₃ b₃
              pb₄ = subst (λ X → X) eqBind₄ b₄
              pbind₁ = pmBind pm₁ pb₁
              pbind₂ = pmBind pm₁ pb₂
              pbind₃ = pmBind pm₁ pb₃
              pbind₄ = pmBind pm₁ pb₄
          in begin
          bind₂ (bind₁ m f) g 
            ≡⟨ cong (λ X → bind₂ X g) eqSubstBind₁ ⟩
          bind₂ (substBind eqM eqN eqP pbind₁ m f) g 
            ≡⟨ eqSubstBind₂ (substBind eqM eqN eqP pbind₁ m f) ⟩
          substBind eqP eqR eqT pbind₂ (substBind eqM eqN eqP pbind₁ m f) g 
            ≡⟨ substBindInwardEq pbind₂ eqP eqR eqT ((substBind eqM eqN eqP pbind₁ m f)) g ⟩
          subst (λ X → X γ) eqT (pbind₂ (subst (λ X → X β) (sym eqP) (substBind eqM eqN eqP pbind₁ m f)) (subst (λ X → (β → X γ)) (sym eqR) g)) 
            ≡⟨ cong (λ X → subst (λ X → X γ) eqT (pbind₂ (subst (λ X → X β) (sym eqP) X) (subst (λ X → (β → X γ)) (sym eqR) g)) ) 
                    (substBindInwardEq pbind₁ eqM eqN eqP m f) ⟩
          subst (λ X → X γ) eqT (pbind₂ 
                (subst (λ X → X β) (sym eqP) (subst (λ X → X β) eqP (pbind₁ 
                       (subst (λ X → X α) (sym eqM) m) 
                       (subst (λ X → (α → X β)) (sym eqN) f)))) 
                (subst (λ X → (β → X γ)) (sym eqR) g)) 
            ≡⟨ cong (λ X → subst (λ X → X γ) eqT (pbind₂ X (subst (λ X → (β → X γ)) (sym eqR) g))) (sym (x≡subst²x eqP)) ⟩
          subst (λ X → X γ) eqT (pbind₂ 
                (pbind₁ 
                       (subst (λ X → X α) (sym eqM) m) 
                       (subst (λ X → (α → X β)) (sym eqN) f))
                (subst (λ X → (β → X γ)) (sym eqR) g))
            ≡⟨ cong (λ X → subst (λ X → X γ) eqT X) (pmLawAssoc pm₁ M N P R T S pb₁ pb₂ pb₃ pb₄ {α} {β} {γ} 
                                                                (subst (λ X → X α) (sym eqM) m) 
                                                                (subst (λ X → (α → X β)) (sym eqN) f) 
                                                                (subst (λ X → (β → X γ)) (sym eqR) g)) ⟩
          subst (λ X → X γ) eqT (pbind₄ (subst (λ X → X α) (sym eqM) m) 
                                        (λ x → (pbind₃ ((subst (λ X → (α → X β)) (sym eqN) f) x) (subst (λ X → (β → X γ)) (sym eqR) g))) )
            ≡⟨ cong (λ X → subst (λ X → X γ) eqT (pbind₄ (subst (λ X → X α) (sym eqM) m) X)) 
                    (shiftApplySubstF (sym eqN) (λ X → (pbind₃ X (subst (λ X → (β → X γ)) (sym eqR) g))) f) ⟩
          subst (λ X → X γ) eqT (pbind₄ (subst (λ X → X α) (sym eqM) m) 
                                        (λ x → (pbind₃ (subst (λ X → X β) (sym eqN) (f x)) (subst (λ X → (β → X γ)) (sym eqR) g))) )
            ≡⟨ cong (λ X → subst (λ X → X γ) eqT (pbind₄ (subst (λ X → X α) (sym eqM) m) X )) (f≡subst²f eqS) ⟩
          subst (λ X → X γ) eqT (pbind₄ (subst (λ X → X α) (sym eqM) m) (subst (λ X → (α → X γ)) (sym eqS) 
                                        (subst (λ X → (α → X γ)) eqS (λ x → (pbind₃ (subst (λ X → X β) (sym eqN) (f x)) (subst (λ X → (β → X γ)) (sym eqR) g)))) ))
            ≡⟨ cong (λ X → subst (λ X → X γ) eqT (pbind₄ (subst (λ X → X α) (sym eqM) m) (subst (λ X → (α → X γ)) (sym eqS) X ))) 
                    (sym (shiftFunSubst eqS (λ x → (pbind₃ (subst (λ X → X β) (sym eqN) (f x)) (subst (λ X → (β → X γ)) (sym eqR) g)))) ) ⟩
          subst (λ X → X γ) eqT (pbind₄ (subst (λ X → X α) (sym eqM) m) (subst (λ X → (α → X γ)) (sym eqS) 
                                        (λ x → subst (λ X → X γ) eqS (pbind₃ (subst (λ X → X β) (sym eqN) (f x)) (subst (λ X → (β → X γ)) (sym eqR) g))) ))
            ≡⟨ refl ⟩
          subst (λ X → X γ) eqT (pbind₄ (subst (λ X → X α) (sym eqM) m) (subst (λ X → (α → X γ)) (sym eqS) 
                                        (λ x → subst (λ X → X γ) eqS (pbind₃ ((λ x → (subst (λ X → X β) (sym eqN) (f x))) x) (subst (λ X → (β → X γ)) (sym eqR) g))) ))
            ≡⟨ sym (substBindInwardEq pbind₄ eqM eqS eqT m 
                                      (λ x → subst (λ X → X γ) eqS (pbind₃ ((λ x → (subst (λ X → X β) (sym eqN) (f x))) x) (subst (λ X → (β → X γ)) (sym eqR) g)))) ⟩
          substBind eqM eqS eqT pbind₄ m (λ x → subst (λ X → X γ) eqS (pbind₃ ((λ x → (subst (λ X → X β) (sym eqN) (f x))) x) (subst (λ X → (β → X γ)) (sym eqR) g))) 
            ≡⟨ cong (λ X → substBind eqM eqS eqT pbind₄ m X) (sym (substBindInwardEqF pbind₃ eqN eqR eqS {γ = α} f g) ) ⟩
          substBind eqM eqS eqT pbind₄ m (λ x → substBind eqN eqR eqS pbind₃ (f x) g) 
            ≡⟨ sym (eqSubstBind₄ (λ x → substBind eqN eqR eqS pbind₃ (f x) g)) ⟩
          bind₄ m (λ x → substBind eqN eqR eqS pbind₃ (f x) g) 
            ≡⟨ cong (λ X → bind₄ m X) (sym eqSubstBind₃) ⟩
          bind₄ m (λ x → bind₃ (f x) g) ∎
        
        lawAssocHelp1 : (b : B[ idTC , idTC ]▷ idTC) 
                              → ∀ {α β : Type} (m : ⟨ idTC ⟩ α) (f : α → ⟨ idTC ⟩ β) 
                              → substBind eqId₁ eqId₁ eqId₁ (pmBind pm₁ b) m f
                              ≡ substBind eqId₂ eqId₂ eqId₂ (pmBind pm₂ (subst (λ x → x) eqIdBind b)) m f
        lawAssocHelp1 b {α = α} {β = β} m f = begin
          substBind eqId₁ eqId₁ eqId₁ (pmBind pm₁ b) m f ≡⟨ cong (λ x → x m f) (eqBindId₁ b) ⟩
          bindId m f ≡⟨ sym (cong (λ x → x m f) (eqBindId₂ ((subst (λ x → x) eqIdBind b)))) ⟩
          substBind eqId₂ eqId₂ eqId₂ (pmBind pm₂ (subst (λ x → x) eqIdBind b)) m f ∎
        
        lawAssocHelp2 : (b : B[ idTC , idTC ]▷ idTC) 
                      → ∀ {α β : Type} (f : α → ⟨ idTC ⟩ β) 
                      → ( (x : ⟨ idTC ⟩ α) → substBind eqId₁ eqId₁ eqId₁ (pmBind pm₁ b) x f
                                           ≡ substBind eqId₂ eqId₂ eqId₂ (pmBind pm₂ (subst (λ x → x) eqIdBind b)) x f)
        lawAssocHelp2 b f x = lawAssocHelp1 b x f

        lawAssocHelp3 : (b : B[ idTC , idTC ]▷ idTC) 
                              → ∀ {α β γ : Type} (f : α → ⟨ idTC ⟩ β) (g : β → ⟨ idTC ⟩ γ)
                              → (λ x → substBind eqId₁ eqId₁ eqId₁ (pmBind pm₁ b) (f x) g)
                              ≡ (λ x → substBind eqId₂ eqId₂ eqId₂ (pmBind pm₂ (subst (λ x → x) eqIdBind b)) (f x) g)
        lawAssocHelp3 b {α = α} {β = β} {γ = γ} f g = begin
          (λ x → substBind eqId₁ eqId₁ eqId₁ (pmBind pm₁ b) (f x) g) ≡⟨ cong (λ bind → (λ x → bind (f x) g)) (eqBindId₁ b) ⟩
          (λ x → bindId (f x) g) ≡⟨ sym (cong (λ bind x → bind (f x) g) (eqBindId₂ ((subst (λ x → x) eqIdBind b)))) ⟩
          (λ x → substBind eqId₂ eqId₂ eqId₂ (pmBind pm₂ (subst (λ x → x) eqIdBind b)) (f x) g) ∎
        
        lawAssocHelp4 : (b : B[ idTC , idTC ]▷ idTC) 
                      → ∀ {α β : Type} (m : ⟨ idTC ⟩ α) 
                      → ( (x : α → ⟨ idTC ⟩ β) → substBind eqId₁ eqId₁ eqId₁ (pmBind pm₁ b) m x
                                               ≡ substBind eqId₂ eqId₂ eqId₂ (pmBind pm₂ (subst (λ x → x) eqIdBind b)) m x )
        lawAssocHelp4 b m x = lawAssocHelp1 b m x


        
        lawAssocProof₂ :  ∀ (M N P R T S : IdTyCons ⊎ TyCons₂)
                       → (b₁ : B[ TC₂→TC M , TC₂→TC N ]▷ TC₂→TC P) (b₂ : B[ TC₂→TC P , TC₂→TC R ]▷ TC₂→TC T) 
                       → (b₃ : B[ TC₂→TC N , TC₂→TC R ]▷ TC₂→TC S) (b₄ : B[ TC₂→TC M , TC₂→TC S ]▷ TC₂→TC T)
                       → (eqBind₁ : B[ TC₂→TC M , TC₂→TC N ]▷ TC₂→TC P ≡ B[ M , N ] pm₂ ▷ P)
                       → (eqBind₂ : B[ TC₂→TC P , TC₂→TC R ]▷ TC₂→TC T ≡ B[ P , R ] pm₂ ▷ T)
                       → (eqBind₃ : B[ TC₂→TC N , TC₂→TC R ]▷ TC₂→TC S ≡ B[ N , R ] pm₂ ▷ S)
                       → (eqBind₄ : B[ TC₂→TC M , TC₂→TC S ]▷ TC₂→TC T ≡ B[ M , S ] pm₂ ▷ T)
                       → ∀ {α β γ : Type} (m : ⟨ TC₂→TC M ⟩ α) (f : α → ⟨ TC₂→TC N ⟩ β) (g : β → ⟨ TC₂→TC R ⟩ γ)
                       → (eqSubstBind₁ : bind {TC₂→TC M} {TC₂→TC N} {TC₂→TC P} b₁ m f
                                       ≡ substBind (eqTC₂ M) (eqTC₂ N) (eqTC₂ P) (pmBind pm₂ (subst (λ x → x) eqBind₁ b₁)) m f)
                       → (eqSubstBind₂ : (x : ⟨ TC₂→TC P ⟩ β) → bind {TC₂→TC P} {TC₂→TC R} {TC₂→TC T} b₂ x g
                                       ≡ substBind (eqTC₂ P) (eqTC₂ R) (eqTC₂ T) (pmBind pm₂ (subst (λ x → x) eqBind₂ b₂)) x g)
                       → (eqSubstBind₃ : (λ x → bind {TC₂→TC N} {TC₂→TC R} {TC₂→TC S} b₃ (f x) g)
                                       ≡ (λ x → substBind (eqTC₂ N) (eqTC₂ R) (eqTC₂ S) (pmBind pm₂ (subst (λ x → x) eqBind₃ b₃)) (f x) g))
                       → (eqSubstBind₄ : (x : α → ⟨ TC₂→TC S ⟩ γ) → bind {TC₂→TC M} {TC₂→TC S} {TC₂→TC T} b₄ m x
                                       ≡ substBind (eqTC₂ M) (eqTC₂ S) (eqTC₂ T) (pmBind pm₂ (subst (λ x → x) eqBind₄ b₄)) m x)
                       → (bind {TC₂→TC P} {TC₂→TC R} {TC₂→TC T} b₂) ((bind {TC₂→TC M} {TC₂→TC N} {TC₂→TC P} b₁) m f) g 
                       ≡ (bind {TC₂→TC M} {TC₂→TC S} {TC₂→TC T} b₄) m (λ x → (bind {TC₂→TC N} {TC₂→TC R} {TC₂→TC S}  b₃) (f x) g)
        lawAssocProof₂ M N P R T S b₁ b₂ b₃ b₄ eqBind₁ eqBind₂ eqBind₃ eqBind₄ {α = α} {β = β} {γ = γ} m f g eqSubstBind₁ eqSubstBind₂ eqSubstBind₃ eqSubstBind₄ = 
          let bind₁ = bind {TC₂→TC M} {TC₂→TC N} {TC₂→TC P} b₁
              bind₂ = bind {TC₂→TC P} {TC₂→TC R} {TC₂→TC T} b₂
              bind₃ = bind {TC₂→TC N} {TC₂→TC R} {TC₂→TC S} b₃
              bind₄ = bind {TC₂→TC M} {TC₂→TC S} {TC₂→TC T} b₄
              eqM = eqTC₂ M
              eqN = eqTC₂ N
              eqP = eqTC₂ P
              eqR = eqTC₂ R
              eqT = eqTC₂ T
              eqS = eqTC₂ S
              pb₁ = subst (λ X → X) eqBind₁ b₁
              pb₂ = subst (λ X → X) eqBind₂ b₂
              pb₃ = subst (λ X → X) eqBind₃ b₃
              pb₄ = subst (λ X → X) eqBind₄ b₄
              pbind₁ = pmBind pm₂ pb₁
              pbind₂ = pmBind pm₂ pb₂
              pbind₃ = pmBind pm₂ pb₃
              pbind₄ = pmBind pm₂ pb₄
          in begin
          bind₂ (bind₁ m f) g 
            ≡⟨ cong (λ X → bind₂ X g) eqSubstBind₁ ⟩
          bind₂ (substBind eqM eqN eqP pbind₁ m f) g 
            ≡⟨ eqSubstBind₂ (substBind eqM eqN eqP pbind₁ m f) ⟩
          substBind eqP eqR eqT pbind₂ (substBind eqM eqN eqP pbind₁ m f) g 
            ≡⟨ substBindInwardEq pbind₂ eqP eqR eqT ((substBind eqM eqN eqP pbind₁ m f)) g ⟩
          subst (λ X → X γ) eqT (pbind₂ (subst (λ X → X β) (sym eqP) (substBind eqM eqN eqP pbind₁ m f)) (subst (λ X → (β → X γ)) (sym eqR) g)) 
            ≡⟨ cong (λ X → subst (λ X → X γ) eqT (pbind₂ (subst (λ X → X β) (sym eqP) X) (subst (λ X → (β → X γ)) (sym eqR) g)) ) 
                    (substBindInwardEq pbind₁ eqM eqN eqP m f) ⟩
          subst (λ X → X γ) eqT (pbind₂ 
                (subst (λ X → X β) (sym eqP) (subst (λ X → X β) eqP (pbind₁ 
                       (subst (λ X → X α) (sym eqM) m) 
                       (subst (λ X → (α → X β)) (sym eqN) f)))) 
                (subst (λ X → (β → X γ)) (sym eqR) g)) 
            ≡⟨ cong (λ X → subst (λ X → X γ) eqT (pbind₂ X (subst (λ X → (β → X γ)) (sym eqR) g))) (sym (x≡subst²x eqP)) ⟩
          subst (λ X → X γ) eqT (pbind₂ 
                (pbind₁ 
                       (subst (λ X → X α) (sym eqM) m) 
                       (subst (λ X → (α → X β)) (sym eqN) f))
                (subst (λ X → (β → X γ)) (sym eqR) g))
            ≡⟨ cong (λ X → subst (λ X → X γ) eqT X) (pmLawAssoc pm₂ M N P R T S pb₁ pb₂ pb₃ pb₄ {α} {β} {γ} 
                                                                (subst (λ X → X α) (sym eqM) m) 
                                                                (subst (λ X → (α → X β)) (sym eqN) f) 
                                                                (subst (λ X → (β → X γ)) (sym eqR) g)) ⟩
          subst (λ X → X γ) eqT (pbind₄ (subst (λ X → X α) (sym eqM) m) 
                                        (λ x → (pbind₃ ((subst (λ X → (α → X β)) (sym eqN) f) x) (subst (λ X → (β → X γ)) (sym eqR) g))) )
            ≡⟨ cong (λ X → subst (λ X → X γ) eqT (pbind₄ (subst (λ X → X α) (sym eqM) m) X)) 
                    (shiftApplySubstF (sym eqN) (λ X → (pbind₃ X (subst (λ X → (β → X γ)) (sym eqR) g))) f) ⟩
          subst (λ X → X γ) eqT (pbind₄ (subst (λ X → X α) (sym eqM) m) 
                                        (λ x → (pbind₃ (subst (λ X → X β) (sym eqN) (f x)) (subst (λ X → (β → X γ)) (sym eqR) g))) )
            ≡⟨ cong (λ X → subst (λ X → X γ) eqT (pbind₄ (subst (λ X → X α) (sym eqM) m) X )) (f≡subst²f eqS) ⟩
          subst (λ X → X γ) eqT (pbind₄ (subst (λ X → X α) (sym eqM) m) (subst (λ X → (α → X γ)) (sym eqS) 
                                        (subst (λ X → (α → X γ)) eqS (λ x → (pbind₃ (subst (λ X → X β) (sym eqN) (f x)) (subst (λ X → (β → X γ)) (sym eqR) g)))) ))
            ≡⟨ cong (λ X → subst (λ X → X γ) eqT (pbind₄ (subst (λ X → X α) (sym eqM) m) (subst (λ X → (α → X γ)) (sym eqS) X ))) 
                    (sym (shiftFunSubst eqS (λ x → (pbind₃ (subst (λ X → X β) (sym eqN) (f x)) (subst (λ X → (β → X γ)) (sym eqR) g)))) ) ⟩
          subst (λ X → X γ) eqT (pbind₄ (subst (λ X → X α) (sym eqM) m) (subst (λ X → (α → X γ)) (sym eqS) 
                                        (λ x → subst (λ X → X γ) eqS (pbind₃ (subst (λ X → X β) (sym eqN) (f x)) (subst (λ X → (β → X γ)) (sym eqR) g))) ))
            ≡⟨ refl ⟩
          subst (λ X → X γ) eqT (pbind₄ (subst (λ X → X α) (sym eqM) m) (subst (λ X → (α → X γ)) (sym eqS) 
                                        (λ x → subst (λ X → X γ) eqS (pbind₃ ((λ x → (subst (λ X → X β) (sym eqN) (f x))) x) (subst (λ X → (β → X γ)) (sym eqR) g))) ))
            ≡⟨ sym (substBindInwardEq pbind₄ eqM eqS eqT m 
                                      (λ x → subst (λ X → X γ) eqS (pbind₃ ((λ x → (subst (λ X → X β) (sym eqN) (f x))) x) (subst (λ X → (β → X γ)) (sym eqR) g)))) ⟩
          substBind eqM eqS eqT pbind₄ m (λ x → subst (λ X → X γ) eqS (pbind₃ ((λ x → (subst (λ X → X β) (sym eqN) (f x))) x) (subst (λ X → (β → X γ)) (sym eqR) g))) 
            ≡⟨ cong (λ X → substBind eqM eqS eqT pbind₄ m X) (sym (substBindInwardEqF pbind₃ eqN eqR eqS {γ = α} f g) ) ⟩
          substBind eqM eqS eqT pbind₄ m (λ x → substBind eqN eqR eqS pbind₃ (f x) g) 
            ≡⟨ sym (eqSubstBind₄ (λ x → substBind eqN eqR eqS pbind₃ (f x) g)) ⟩
          bind₄ m (λ x → substBind eqN eqR eqS pbind₃ (f x) g) 
            ≡⟨ cong (λ X → bind₄ m X) (sym eqSubstBind₃) ⟩
          bind₄ m (λ x → bind₃ (f x) g) ∎
      
      lawAssoc : ∀ (M N P R T S : TyCons) 
               → (b₁ : B[ M , N ]▷ P) (b₂ : B[ P , R ]▷ T) 
               → (b₃ : B[ N , R ]▷ S) (b₄ : B[ M , S ]▷ T)
               → ∀ {α β γ : Type} (m : ⟨ M ⟩ α) (f : α → ⟨ N ⟩ β) (g : β → ⟨ R ⟩ γ)
               → (bind {P} {R} {T} b₂) ((bind {M} {N} {P} b₁) m f) g ≡ (bind {M} {S} {T} b₄) m (λ x → (bind {N} {R} {S}  b₃) (f x) g)
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g =
        lawAssocProof₁ idTC idTC idTC idTC idTC idTC b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ S₁)) b₁ b₂ b₃ b₄ m f g =
        lawAssocProof₁ idTC idTC idTC idTC idTC (inj₂ S₁) b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ S₂)) b₁ b₂ b₃ b₄ m f g =
        lawAssocProof₂ idTC idTC idTC idTC idTC (inj₂ S₂) b₁ b₂ b₃ b₄ eqIdBind eqIdBind refl refl m f g (lawAssocHelp1 b₁ m f) (lawAssocHelp2 b₂ g) refl (λ x → refl)
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₁ idTC idTC idTC idTC (inj₂ T₁) idTC b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₂ (inj₁ S₁)) b₁ b₂ b₃ b₄ m f g =
        lawAssocProof₁ idTC idTC idTC idTC (inj₂ T₁) (inj₂ S₁) b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₂ (inj₂ S₂)) b₁ b₂ b₃ () m f g
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g =
        lawAssocProof₂ idTC idTC idTC idTC (inj₂ T₂) idTC b₁ b₂ b₃ b₄ eqIdBind refl eqIdBind refl m f g (lawAssocHelp1 b₁ m f) (λ x → refl) (lawAssocHelp3 b₃ f g) (λ x → refl)
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₂ (inj₁ S₁)) b₁ b₂ b₃ () m f g
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₂ (inj₂ S₂)) b₁ b₂ b₃ b₄ m f g =
        lawAssocProof₂ idTC idTC idTC idTC (inj₂ T₂) (inj₂ S₂) b₁ b₂ b₃ b₄ eqIdBind refl refl refl m f g (lawAssocHelp1 b₁ m f) (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g =
        lawAssocProof₁ idTC idTC idTC (inj₂ R₁) idTC idTC b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₂ (inj₁ S₁)) b₁ b₂ b₃ b₄ m f g =
        lawAssocProof₁ idTC idTC idTC (inj₂ R₁) idTC (inj₂ S₁) b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₂ (inj₂ S₂)) b₁ b₂ () b₄ m f g
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₂ (inj₁ T₁)) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g =
        lawAssocProof₁ idTC idTC idTC (inj₂ R₁) (inj₂ T₁) idTC b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₂ (inj₁ T₁)) (inj₂ (inj₁ S₁)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₁ idTC idTC idTC (inj₂ R₁) (inj₂ T₁) (inj₂ S₁) b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₂ (inj₁ T₁)) (inj₂ (inj₂ S₂)) b₁ b₂ () () m f g
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₂ (inj₂ T₂)) S b₁ () b₃ b₄ m f g
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₂ idTC idTC idTC (inj₂ R₂) idTC idTC b₁ b₂ b₃ b₄ eqIdBind refl refl eqIdBind m f g (lawAssocHelp1 b₁ m f) (λ x → refl) refl (lawAssocHelp4 b₄ m)
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₂ (inj₁ S₁)) b₁ b₂ () b₄ m f g
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₂ (inj₂ S₂)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₂ idTC idTC idTC (inj₂ R₂) idTC (inj₂ S₂) b₁ b₂ b₃ b₄ eqIdBind refl refl refl m f g (lawAssocHelp1 b₁ m f) (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₂ (inj₁ T₁)) S b₁ () b₃ b₄ m f g
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₂ (inj₂ T₂)) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₂ idTC idTC idTC (inj₂ R₂) (inj₂ T₂) idTC b₁ b₂ b₃ b₄ eqIdBind refl refl refl m f g (lawAssocHelp1 b₁ m f) (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₂ (inj₂ T₂)) (inj₂ (inj₁ S₁)) b₁ b₂ () () m f g
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₂ (inj₂ T₂)) (inj₂ (inj₂ S₂)) b₁ b₂ b₃ b₄ m f g =
        lawAssocProof₂ idTC idTC idTC (inj₂ R₂) (inj₂ T₂) (inj₂ S₂) b₁ b₂ b₃ b₄ eqIdBind refl refl refl m f g (lawAssocHelp1 b₁ m f) (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g =
        lawAssocProof₁ idTC idTC (inj₂ P₁) idTC idTC idTC b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ S₁)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₁ idTC idTC (inj₂ P₁) idTC idTC (inj₂ S₁) b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ S₂)) b₁ b₂ b₃ b₄ m f g with idMorph¬∃₁ (inj₁ (P₁ , refl)) b₂
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ S₂)) b₁ b₂ b₃ b₄ m f g | ()
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g =
        lawAssocProof₁ idTC idTC (inj₂ P₁) idTC (inj₂ T₁) idTC b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₂ (inj₁ S₁)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₁ idTC idTC (inj₂ P₁) idTC (inj₂ T₁) (inj₂ S₁) b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₂ (inj₂ S₂)) b₁ b₂ b₃ () m f g
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) S b₁ () b₃ b₄ m f g
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g =
        lawAssocProof₁ idTC idTC (inj₂ P₁) (inj₂ R₁) idTC idTC b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₂ (inj₁ S₁)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₁ idTC idTC (inj₂ P₁) (inj₂ R₁) idTC (inj₂ S₁) b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₂ (inj₂ S₂)) b₁ b₂ () b₄ m f g
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) (inj₂ (inj₁ R₁)) (inj₂ (inj₁ T₁)) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₁ idTC idTC (inj₂ P₁) (inj₂ R₁) (inj₂ T₁) idTC b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) (inj₂ (inj₁ R₁)) (inj₂ (inj₁ T₁)) (inj₂ (inj₁ S₁)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₁ idTC idTC (inj₂ P₁) (inj₂ R₁) (inj₂ T₁) (inj₂ S₁) b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) (inj₂ (inj₁ R₁)) (inj₂ (inj₁ T₁)) (inj₂ (inj₂ S₂)) b₁ b₂ () () m f g
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) (inj₂ (inj₁ R₁)) (inj₂ (inj₂ T₂)) S b₁ () b₃ b₄ m f g
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) S b₁ () b₃ b₄ m f g
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) (inj₂ (inj₂ R₂)) (inj₂ (inj₁ T₁)) S b₁ () b₃ b₄ m f g
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) (inj₂ (inj₂ R₂)) (inj₂ (inj₂ T₂)) S b₁ () b₃ b₄ m f g
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g =
        lawAssocProof₂ idTC idTC (inj₂ P₂) idTC idTC idTC b₁ b₂ b₃ b₄ refl refl eqIdBind eqIdBind m f g refl (λ x → refl) (lawAssocHelp3 b₃ f g) (lawAssocHelp4 b₄ m)
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ S₁)) b₁ b₂ b₃ b₄ m f g with idMorph¬∃₂ (inj₁ (P₂ , refl)) b₂
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ S₁)) b₁ b₂ b₃ b₄ m f g | ()
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ S₂)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₂ idTC idTC (inj₂ P₂) idTC idTC (inj₂ S₂) b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) S b₁ () b₃ b₄ m f g
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g =
        lawAssocProof₂ idTC idTC (inj₂ P₂) idTC (inj₂ T₂) idTC b₁ b₂ b₃ b₄ refl refl eqIdBind refl m f g refl (λ x → refl) (lawAssocHelp3 b₃ f g) (λ x → refl)
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₂ (inj₁ S₁)) b₁ b₂ b₃ () m f g
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₂ (inj₂ S₂)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₂ idTC idTC (inj₂ P₂) idTC (inj₂ T₂) (inj₂ S₂) b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) S b₁() b₃ b₄ m f g
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) (inj₂ (inj₁ R₁)) (inj₂ (inj₁ T₁)) S b₁ () b₃ b₄ m f g
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) (inj₂ (inj₁ R₁)) (inj₂ (inj₂ T₂)) S b₁ () b₃ b₄ m f g
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g =
        lawAssocProof₂ idTC idTC (inj₂ P₂) (inj₂ R₂) idTC idTC b₁ b₂ b₃ b₄ refl refl refl eqIdBind m f g refl (λ x → refl) refl (lawAssocHelp4 b₄ m)
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₂ (inj₁ S₁)) b₁ b₂ () b₄ m f g
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₂ (inj₂ S₂)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₂ idTC idTC (inj₂ P₂) (inj₂ R₂) idTC (inj₂ S₂) b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) (inj₂ (inj₂ R₂)) (inj₂ (inj₁ T₁)) S b₁ () b₃ b₄ m f g
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) (inj₂ (inj₂ R₂)) (inj₂ (inj₂ T₂)) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₂ idTC idTC (inj₂ P₂) (inj₂ R₂) (inj₂ T₂) idTC b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) (inj₂ (inj₂ R₂)) (inj₂ (inj₂ T₂)) (inj₂ (inj₁ S₁)) b₁ b₂ () () m f g
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) (inj₂ (inj₂ R₂)) (inj₂ (inj₂ T₂)) (inj₂ (inj₂ S₂)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₂ idTC idTC (inj₂ P₂) (inj₂ R₂) (inj₂ T₂) (inj₂ S₂) b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₁ idTC (inj₂ N₁) idTC idTC idTC idTC b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₁ idTC (inj₂ N₁) idTC idTC (inj₂ T₁) idTC b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g with idMorph¬∃₁ (inj₁ (N₁ , refl)) b₃
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g | ()
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ S₁)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₁ idTC (inj₂ N₁) idTC idTC idTC (inj₂ S₁) b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₂ (inj₁ S₁)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₁ idTC (inj₂ N₁) idTC idTC (inj₂ T₁) (inj₂ S₁) b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₂ (inj₁ S₁)) b₁ b₂ b₃ () m f g
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₁ IdentTC) T (inj₂ (inj₂ S₂)) b₁ b₂ () b₄ m f g
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₁ idTC (inj₂ N₁) idTC (inj₂ R₁) idTC idTC b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₂ (inj₁ T₁)) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₁ idTC (inj₂ N₁) idTC (inj₂ R₁) (inj₂ T₁) idTC b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₂ (inj₂ T₂)) (inj₁ IdentTC) b₁ () b₃ b₄ m f g
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₂ (inj₁ S₁)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₁ idTC (inj₂ N₁) idTC (inj₂ R₁) idTC (inj₂ S₁) b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₂ (inj₁ T₁)) (inj₂ (inj₁ S₁)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₁ idTC (inj₂ N₁) idTC (inj₂ R₁) (inj₂ T₁) (inj₂ S₁) b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₂ (inj₂ T₂)) (inj₂ (inj₁ S₁)) b₁ () b₃ () m f g
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) T (inj₂ (inj₂ S₂)) b₁ b₂ () b₄ m f g
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) T (inj₁ IdentTC) b₁ b₂ () b₄ m f g
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) T (inj₂ (inj₁ S₁)) b₁ b₂ () b₄ m f g
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) T (inj₂ (inj₂ S₂)) b₁ b₂ () b₄ m f g
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ P₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₁ idTC (inj₂ N₁) (inj₂ P₁) idTC idTC idTC b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ P₁)) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₁ idTC (inj₂ N₁) (inj₂ P₁) idTC (inj₂ T₁) idTC b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ P₁)) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₁ IdentTC) b₁ () b₃ b₄ m f g
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ P₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ S₁)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₁ idTC (inj₂ N₁) (inj₂ P₁) idTC idTC (inj₂ S₁) b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ P₁)) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₂ (inj₁ S₁)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₁ idTC (inj₂ N₁) (inj₂ P₁) idTC (inj₂ T₁) (inj₂ S₁) b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ P₁)) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₂ (inj₁ S₁)) b₁ () b₃ () m f g
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ P₁)) (inj₁ IdentTC) T (inj₂ (inj₂ S₂)) b₁ b₂ () b₄ m f g
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ P₁)) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₁ idTC (inj₂ N₁) (inj₂ P₁) (inj₂ R₁) idTC idTC b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ P₁)) (inj₂ (inj₁ R₁)) (inj₂ (inj₁ T₁)) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₁ idTC (inj₂ N₁) (inj₂ P₁) (inj₂ R₁) (inj₂ T₁) idTC b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ P₁)) (inj₂ (inj₁ R₁)) (inj₂ (inj₂ T₂)) (inj₁ IdentTC) b₁ () b₃ b₄ m f g
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ P₁)) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₂ (inj₁ S₁)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₁ idTC (inj₂ N₁) (inj₂ P₁) (inj₂ R₁) idTC (inj₂ S₁) b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ P₁)) (inj₂ (inj₁ R₁)) (inj₂ (inj₁ T₁)) (inj₂ (inj₁ S₁)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₁ idTC (inj₂ N₁) (inj₂ P₁) (inj₂ R₁) (inj₂ T₁) (inj₂ S₁) b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ P₁)) (inj₂ (inj₁ R₁)) (inj₂ (inj₂ T₂)) (inj₂ (inj₁ S₁)) b₁ () b₃ () m f g
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ P₁)) (inj₂ (inj₁ R₁)) T (inj₂ (inj₂ S₂)) b₁ b₂ () b₄ m f g
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ P₁)) (inj₂ (inj₂ R₂)) T (inj₁ IdentTC) b₁ b₂ () b₄ m f g
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ P₁)) (inj₂ (inj₂ R₂)) T (inj₂ (inj₁ S₁)) b₁ b₂ () b₄ m f g
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ P₁)) (inj₂ (inj₂ R₂)) T (inj₂ (inj₂ S₂)) b₁ b₂ () b₄ m f g
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₁ N₁)) (inj₂ (inj₂ P₂)) R T S () b₂ b₃ b₄ m f g
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₂ idTC (inj₂ N₂) idTC idTC idTC idTC b₁ b₂ b₃ b₄ refl eqIdBind refl eqIdBind m f g refl (lawAssocHelp2 b₂ g) refl (lawAssocHelp4 b₄ m)
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g with idMorph¬∃₂ (inj₁ (N₂ , refl)) b₃
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g | ()
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₂ idTC (inj₂ N₂) idTC idTC (inj₂ T₂) idTC b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₁ IdentTC) T (inj₂ (inj₁ S₁)) b₁ b₂ () b₄ m f g
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ S₂)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₂ idTC (inj₂ N₂) idTC idTC idTC (inj₂ S₂) b₁ b₂ b₃ b₄ refl eqIdBind refl refl m f g refl (lawAssocHelp2 b₂ g) refl (λ x → refl)
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₂ (inj₂ S₂)) b₁ b₂ b₃ () m f g
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₂ (inj₂ S₂)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₂ idTC (inj₂ N₂) idTC idTC (inj₂ T₂) (inj₂ S₂) b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) T (inj₁ IdentTC) b₁ b₂ () b₄ m f g
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) T (inj₂ (inj₁ S₁)) b₁ b₂ () b₄ m f g
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) T (inj₂ (inj₂ S₂)) b₁ b₂ () b₄ m f g
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₂ idTC (inj₂ N₂) idTC (inj₂ R₂) idTC idTC b₁ b₂ b₃ b₄ refl refl refl eqIdBind m f g refl (λ x → refl) refl (lawAssocHelp4 b₄ m)
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₂ (inj₁ T₁)) (inj₁ IdentTC) b₁ () b₃ b₄ m f g
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₂ (inj₂ T₂)) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₂ idTC (inj₂ N₂) idTC (inj₂ R₂) (inj₂ T₂) idTC b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) T (inj₂ (inj₁ S₁)) b₁ b₂ () b₄ m f g
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₂ (inj₂ S₂)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₂ idTC (inj₂ N₂) idTC (inj₂ R₂) idTC (inj₂ S₂) b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₂ (inj₁ T₁)) (inj₂ (inj₂ S₂)) b₁ () b₃ () m f g
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₂ (inj₂ T₂)) (inj₂ (inj₂ S₂)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₂ idTC (inj₂ N₂) idTC (inj₂ R₂) (inj₂ T₂) (inj₂ S₂) b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₁ P₁)) R T S () b₂ b₃ b₄ m f g
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₂ idTC (inj₂ N₂) (inj₂ P₂) idTC idTC idTC b₁ b₂ b₃ b₄ refl refl refl eqIdBind m f g refl (λ x → refl) refl (lawAssocHelp4 b₄ m)
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ S₁)) b₁ b₂ () b₄ m f g
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ S₂)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₂ idTC (inj₂ N₂) (inj₂ P₂) idTC idTC (inj₂ S₂) b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) S b₁ () b₃ b₄ m f g
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₂ idTC (inj₂ N₂) (inj₂ P₂) idTC (inj₂ T₂) idTC b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₂ (inj₁ S₁)) b₁ b₂ () () m f g
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₂ (inj₂ S₂)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₂ idTC (inj₂ N₂) (inj₂ P₂) idTC (inj₂ T₂) (inj₂ S₂) b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₁ IdentTC) b₁ () () b₄ m f g
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₂ (inj₁ S₁)) b₁ () () b₄ m f g
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₂ (inj₂ S₂)) b₁ () () b₄ m f g
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₂ (inj₁ R₁)) (inj₂ (inj₁ T₁)) S b₁ () b₃ b₄ m f g
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₂ (inj₁ R₁)) (inj₂ (inj₂ T₂)) (inj₁ IdentTC) b₁ () () b₄ m f g
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₂ (inj₁ R₁)) (inj₂ (inj₂ T₂)) (inj₂ (inj₁ S₁)) b₁ () () () m f g
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₂ (inj₁ R₁)) (inj₂ (inj₂ T₂)) (inj₂ (inj₂ S₂)) b₁ () () b₄ m f g
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₂ idTC (inj₂ N₂) (inj₂ P₂) (inj₂ R₂) idTC idTC b₁ b₂ b₃ b₄ refl refl refl eqIdBind m f g refl (λ x → refl) refl (lawAssocHelp4 b₄ m)
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₂ (inj₁ S₁)) b₁ b₂ () b₄ m f g
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₂ (inj₂ S₂)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₂ idTC (inj₂ N₂) (inj₂ P₂) (inj₂ R₂) idTC (inj₂ S₂) b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₂ (inj₂ R₂)) (inj₂ (inj₁ T₁)) S b₁ () b₃ b₄ m f g
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₂ (inj₂ R₂)) (inj₂ (inj₂ T₂)) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₂ idTC (inj₂ N₂) (inj₂ P₂) (inj₂ R₂) (inj₂ T₂) idTC b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₂ (inj₂ R₂)) (inj₂ (inj₂ T₂)) (inj₂ (inj₁ S₁)) b₁ b₂ () () m f g
      lawAssoc (inj₁ IdentTC) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₂ (inj₂ R₂)) (inj₂ (inj₂ T₂)) (inj₂ (inj₂ S₂)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₂ idTC (inj₂ N₂) (inj₂ P₂) (inj₂ R₂) (inj₂ T₂) (inj₂ S₂) b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₁ (inj₂ M₁) idTC idTC idTC idTC idTC b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₁ (inj₂ M₁) idTC idTC (inj₂ R₁) idTC idTC b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g with idMorph¬∃₁ (inj₁ (M₁ , refl)) b₁
      lawAssoc (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g | ()
      lawAssoc (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ S₁)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₁ (inj₂ M₁) idTC idTC idTC idTC (inj₂ S₁) b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₂ (inj₁ S₁)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₁ (inj₂ M₁) idTC idTC (inj₂ R₁) idTC (inj₂ S₁) b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₂ (inj₁ S₁)) b₁ b₂ () b₄ m f g
      lawAssoc (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₁ IdentTC) R (inj₁ IdentTC) (inj₂ (inj₂ S₂)) b₁ b₂ b₃ () m f g
      lawAssoc (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₁ (inj₂ M₁) idTC idTC idTC (inj₂ T₁) idTC b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₂ (inj₁ T₁)) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₁ (inj₂ M₁) idTC idTC (inj₂ R₁) (inj₂ T₁) idTC b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₂ (inj₁ T₁)) (inj₁ IdentTC) b₁ () b₃ b₄ m f g
      lawAssoc (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₂ (inj₁ S₁)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₁ (inj₂ M₁) idTC idTC idTC (inj₂ T₁) (inj₂ S₁) b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₂ (inj₁ T₁)) (inj₂ (inj₁ S₁)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₁ (inj₂ M₁) idTC idTC (inj₂ R₁) (inj₂ T₁) (inj₂ S₁) b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₂ (inj₁ T₁)) (inj₂ (inj₁ S₁)) b₁ () () b₄ m f g
      lawAssoc (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₁ IdentTC) R (inj₂ (inj₁ T₁)) (inj₂ (inj₂ S₂)) b₁ b₂ b₃ () m f g
      lawAssoc (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₁ IdentTC) R (inj₂ (inj₂ T₂)) (inj₁ IdentTC) b₁ b₂ b₃ () m f g
      lawAssoc (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₁ IdentTC) R (inj₂ (inj₂ T₂)) (inj₂ (inj₁ S₁)) b₁ b₂ b₃ () m f g
      lawAssoc (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₁ IdentTC) R (inj₂ (inj₂ T₂)) (inj₂ (inj₂ S₂)) b₁ b₂ b₃ () m f g
      lawAssoc (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₁ (inj₂ M₁) idTC (inj₂ P₁) idTC idTC idTC b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ S₁)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₁ (inj₂ M₁) idTC (inj₂ P₁) idTC idTC (inj₂ S₁) b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ S₂)) b₁ b₂ b₃ () m f g
      lawAssoc (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₁ (inj₂ M₁) idTC (inj₂ P₁) idTC (inj₂ T₁) idTC b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₂ (inj₁ S₁)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₁ (inj₂ M₁) idTC (inj₂ P₁) idTC (inj₂ T₁) (inj₂ S₁) b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₂ (inj₂ S₂)) b₁ b₂ b₃ () m f g
      lawAssoc (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) S b₁ () b₃ b₄ m f g
      lawAssoc (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₁ (inj₂ M₁) idTC (inj₂ P₁) (inj₂ R₁) idTC idTC b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₂ (inj₁ S₁)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₁ (inj₂ M₁) idTC (inj₂ P₁) (inj₂ R₁) idTC (inj₂ S₁) b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₂ (inj₂ S₂)) b₁ b₂ () () m f g
      lawAssoc (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) (inj₂ (inj₁ R₁)) (inj₂ (inj₁ T₁)) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₁ (inj₂ M₁) idTC (inj₂ P₁) (inj₂ R₁) (inj₂ T₁) idTC b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) (inj₂ (inj₁ R₁)) (inj₂ (inj₁ T₁)) (inj₂ (inj₁ S₁)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₁ (inj₂ M₁) idTC (inj₂ P₁) (inj₂ R₁) (inj₂ T₁) (inj₂ S₁) b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) (inj₂ (inj₁ R₁)) (inj₂ (inj₁ T₁)) (inj₂ (inj₂ S₂)) b₁ b₂ () () m f g
      lawAssoc (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) (inj₂ (inj₁ R₁)) (inj₂ (inj₂ T₂)) S b₁ () b₃ b₄ m f g
      lawAssoc (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) S b₁ () b₃ b₄ m f g
      lawAssoc (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) (inj₂ (inj₂ R₂)) (inj₂ (inj₁ T₁)) S b₁ () b₃ b₄ m f g
      lawAssoc (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) (inj₂ (inj₂ R₂)) (inj₂ (inj₂ T₂)) S b₁ () b₃ b₄ m f g
      lawAssoc (inj₂ (inj₁ M₁)) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) R T S () b₂ b₃ b₄ m f g
      lawAssoc (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₁ (inj₂ M₁) (inj₂ N₁) idTC idTC idTC idTC b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₁ (inj₂ M₁) (inj₂ N₁) idTC (inj₂ R₁) idTC idTC b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₁ IdentTC) b₁ b₂ () b₄ m f g
      lawAssoc (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ S₁)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₁ (inj₂ M₁) (inj₂ N₁) idTC idTC idTC (inj₂ S₁) b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₂ (inj₁ S₁)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₁ (inj₂ M₁) (inj₂ N₁) idTC (inj₂ R₁) idTC (inj₂ S₁) b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₂ (inj₁ S₁)) b₁ b₂ () b₄ m f g
      lawAssoc (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) R (inj₁ IdentTC) (inj₂ (inj₂ S₂)) b₁ b₂ b₃ () m f g
      lawAssoc (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₁ (inj₂ M₁) (inj₂ N₁) idTC idTC (inj₂ T₁) idTC b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₂ (inj₁ T₁)) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₁ (inj₂ M₁) (inj₂ N₁) idTC (inj₂ R₁) (inj₂ T₁) idTC b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₂ (inj₁ T₁)) (inj₁ IdentTC) b₁ () () b₄ m f g
      lawAssoc (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₂ (inj₁ S₁)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₁ (inj₂ M₁) (inj₂ N₁) idTC idTC (inj₂ T₁) (inj₂ S₁) b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₂ (inj₁ T₁)) (inj₂ (inj₁ S₁)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₁ (inj₂ M₁) (inj₂ N₁) idTC (inj₂ R₁) (inj₂ T₁) (inj₂ S₁) b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₂ (inj₁ T₁)) (inj₂ (inj₁ S₁)) b₁ () () b₄ m f g
      lawAssoc (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) R (inj₂ (inj₁ T₁)) (inj₂ (inj₂ S₂)) b₁ b₂ b₃ () m f g
      lawAssoc (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) R (inj₂ (inj₂ T₂)) (inj₁ IdentTC) b₁ b₂ b₃ () m f g
      lawAssoc (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) R (inj₂ (inj₂ T₂)) (inj₂ (inj₁ S₁)) b₁ b₂ b₃ () m f g
      lawAssoc (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) R (inj₂ (inj₂ T₂)) (inj₂ (inj₂ S₂)) b₁ b₂ b₃ () m f g
      lawAssoc (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ P₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₁ (inj₂ M₁) (inj₂ N₁) (inj₂ P₁) idTC idTC idTC b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ P₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ S₁)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₁ (inj₂ M₁) (inj₂ N₁) (inj₂ P₁) idTC idTC (inj₂ S₁) b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ P₁)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ S₂)) b₁ b₂ () () m f g
      lawAssoc (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ P₁)) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₁ (inj₂ M₁) (inj₂ N₁) (inj₂ P₁) idTC (inj₂ T₁) idTC b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ P₁)) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₂ (inj₁ S₁)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₁ (inj₂ M₁) (inj₂ N₁) (inj₂ P₁) idTC (inj₂ T₁) (inj₂ S₁) b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ P₁)) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) (inj₂ (inj₂ S₂)) b₁ b₂ () () m f g
      lawAssoc (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ P₁)) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) S b₁ () b₃ b₄ m f g
      lawAssoc (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ P₁)) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₁ (inj₂ M₁) (inj₂ N₁) (inj₂ P₁) (inj₂ R₁) idTC idTC b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ P₁)) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₂ (inj₁ S₁)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₁ (inj₂ M₁) (inj₂ N₁) (inj₂ P₁) (inj₂ R₁) idTC (inj₂ S₁) b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ P₁)) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₂ (inj₂ S₂)) b₁ b₂ () () m f g
      lawAssoc (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ P₁)) (inj₂ (inj₁ R₁)) (inj₂ (inj₁ T₁)) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₁ (inj₂ M₁) (inj₂ N₁) (inj₂ P₁) (inj₂ R₁) (inj₂ T₁) idTC b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ P₁)) (inj₂ (inj₁ R₁)) (inj₂ (inj₁ T₁)) (inj₂ (inj₁ S₁)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₁ (inj₂ M₁) (inj₂ N₁) (inj₂ P₁) (inj₂ R₁) (inj₂ T₁) (inj₂ S₁) b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ P₁)) (inj₂ (inj₁ R₁)) (inj₂ (inj₁ T₁)) (inj₂ (inj₂ S₂)) b₁ b₂ () () m f g
      lawAssoc (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ P₁)) (inj₂ (inj₁ R₁)) (inj₂ (inj₂ T₂)) S b₁ () b₃ b₄ m f g
      lawAssoc (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ P₁)) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) S b₁ () b₃ b₄ m f g
      lawAssoc (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ P₁)) (inj₂ (inj₂ R₂)) (inj₂ (inj₁ T₁)) S b₁ () b₃ b₄ m f g
      lawAssoc (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ P₁)) (inj₂ (inj₂ R₂)) (inj₂ (inj₂ T₂)) S b₁ () b₃ b₄ m f g
      lawAssoc (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) (inj₂ (inj₂ P₂)) R T S () b₂ b₃ b₄ m f g
      lawAssoc (inj₂ (inj₁ M₁)) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) R T S () b₂ b₃ b₄ m f g
      lawAssoc (inj₂ (inj₁ M₁)) (inj₂ (inj₂ N₂)) (inj₂ (inj₁ P₁)) R T S () b₂ b₃ b₄ m f g
      lawAssoc (inj₂ (inj₁ M₁)) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) R T S () b₂ b₃ b₄ m f g
      lawAssoc (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₂ (inj₂ M₂) idTC idTC idTC idTC idTC b₁ b₂ b₃ b₄ refl eqIdBind eqIdBind refl m f g refl (lawAssocHelp2 b₂ g) (lawAssocHelp3 b₃ f g) (λ x → refl)
      lawAssoc (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g with idMorph¬∃₂ (inj₁ (M₂ , refl)) b₁
      lawAssoc (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g | ()
      lawAssoc (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₂ (inj₂ M₂) idTC idTC (inj₂ R₂) idTC idTC b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₁ IdentTC) R (inj₁ IdentTC) (inj₂ (inj₁ S₁)) b₁ b₂ b₃ () m f g
      lawAssoc (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ S₂)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₂ (inj₂ M₂) idTC idTC idTC idTC (inj₂ S₂) b₁ b₂ b₃ b₄ refl eqIdBind refl refl m f g refl (lawAssocHelp2 b₂ g) refl (λ x → refl)
      lawAssoc (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₂ (inj₂ S₂)) b₁ b₂ () b₄ m f g
      lawAssoc (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₂ (inj₂ S₂)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₂ (inj₂ M₂) idTC idTC (inj₂ R₂) idTC (inj₂ S₂) b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₁ IdentTC) R (inj₂ (inj₁ T₁)) (inj₁ IdentTC) b₁ b₂ b₃ () m f g
      lawAssoc (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₁ IdentTC) R (inj₂ (inj₁ T₁)) (inj₂ (inj₁ S₁)) b₁ b₂ b₃ () m f g
      lawAssoc (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₁ IdentTC) R (inj₂ (inj₁ T₁)) (inj₂ (inj₂ S₂)) b₁ b₂ b₃ () m f g
      lawAssoc (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₂ (inj₂ M₂) idTC idTC idTC (inj₂ T₂) idTC b₁ b₂ b₃ b₄ refl refl eqIdBind refl m f g refl (λ x → refl) (lawAssocHelp3 b₃ f g) (λ x → refl)
      lawAssoc (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₂ (inj₂ T₂)) (inj₁ IdentTC) b₁ () b₃ b₄ m f g
      lawAssoc (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₂ (inj₂ T₂)) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₂ (inj₂ M₂) idTC idTC (inj₂ R₂) (inj₂ T₂) idTC b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₁ IdentTC) R (inj₂ (inj₂ T₂)) (inj₂ (inj₁ S₁)) b₁ b₂ b₃ () m f g
      lawAssoc (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₂ (inj₂ S₂)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₂ (inj₂ M₂) idTC idTC idTC (inj₂ T₂) (inj₂ S₂) b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₂ (inj₂ T₂)) (inj₂ (inj₂ S₂)) b₁ () () b₄ m f g
      lawAssoc (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₂ (inj₂ T₂)) (inj₂ (inj₂ S₂)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₂ (inj₂ M₂) idTC idTC (inj₂ R₂) (inj₂ T₂) (inj₂ S₂) b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₂ (inj₁ P₁)) R T S () b₂ b₃ b₄ m f g
      lawAssoc (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₂ (inj₂ M₂) idTC (inj₂ P₂) idTC idTC idTC b₁ b₂ b₃ b₄ refl refl eqIdBind refl m f g refl (λ x → refl) (lawAssocHelp3 b₃ f g) (λ x → refl)
      lawAssoc (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ S₁)) b₁ b₂ b₃ () m f g
      lawAssoc (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ S₂)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₂ (inj₂ M₂) idTC (inj₂ P₂) idTC idTC (inj₂ S₂) b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) S b₁ () b₃ b₄ m f g
      lawAssoc (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₂ (inj₂ M₂) idTC (inj₂ P₂) idTC (inj₂ T₂) idTC b₁ b₂ b₃ b₄ refl refl eqIdBind refl m f g refl (λ x → refl) (lawAssocHelp3 b₃ f g) (λ x → refl)
      lawAssoc (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₂ (inj₁ S₁)) b₁ b₂ b₃ () m f g
      lawAssoc (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₂ (inj₂ S₂)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₂ (inj₂ M₂) idTC (inj₂ P₂) idTC (inj₂ T₂) (inj₂ S₂) b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) S b₁ () b₃ b₄ m f g
      lawAssoc (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) (inj₂ (inj₁ R₁)) (inj₂ (inj₁ T₁)) S b₁ () b₃ b₄ m f g
      lawAssoc (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) (inj₂ (inj₁ R₁)) (inj₂ (inj₂ T₂)) S b₁ () b₃ b₄ m f g
      lawAssoc (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₂ (inj₂ M₂) idTC (inj₂ P₂) (inj₂ R₂) idTC idTC b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₂ (inj₁ S₁)) b₁ b₂ () () m f g
      lawAssoc (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₂ (inj₂ S₂)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₂ (inj₂ M₂) idTC (inj₂ P₂) (inj₂ R₂) idTC (inj₂ S₂) b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) (inj₂ (inj₂ R₂)) (inj₂ (inj₁ T₁)) S b₁ () b₃ b₄ m f g
      lawAssoc (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) (inj₂ (inj₂ R₂)) (inj₂ (inj₂ T₂)) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₂ (inj₂ M₂) idTC (inj₂ P₂) (inj₂ R₂) (inj₂ T₂) idTC b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) (inj₂ (inj₂ R₂)) (inj₂ (inj₂ T₂)) (inj₂ (inj₁ S₁)) b₁ b₂ () () m f g
      lawAssoc (inj₂ (inj₂ M₂)) (inj₁ IdentTC) (inj₂ (inj₂ P₂)) (inj₂ (inj₂ R₂)) (inj₂ (inj₂ T₂)) (inj₂ (inj₂ S₂)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₂ (inj₂ M₂) idTC (inj₂ P₂) (inj₂ R₂) (inj₂ T₂) (inj₂ S₂) b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₂ (inj₂ M₂)) (inj₂ (inj₁ N₁)) (inj₁ IdentTC) R T S () b₂ b₃ b₄ m f g
      lawAssoc (inj₂ (inj₂ M₂)) (inj₂ (inj₁ N₁)) (inj₂ (inj₁ P₁)) R T S () b₂ b₃ b₄ m f g
      lawAssoc (inj₂ (inj₂ M₂)) (inj₂ (inj₁ N₁)) (inj₂ (inj₂ P₂)) R T S () b₂ b₃ b₄ m f g
      lawAssoc (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₂ (inj₂ M₂) (inj₂ N₂) idTC idTC idTC idTC b₁ b₂ b₃ b₄ refl eqIdBind refl refl m f g refl (lawAssocHelp2 b₂ g) refl (λ x → refl)
      lawAssoc (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₁ IdentTC) b₁ b₂ () b₄ m f g
      lawAssoc (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₂ (inj₂ M₂) (inj₂ N₂) idTC (inj₂ R₂) idTC idTC b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) R (inj₁ IdentTC) (inj₂ (inj₁ S₁)) b₁ b₂ b₃ () m f g
      lawAssoc (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ S₂)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₂ (inj₂ M₂) (inj₂ N₂) idTC idTC idTC (inj₂ S₂) b₁ b₂ b₃ b₄ refl eqIdBind refl refl m f g refl (lawAssocHelp2 b₂ g) refl (λ x → refl)
      lawAssoc (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) (inj₂ (inj₂ S₂)) b₁ b₂ () b₄ m f g
      lawAssoc (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₂ (inj₂ S₂)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₂ (inj₂ M₂) (inj₂ N₂) idTC (inj₂ R₂) idTC (inj₂ S₂) b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) R (inj₂ (inj₁ T₁)) (inj₁ IdentTC) b₁ b₂ b₃ () m f g
      lawAssoc (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) R (inj₂ (inj₁ T₁)) (inj₂ (inj₁ S₁)) b₁ b₂ b₃ () m f g
      lawAssoc (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) R (inj₂ (inj₁ T₁)) (inj₂ (inj₂ S₂)) b₁ b₂ b₃ () m f g
      lawAssoc (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₂ (inj₂ M₂) (inj₂ N₂) idTC idTC (inj₂ T₂) idTC b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₂ (inj₂ T₂)) (inj₁ IdentTC) b₁ () () b₄ m f g
      lawAssoc (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₂ (inj₂ T₂)) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₂ (inj₂ M₂) (inj₂ N₂) idTC (inj₂ R₂) (inj₂ T₂) idTC b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) R (inj₂ (inj₂ T₂)) (inj₂ (inj₁ S₁)) b₁ b₂ b₃ () m f g
      lawAssoc (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₂ (inj₂ S₂)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₂ (inj₂ M₂) (inj₂ N₂) idTC idTC (inj₂ T₂) (inj₂ S₂) b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₂ (inj₁ R₁)) (inj₂ (inj₂ T₂)) (inj₂ (inj₂ S₂)) b₁ () () b₄ m f g
      lawAssoc (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₁ IdentTC) (inj₂ (inj₂ R₂)) (inj₂ (inj₂ T₂)) (inj₂ (inj₂ S₂)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₂ (inj₂ M₂) (inj₂ N₂) idTC (inj₂ R₂) (inj₂ T₂) (inj₂ S₂) b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₂ (inj₁ P₁)) R T S () b₂ b₃ b₄ m f g
      lawAssoc (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₂ (inj₂ M₂) (inj₂ N₂) (inj₂ P₂) idTC idTC idTC b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ S₁)) b₁ b₂ () () m f g
      lawAssoc (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ S₂)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₂ (inj₂ M₂) (inj₂ N₂) (inj₂ P₂) idTC idTC (inj₂ S₂) b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₁ IdentTC) (inj₂ (inj₁ T₁)) S b₁ () b₃ b₄ m f g
      lawAssoc (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₂ (inj₂ M₂) (inj₂ N₂) (inj₂ P₂) idTC (inj₂ T₂) idTC b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₂ (inj₁ S₁)) b₁ b₂ () () m f g
      lawAssoc (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₁ IdentTC) (inj₂ (inj₂ T₂)) (inj₂ (inj₂ S₂)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₂ (inj₂ M₂) (inj₂ N₂) (inj₂ P₂) idTC (inj₂ T₂) (inj₂ S₂) b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₂ (inj₁ R₁)) (inj₁ IdentTC) S b₁ () b₃ b₄ m f g
      lawAssoc (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₂ (inj₁ R₁)) (inj₂ (inj₁ T₁)) S b₁ () b₃ b₄ m f g
      lawAssoc (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₂ (inj₁ R₁)) (inj₂ (inj₂ T₂)) S b₁ () b₃ b₄ m f g
      lawAssoc (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₂ (inj₂ M₂) (inj₂ N₂) (inj₂ P₂) (inj₂ R₂) idTC idTC b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₂ (inj₁ S₁)) b₁ b₂ () () m f g
      lawAssoc (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₂ (inj₂ R₂)) (inj₁ IdentTC) (inj₂ (inj₂ S₂)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₂ (inj₂ M₂) (inj₂ N₂) (inj₂ P₂) (inj₂ R₂) idTC (inj₂ S₂) b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₂ (inj₂ R₂)) (inj₂ (inj₁ T₁)) S b₁ () b₃ b₄ m f g
      lawAssoc (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₂ (inj₂ R₂)) (inj₂ (inj₂ T₂)) (inj₁ IdentTC) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₂ (inj₂ M₂) (inj₂ N₂) (inj₂ P₂) (inj₂ R₂) (inj₂ T₂) idTC b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)
      lawAssoc (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₂ (inj₂ R₂)) (inj₂ (inj₂ T₂)) (inj₂ (inj₁ S₁)) b₁ b₂ () () m f g
      lawAssoc (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) (inj₂ (inj₂ P₂)) (inj₂ (inj₂ R₂)) (inj₂ (inj₂ T₂)) (inj₂ (inj₂ S₂)) b₁ b₂ b₃ b₄ m f g = 
        lawAssocProof₂ (inj₂ M₂) (inj₂ N₂) (inj₂ P₂) (inj₂ R₂) (inj₂ T₂) (inj₂ S₂) b₁ b₂ b₃ b₄ refl refl refl refl m f g refl (λ x → refl) refl (λ x → refl)


