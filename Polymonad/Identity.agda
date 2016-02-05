 
module Polymonad.Identity where

-- Stdlib
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Local
open import Utilities
open import Haskell
open import Identity
open import Monad.Identity
open import Monad.Polymonad
open import Monad.Principal
open import Polymonad
open import Polymonad.Principal
open import Polymonad.Unionable

-- -----------------------------------------------------------------------------
-- Custom Identity Polymonad
-- -----------------------------------------------------------------------------

-- Polymonad instance for the pure identity polymonad.
polymonadId : Polymonad (IdTyCons ⊎ ⊥) idTC
polymonadId = record 
  { B[_,_]▷_ = id[_,_]▷_
  ; ⟨_⟩ = id⟨_⟩
  ; bind = λ {M} {N} {P} → bind {M} {N} {P}
  ; lawId = refl    
  ; lawFunctor1 = lawFunctor1
  ; lawFunctor2 = lawFunctor2
  ; lawMorph1 = lawMorph1
  ; lawMorph2 = lawMorph2
  ; lawMorph3 = lawMorph3
  ; lawDiamond1 = lawDiamond1 
  ; lawDiamond2 = lawDiamond2
  ; lawAssoc = lawAssoc
  ; lawClosure = lawClosure 
  } where
      TyCons = IdTyCons ⊎ ⊥
      
      Id : TyCons
      Id = idTC
      
      id⟨_⟩ : TyCons → TyCon
      id⟨_⟩ (inj₁ IdentTC) = Identity
      id⟨_⟩ (inj₂ ())
      
      id[_,_]▷_ : (M N P : TyCons) → Set
      id[ inj₁ IdentTC , inj₁ IdentTC ]▷ inj₁ IdentTC = IdBinds
      id[ inj₁ IdentTC , inj₁ IdentTC ]▷ inj₂ ()
      id[ inj₁ IdentTC , inj₂ () ]▷ P
      id[ inj₂ () , N ]▷ P

      bind : {M N P : TyCons} → id[ M , N ]▷ P → [ id⟨ M ⟩ , id⟨ N ⟩ ]▷ id⟨ P ⟩
      bind {inj₁ IdentTC} {inj₁ IdentTC} {inj₁ IdentTC} IdB = bindId
      bind {inj₁ IdentTC} {inj₁ IdentTC} {inj₂ ()}
      bind {inj₁ IdentTC} {inj₂ ()}
      bind {inj₂ ()}
      
      lawFunctor1 : ∀ (M : TyCons) → id[ M , Id ]▷ M
      lawFunctor1 (inj₁ IdentTC) = IdentB
      lawFunctor1 (inj₂ ())

      lawFunctor2 : ∀ (M : TyCons) → (b : id[ M , Id ]▷ M) 
                 → ∀ {a : Type} (m : id⟨ M ⟩ a) → (bind {M} {Id} {M} b) m identity ≡ m
      lawFunctor2 (inj₁ IdentTC) IdentB m = refl
      lawFunctor2 (inj₂ ())
      
      lawMorph1 : ∀ (M N : TyCons) 
                → (id[ M , Id ]▷ N → id[ Id , M ]▷ N)
      lawMorph1 (inj₁ IdentTC) (inj₁ IdentTC) IdB = IdB
      lawMorph1 (inj₁ IdentTC) (inj₂ ())
      lawMorph1 (inj₂ ()) N

      lawMorph2 : ∀ (M N : TyCons) 
                → (id[ Id , M ]▷ N → id[ M , Id ]▷ N)
      lawMorph2 (inj₁ IdentTC) (inj₁ IdentTC) t = t
      lawMorph2 (inj₁ IdentTC) (inj₂ ())
      lawMorph2 (inj₂ ()) N
      
      p : id[ inj₁ IdentTC , inj₁ IdentTC ]▷  inj₁ IdentTC ≡ IdBinds
      p = refl

      q : ∀ {A B : Set} {b : IdTyCons} {x : A} {f : A → B}
        → bind {M = inj₁ IdentTC} {N = inj₁ IdentTC} {P = inj₁ IdentTC} IdentB x f ≡ (bind {M = Id} {N = Id} {P = Id} IdentB) x f
      q {b = IdentTC} = refl
      
      lawMorph3 : ∀ (M N : TyCons) (b₁ : id[ M , Id ]▷ N) (b₂ : id[ Id , M ]▷ N)
                → ∀ {a b : Type} (v : a) (f : a → id⟨ M ⟩ b) 
                → (bind b₁) (f v) identity ≡ (bind b₂) (identity v) f
      lawMorph3 (inj₁ IdentTC) (inj₁ IdentTC) IdentB IdentB v f = refl 
      lawMorph3 (inj₁ IdentTC) (inj₂ ())
      lawMorph3 (inj₂ ()) N

      lawDiamond1 : ∀ (M N R T : TyCons)
                  → (∃ λ(P : TyCons) → id[ M , N ]▷ P × id[ P , R ]▷ T)
                  → (∃ λ(S : TyCons) → id[ N , R ]▷ S × id[ M , S ]▷ T)
      lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC , b₁ , b₂) = Id , IdentB , IdentB
      lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ () , b₁ , b₂)
      lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ ())
      lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ ()) T
      lawDiamond1 (inj₁ IdentTC) (inj₂ ()) R T
      lawDiamond1 (inj₂ ()) N R T

      lawDiamond2 : ∀ (M N R T : TyCons)
                  → (∃ λ(S : TyCons) → id[ N , R ]▷ S × id[ M , S ]▷ T)
                  → (∃ λ(P : TyCons) → id[ M , N ]▷ P × id[ P , R ]▷ T)
      lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC , b₁ , b₂) = Id , IdentB , IdentB
      lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ () , b₁ , b₂)
      lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ ())
      lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ ()) T
      lawDiamond2 (inj₁ IdentTC) (inj₂ ()) R T
      lawDiamond2 (inj₂ ()) N R T
    
      lawAssoc : ∀ (M N P R T S : TyCons) 
                 (b₁ : id[ M , N ]▷ P) (b₂ : id[ P , R ]▷ T) 
                 (b₃ : id[ N , R ]▷ S) (b₄ : id[ M , S ]▷ T)
               → ∀ {a b c : Type} (m : id⟨ M ⟩ a) (f : a → id⟨ N ⟩ b) (g : b → id⟨ R ⟩ c)
               → (bind b₂) ((bind b₁) m f) g ≡ (bind b₄) m (λ x → (bind b₃) (f x) g)
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) IdentB IdentB IdentB IdentB m f g = refl
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ ())
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ ()) S
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ ()) T S
      lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ ()) R T S
      lawAssoc (inj₁ IdentTC) (inj₂ ()) P R T S
      lawAssoc (inj₂ ()) N P R T S
      
      lawClosure : ∀ (M N P S T U : TyCons)
                 → ( id[ M , N  ]▷ P × id[ S , Id ]▷ M × id[ T , Id ]▷ N × id[ P , Id ]▷ U )
                 → id[ S , T ]▷ U
      lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (IdentB , IdentB , IdentB , IdentB) = IdentB
      lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ ())
      lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ ()) U
      lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ ()) T U
      lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ ()) S T U
      lawClosure (inj₁ IdentTC) (inj₂ ()) P S T U
      lawClosure (inj₂ ()) N P S T U

pmId≡identity : ∀ {τ : Type} {x : τ} → id {τ} (pmLawId polymonadId) ≡ identity {τ}
pmId≡identity {τ} {x} = refl

principalPolymonadId : PrincipalPM polymonadId
principalPolymonadId F (M , M' , MM'∈F) (inj₁ IdentTC) (inj₁ IdentTC) morph₁ morph₂ = (inj₁ IdentTC) , IdentB , IdentB , morph₁
principalPolymonadId F (M , M' , MM'∈F) (inj₁ IdentTC) (inj₂ ()) morph₁ morph₂
principalPolymonadId F (M , M' , MM'∈F) (inj₂ ()) M₂ morph₁ morph₂

unionablePolymonadId : UnionablePolymonad polymonadId
unionablePolymonadId = record 
  { lawEqBindId = lawEqBindId
  ; lawEqIdBinds = lawEqIdBinds
  ; idMorph¬∃ = idMorph¬∃
  } 
  where
    lawEqBindId : ∀ {α β : Type} → (b : B[ idTC , idTC ] polymonadId ▷ idTC) 
                → substBind {P₂ = Identity} refl refl refl (pmBind polymonadId b) ≡ bindId {α} {β}
    lawEqBindId IdentB = refl
    
    lawEqIdBinds : B[ idTC , idTC ] polymonadId ▷ idTC ≡ IdBinds
    lawEqIdBinds = refl
    
    idMorph¬∃ : ∀ {M N : IdTyCons ⊎ ⊥} → (∃ λ(M' : ⊥) → M ≡ inj₂ M') ⊎ (∃ λ(N' : ⊥) → N ≡ inj₂ N') → ¬ (B[ M , N ] polymonadId ▷ idTC)
    idMorph¬∃ (inj₁ (() , refl)) b
    idMorph¬∃ (inj₂ (() , refl)) b

-- -----------------------------------------------------------------------------
-- Monad Identity Polymonad
-- -----------------------------------------------------------------------------

monadPolymonadId : Polymonad (IdTyCons ⊎ MonadTyCons) idTC
monadPolymonadId = Monad→Polymonad monadId

principalMonadPolymonadId : PrincipalPM monadPolymonadId
principalMonadPolymonadId = Monad→PrincipalPolymonad monadId




