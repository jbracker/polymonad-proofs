 
module Theory.Examples.Haskell.FunctorEndomorphisms where

open import Level renaming ( suc to lsuc ; zero to lzero )
open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Data.Unit
open import Data.Product
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Extensionality
open import Congruence
open import ProofIrrelevance
open import Haskell
open import Theory.ConstrainedFunctor

-- The functor of endomorphisms.
data Endo (α : Type) : Type where
  endo : (α → α) → Endo α

-- fmap of the functor of endomorphisms.
endomap : {α : Type} → (α → α) → (Endo α) → (Endo α)
endomap f (endo g) = endo $ f ∘F g

-- The categorical structure of the constrained functor.
FunctorEndomorphisms : ConstrainedFunctor
FunctorEndomorphisms = record
  { ObjCts = ObjCts
  ; HomCts = HomCts
  ; _∘Ct_ = flip trans
  ; idCt = refl
  ; constraint-assoc = λ {α} {β} {γ} {δ} {α'} {β'} {γ'} {δ'} {f} {g} {h} → assoc {f = f} {g} {h}
  ; constraint-right-id = λ {α} {β} {α'} {β'} {f} → right-id {f = f}
  ; constraint-left-id = λ {α} {β} {α'} {β'} {f} → left-id {f = f}
  ; F = F
  ; map = ctMap
  ; functor-id = ctFuncId
  ; functor-compose = λ {α} {β} {γ} {f} {g} → ctFuncComp {α} {β} {γ} {f} {g}
  ; proof-irr-ObjCts = λ {α} → ctObjProofIrr {α}
  ; proof-irr-HomCts = λ {α} {β} {α'} {β'} {f} → ctHomProofIrr {f = f}
  } where
    ObjCts : Type → Set lzero
    ObjCts _ = Lift ⊤
    
    HomCts : {α β : Type} → ObjCts α → ObjCts β → (α → β) → Set (lsuc lzero)
    HomCts = λ {α} {β} _ _ f → α ≡ β

    Obj = Σ Type ObjCts
    
    Hom : Obj → Obj → Set (lsuc lzero)
    Hom (α , αCts) (β , βCts) = Σ (α → β) (HomCts {α} {β} αCts βCts)
    
    assoc : {α β γ δ : Type} 
          → {α' : ObjCts α} {β' : ObjCts β} {γ' : ObjCts γ} {δ' : ObjCts δ}
          → {f : α → β} {g : β → γ} {h : γ → δ}
          → (f' : HomCts α' β' f) (g' : HomCts β' γ' g) (h' : HomCts γ' δ' h) 
          → flip trans h' (flip trans g' f') ≡ flip trans (flip trans h' g') f'
    assoc refl refl refl = refl
    
    right-id : {α β : Type} {α' : ObjCts α} {β' : ObjCts β} {f : α → β}
        → (f' : HomCts α' β' f) → flip trans refl f' ≡ f'
    right-id refl = refl
    
    left-id : {α β : Type} {α' : ObjCts α} {β' : ObjCts β} {f : α → β}
        → (f' : HomCts α' β' f) → flip trans f' refl ≡ f'
    left-id refl = refl
    
    F : Obj → Type
    F (α , _) = Endo α
    
    ctMap : {α β : Obj} → (Hom α β) → F α → F β
    ctMap (f , refl) x = endomap f x
    
    ctFuncId : {α : Obj} → endomap {α = proj₁ α} idF ≡ idF
    ctFuncId {α , lift tt} = fun-ext helper
      where helper : (x : Endo α) → endomap idF x ≡ idF x
            helper (endo f) = refl
    
    ctFuncComp : {α β γ : Obj} {f : Hom α β} {g : Hom β γ}
               → ctMap (proj₁ g ∘F proj₁ f , flip trans (proj₂ g) (proj₂ f)) ≡ ctMap g ∘F ctMap f
    ctFuncComp {α , lift tt} {.α , lift tt} {.α , lift tt} {f , refl} {g , refl} = fun-ext helper
      where helper : (x : Endo α) → endomap (g ∘F f) x ≡ (endomap g ∘F endomap f) x
            helper (endo h) = refl
    
    ctObjProofIrr : {α : Type} (αCts αCts' : ObjCts α) → αCts ≡ αCts'
    ctObjProofIrr (lift tt) (lift tt) = refl
    
    ctHomProofIrr : {α β : Type} {αCts : ObjCts α} {βCts : ObjCts β} {f : α → β}
                  → (fCts fCts' : HomCts αCts βCts f) → fCts ≡ fCts'
    ctHomProofIrr refl refl = refl
