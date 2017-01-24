
module Supermonad.DefinitionWithCategory where

-- Stdlib
open import Level
open import Function hiding ( _∘_ ; id )
open import Agda.Primitive
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Data.Nat hiding ( _⊔_ )
open import Data.Vec
open import Data.List hiding ( sequence )
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning


open import Haskell
open import Theory.Category
open import Supermonad.Definition

{-
-- Play around with other alternate formulations.

toLevel : ℕ → Level
toLevel zero = lzero
toLevel (suc n) = lsuc (toLevel n)


Kind : Set (toLevel 3)
Kind = Set (toLevel 2)

Type : Kind
Type = Set (toLevel 1)


data Maybe (A : Type) : Type where
  Just : (a : A) → Maybe A
  Nothing : Maybe A

data Nat : Type where
  Succ : Nat → Nat
  Zero : Nat

data IxList {ℓ : Level} : List (Set ℓ) → Set (lsuc ℓ) where
  Cons : ∀ {T Ts} → (a : T) → IxList Ts → IxList (T ∷ Ts)
  Nil : IxList []

record SupermonadI {ℓ : Level} (ts : List (Set ℓ)) (M : IxList ts → Set ℓ → Set ℓ) : Set (lsuc ℓ) where
  field
    _◆_ : IxList ts → IxList ts → IxList ts

    ValidBindIxs : IxList ts → IxList ts → Set
    ValidReturnIxs : IxList ts → Set
    
    bind : ∀ {α β : Set ℓ} {is js : IxList ts} → (M is α → (α → M js β) → M (is ◆ js) β) 
    
    return : ∀ {α : Set ℓ} {is : IxList ts} → (α → M is α)

    lawReturnIxsL : {is js : IxList ts} 
                  → ValidReturnIxs is → ValidBindIxs is js 
                  → is ◆ js ≡ js
    
    lawReturnIxsR : {is js : IxList ts} 
                  → ValidReturnIxs js → ValidBindIxs is js
                  → is ◆ js ≡ is
    
    lawAssocIxs : {is js ks : IxList ts} 
                → ValidBindIxs is js → ValidBindIxs js ks
                → ValidBindIxs is (js ◆ ks) → ValidBindIxs (is ◆ js) ks
                → is ◆ (js ◆ ks) ≡ (is ◆ js) ◆ ks
    
    -- The supermonad version of the right identity law.
    lawIdR : {α β : Set ℓ} 
           → {is js : IxList ts}
           → (vr : ValidReturnIxs is) → (vb : ValidBindIxs is js)
           → (a : α) → (k : α → M js β)
           → subst (λ X → M X β) (lawReturnIxsL {is} {js} vr vb) (bind (return a) k) ≡ k a
    
    -- The supermonad version of the left identity law.
    lawIdL : {α : Set ℓ} 
           → {is js : IxList ts}
           → (vr : ValidReturnIxs js) → (vb : ValidBindIxs is js)
           → (m : M is α)
           → subst (λ X → M X α) (lawReturnIxsR {is} {js} vr vb) (bind m return) ≡ m
    
    -- The supermonad version of the associativity law.
    lawAssoc : {α β γ : Set ℓ}
             → {is js ks : IxList ts}
             → (vb₁ : ValidBindIxs is js) → (vb₂ : ValidBindIxs js ks)
             → (vb₃ : ValidBindIxs is (js ◆ ks)) → (vb₄ : ValidBindIxs (is ◆ js) ks)
             → (m : M is α) → (f : α → M js β) → (g : β → M ks γ)
             → subst (λ X → M X γ) (lawAssocIxs {is} {js} {ks} vb₁ vb₂ vb₃ vb₄) (bind m (λ x → bind (f x) g)) ≡ bind (bind m f) g
    
  sequence : {α β : Set ℓ} 
           → {is js : IxList ts}
           → M is α → M js β → M (is ◆ js) β
  sequence ma mb = bind ma (λ _ → mb)

-}

-- -----------------------------------------------------------------------------
-- Definition of a monad extended with a category to repredent an alternative 
-- formalization of supermonads.
-- -----------------------------------------------------------------------------

{-
record Category {ℓ₀ ℓ₁ : Level} (Obj : Set ℓ₀) (Hom : Obj → Obj → Set ℓ₁) : Set (lsuc (ℓ₀ ⊔ ℓ₁)) where
  field
    _∘_ : ∀ {a b c} → Hom b c → Hom a b → Hom a c
    id : ∀ {a} → Hom a a
    
    assoc : {a b c d : Obj} {f : Hom a b} {g : Hom b c} {h : Hom c d} 
          → h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f
    idR : {a b : Obj} {f : Hom a b} → id ∘ f ≡ f
    idL : {a b : Obj} {f : Hom a b} → f ∘ id ≡ f
-}

open Category renaming ( idL to catIdL ; idR to catIdR ; assoc to catAssoc )

record SupermonadC {ℓ ℓ₀ ℓ₁ : Level} (C : Category {ℓ₀} {ℓ₁}) (M : ∀ {a b} → Hom C a b → Set ℓ → Set ℓ) : Set (ℓ₀ ⊔ ℓ₁ ⊔ lsuc ℓ) where
  _◆_ = Category._∘_ C
  field
    bind : ∀ {α β : Set ℓ} {a b c : Obj C} {i : Hom C a b} {j : Hom C b c} → (M j α → (α → M i β) → M (j ◆ i) β) 
    
    return : ∀ {α : Set ℓ} {a : Obj C} {i : Hom C a a} → (α → M i α)

    -- The supermonad version of the right identity law.
    idR : {α β : Set ℓ} {a b : Obj C}
           → {i : Hom C a a} {j : Hom C a b}
           → (a : α) → (k : α → M j β)
           → subst (λ X → M X β) (catIdR C) (bind (return a) k) ≡ k a
    
    -- The supermonad version of the left identity law.
    idL : {α : Set ℓ} {a b : Obj C}
           → {i : Hom C a b} {j : Hom C b b}
           → (m : M i α)
           → subst (λ X → M X α) (catIdL C) (bind m return) ≡ m
    
    -- The supermonad version of the associativity law.
    assoc : {α β γ : Set ℓ} {a b c d : Obj C}
             → {i : Hom C a b} {j : Hom C b c} {k : Hom C c d}
             → (m : M k α) → (f : α → M j β) → (g : β → M i γ)
             → subst (λ X → M X γ) (catAssoc C) (bind m (λ x → bind (f x) g)) ≡ bind (bind m f) g
    
  sequence : {α β : Set ℓ} {a b c : Obj C}
           → {i : Hom C a b} {j : Hom C b c}
           → M j α → M i β → M (j ◆ i) β
  sequence ma mb = bind ma (λ _ → mb)

DecidableEquality : ∀ {ℓ} → (A : Set ℓ) → Set ℓ
DecidableEquality A = (a : A) → (b : A) → Dec (a ≡ b)

UniqueHomomorphisms : ∀ {ℓ₀ ℓ₁} → (C : Category {ℓ₀} {ℓ₁}) → Set (ℓ₁ ⊔ ℓ₀)
UniqueHomomorphisms C = ∀ {a b} → (f : Hom C a b) → (g : Hom C a b) → f ≡ g

SupermonadC→Supermonad : {ℓ₀ ℓ₁ : Level} {C : Category {ℓ₀} {ℓ₁}} {F : ∀ {a b} → Hom C a b → TyCon}
                       → DecidableEquality (Obj C)
                       → UniqueHomomorphisms C
                       → SupermonadC C F → Supermonad (∃ λ a → ∃ λ b → Hom C a b)
SupermonadC→Supermonad {ℓ₀} {ℓ₁} {C = C} {F = F} _≡Obj_ uniqueHom smc = record
  { ⟨_⟩ = ⟨_⟩
  ; Binds = Binds
  ; Returns = Returns
  ; functor = {!!}
  ; tyConArity = 1
  ; tyConArgTys = HomIx ∷ []
  ; tyCon = tyCon
  ; bind = bind
  ; return = return
  ; lawSingleTyCon = lawSingleTyCon
  ; lawUniqueBind = λ {α} {β} → lawUniqueBind {α} {β}
  ; lawUniqueReturn = λ {α} {M} → lawUniqueReturn {α} {M}
  ; lawIdR = {!!}
  ; lawIdL = {!!}
  ; lawAssoc = {!!}
  ; lawMonadFmap = {!!}
  }
  where
    _◆_ = _∘_ C
    
    HomIx : Set (ℓ₁ ⊔ ℓ₀)
    HomIx = ∃ λ a → ∃ λ b → Hom C a b
    
    ⟨_⟩ : HomIx → TyCon
    ⟨_⟩ (a , b , f) = F f

    tyCon : HomIx → Lift {ℓ = lsuc (ℓ₀ ⊔ ℓ₁)} TyCon
    tyCon (a , b , f) = lift (F f)
    
    Binds : HomIx → HomIx → HomIx → Type → Type → Set (ℓ₁ ⊔ ℓ₀)
    Binds (b , c , f) (a , b' , g) (a' , c' , h) α β = Lift {ℓ = ℓ₁} $ ∃ λ (eqA : a' ≡ a) → ∃ λ (eqB : b' ≡ b) → ∃ λ (eqC : c' ≡ c) → (f ◆ (subst (Hom C a) eqB g) ≡ (subst₂ (Hom C) eqA eqC h) )
    
    Returns : HomIx → Type → Set (ℓ₁ ⊔ ℓ₀)
    Returns (a , a' , f) α = Lift {ℓ = ℓ₁} (a ≡ a')
    
    bind : {α β : Type} {M N P : HomIx} → Binds M N P α β 
         → ⟨ M ⟩ α → (α → ⟨ N ⟩ β) → ⟨ P ⟩ β
    bind {M = a , b , f} {c , .a , g} {.c , .b , .(f ◆ g)} (lift (refl , refl , refl , refl)) = SupermonadC.bind smc
    
    return : {α : Type} {M : HomIx} → Returns M α 
           → α → ⟨ M ⟩ α
    return {M = a , .a , f} (lift refl) = SupermonadC.return smc
    
    lawSingleTyCon : (M : HomIx) → ∃ (λ i → Lift {ℓ = lsuc (ℓ₀ ⊔ ℓ₁)} (⟨ M ⟩ ≡ lower (tyCon i)))
    lawSingleTyCon (a , b , f) = (a , b , f) , (lift refl)
    
    lawUniqueBind : {α β : Type} {M N P : HomIx} 
                  → (b₁ b₂ : Binds M N P α β) → b₁ ≡ b₂
    lawUniqueBind (lift (refl , refl , refl , refl)) (lift (refl , refl , refl , refl)) = refl
    
    lawUniqueReturn : {α : Type} {M : HomIx}
                    → (r₁ r₂ : Returns M α) → r₁ ≡ r₂
    lawUniqueReturn (lift refl) (lift refl) = refl
    
    lawIdR : {α β : Type} → (M N : HomIx) → (b : Binds M N N α β) → (r : Returns M α) 
           → (a : α) (k : α → ⟨ N ⟩ β) → bind b (return r a) k ≡ k a
    lawIdR (a , .a , f) (b , .a , g) (lift (refl , refl , refl , f◆g≡g)) (lift refl) x k with uniqueHom f (id C {a})
    lawIdR (a , .a , .(id C {a})) (b , .a , g) (lift (refl , refl , refl , f◆g≡g)) (lift refl) x k | refl = {!!}
