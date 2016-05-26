
module Supermonad.Polymonad where

-- Stdlib
open import Level
open import Function hiding ( id )
open import Agda.Primitive
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Data.Vec
open import Data.Nat
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Local
open import Utilities
open import Haskell
open import Identity
open import Functor
open import Polymonad
open import Constrained.ConstrainedFunctor
open import Parameterized.PhantomIndices
open import Supermonad.Definition
{-
-- -----------------------------------------------------------------------------
-- Supermonads are a certain form of Polymonads
-- -----------------------------------------------------------------------------
-- ∃Indices : ∀ {ℓ} {n} → (ts : Vec (Set ℓ) n) → (M : ParamTyCon ts) → (TyCon → Set (lsuc ℓ)) → Set (lsuc ℓ)
Polymonad→Supermonad 
  : ∀ {ℓ}
  → (TyCons : Set ℓ) → (Id : TyCons)
  → (pm : Polymonad TyCons Id)
  → ( (M : TyCons) → B[ M , Id ] pm ▷ M )
  → ( ∃ λ(n : ℕ) → ∃ λ(ts : Vec (Set ℓ) n) → ∃ λ(K : ParamTyCon ts) → ∀ (M : TyCons) → ∃Indices ts K (λ K' → Lift {ℓ = lsuc ℓ} (K' ≡ ⟨ pm ▷ M ⟩)) )
  → UnconstrainedSupermonad TyCons
Polymonad→Supermonad {ℓ = ℓ} TyCons Id pm ∃FunctorBind (n , ts , K , K≡) = record
  { supermonad = supermonad
  ; lawBindUnconstrained = {!!}
  ; lawReturnUnconstrained = {!!}
  ; lawFunctorUnconstrained = {!!}
  } where
    ⟨_⟩ : TyCons → TyCon
    ⟨ M ⟩ = ⟨ pm ▷ M ⟩
    
    Binds : TyCons → TyCons → TyCons → Type → Type → Set ℓ
    Binds M N P _ _ = B[ M , N ] pm ▷ P
    
    Returns : TyCons → Type → Set ℓ
    Returns M _ = B[ Id , Id ] pm ▷ M
    
    fmap : ∀ {α β} {M : TyCons} → (α → β) → ⟨ M ⟩ α → ⟨ M ⟩ β 
    fmap {M = M} f m = functorB m (λ a → pmIdLift pm (f a))
      where
        functorB = pmBind pm (∃FunctorBind M)

    lawIdFunc : ∀ {α : Type} {M : TyCons} → fmap {α = α} {M = M} identity ≡ identity
    lawIdFunc = {!!}

    lawDistFunc : ∀ {α β γ : Type} {M : TyCons}
                → (f : β → γ) → (g : α → β) 
                → fmap {M = M} (f ∘ g) ≡ fmap f ∘ fmap g
    lawDistFunc f g = {!!}
    
    functor : (M : TyCons) → Functor ⟨ M ⟩
    functor M = record 
      { fmap = fmap
      ; lawId = lawIdFunc
      ; lawDist = lawDistFunc
      }
    
    cfunctor : (M : TyCons) → ConstrainedFunctor ⟨ M ⟩
    cfunctor M = Functor→ConstrainedFunctor (⟨ M ⟩) (functor M)
    
    supermonad : Supermonad TyCons
    supermonad = record
      { ⟨_⟩ = ⟨_⟩
      ; Binds = Binds
      ; Returns = Returns
      ; functor = cfunctor
      ; tyConArity = {!!}
      ; tyConArgTys = {!!}
      ; tyCon = {!!}
      ; bind = {!!}
      ; return = {!!}
      ; lawSingleTyCon = {!!}
      ; lawUniqueBind = {!!}
      ; lawUniqueReturn = {!!}
      ; lawIdR = {!!}
      ; lawIdL = {!!}
      ; lawAssoc = {!!}
      ; lawMonadFmap = {!!}
      }
-}
-- -----------------------------------------------------------------------------
-- Every Supermonad is a Polymonad
-- -----------------------------------------------------------------------------
{-
Supermonad→Polymonad : ∀ {ℓ}
                     → (TyCons : Set ℓ)
                     → (monad : UnconstrainedSupermonad TyCons)
                     → Polymonad (IdTyCons ⊎ TyCons) idTC
Supermonad→Polymonad {ℓ = ℓ} SuperTyCons ucsm = record
  { B[_,_]▷_ = B[_,_]▷_
  ; ⟨_⟩ = ⟨_⟩
  ; bind = {!!} -- λ {M} {N} {P} b → bind M N P b
  ; lawId = {!!} -- lawId
  ; lawFunctor1 = {!!} -- lawFunctor1
  ; lawFunctor2 = {!!} -- lawFunctor2
  ; lawMorph1 = {!!} -- lawMorph1
  ; lawMorph2 = {!!} -- lawMorph2
  ; lawMorph3 = {!!} -- lawMorph3
  ; lawDiamond1 = {!!} -- lawDiamond1
  ; lawDiamond2 = {!!} -- lawDiamond2
  ; lawAssoc = {!!} -- lawAssoc
  ; lawClosure = {!!} -- lawClosure
  } where
    TyCons = IdTyCons ⊎ SuperTyCons
    Id = idTC

    sm = UnconstrainedSupermonad.supermonad ucsm

    Returns : SuperTyCons → Set ℓ
    Returns = proj₁ (UnconstrainedSupermonad.lawReturnUnconstrained ucsm)
    
    Binds : SuperTyCons → SuperTyCons → SuperTyCons → Set ℓ
    Binds = proj₁ (UnconstrainedSupermonad.lawBindUnconstrained ucsm)

    functor : 
    
    B[_,_]▷_ : (M N P : TyCons) → Set ℓ
    B[ inj₁ IdentTC , inj₁ IdentTC ]▷ inj₁ IdentTC = Lift ⊤
    B[ inj₁ IdentTC , inj₁ IdentTC ]▷ inj₂ P       = Returns P
    B[ inj₁ IdentTC , inj₂ N       ]▷ inj₁ IdentTC = Lift ⊥
    B[ inj₁ IdentTC , inj₂ N       ]▷ inj₂ P       = Returns N × Binds N N P
    B[ inj₂ M       , inj₁ IdentTC ]▷ inj₁ IdentTC = Lift ⊥
    B[ inj₂ M       , inj₁ IdentTC ]▷ inj₂ P       = Returns P × Binds M P P
    B[ inj₂ M       , inj₂ N       ]▷ inj₁ IdentTC = Lift ⊥
    B[ inj₂ M       , inj₂ N       ]▷ inj₂ P       = Binds M N P
    
    ⟨_⟩ : TyCons → TyCon
    ⟨_⟩ (inj₁ IdentTC) = Identity
    ⟨_⟩ (inj₂ M) = Supermonad.⟨_⟩ sm M
    
    Returns→SmReturns : ∀ {α} {M : SuperTyCons}
                      → Returns M → Supermonad.Returns sm M α
    Returns→SmReturns {α = α} {M = M} r = subst (λ X → X) (proj₂ (UnconstrainedSupermonad.lawReturnUnconstrained ucsm) α M) r
    
    Binds→SmBinds : ∀ {α β} {M N P : SuperTyCons}
                  → Binds M N P → Supermonad.Binds sm M N P α β
    Binds→SmBinds {α} {β} {M} {N} {P} b = subst (λ X → X) (proj₂ (UnconstrainedSupermonad.lawBindUnconstrained ucsm) α β M N P) b
    
    returnB : {M : SuperTyCons} → Returns M → [ ⟨ idTC ⟩ , ⟨ idTC ⟩ ]▷ ⟨ inj₂ M ⟩
    returnB r m f = Supermonad.return sm (Returns→SmReturns r) (f m)
    
    bindB : {M N P : SuperTyCons} → Binds M N P → [ ⟨ inj₂ M ⟩ , ⟨ inj₂ N ⟩ ]▷ ⟨ inj₂ P ⟩
    bindB b m f = Supermonad.bind sm (Binds→SmBinds b) m f
    
    applyB : {N P : SuperTyCons} → Returns N → Binds N N P → [ ⟨ idTC ⟩ , ⟨ inj₂ N ⟩ ]▷ ⟨ inj₂ P ⟩
    applyB r b m f = bindB b (returnB r m identity) f
    
    functorB : {M P : SuperTyCons} → Returns P → Binds M P P → [ ⟨ inj₂ M ⟩ , ⟨ idTC ⟩ ]▷ ⟨ inj₂ P ⟩
    functorB r b m f = bindB b m (λ a → returnB r a f)
    
    bind : (M N P : TyCons) → B[ M , N ]▷ P → [ ⟨ M ⟩ , ⟨ N ⟩ ]▷ ⟨ P ⟩
    bind (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (lift tt) m f = f m
    bind (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ P) = returnB
    bind (inj₁ IdentTC) (inj₂ N) (inj₁ IdentTC) (lift ())
    bind (inj₁ IdentTC) (inj₂ N) (inj₂ P) (r , b) = applyB r b
    bind (inj₂ M) (inj₁ IdentTC) (inj₁ IdentTC) (lift ())
    bind (inj₂ M) (inj₁ IdentTC) (inj₂ P) (r , b) = functorB r b
    bind (inj₂ M) (inj₂ N) (inj₁ IdentTC) (lift ())
    bind (inj₂ M) (inj₂ N) (inj₂ P) = bindB
    
    lawId : ⟨ Id ⟩ ≡ Identity
    lawId = refl
    
    lawFunctor1 : ∀ (M : TyCons) → B[ M , Id ]▷ M
    lawFunctor1 (inj₁ IdentTC) = lift tt
    lawFunctor1 (inj₂ M) = {!!}

    lawFunctor2 : ∀ (M : TyCons) → ∀ (b : B[ M , Id ]▷ M)
                → ∀ {α : Type} (m : ⟨ M ⟩ α) → (bind M Id M b) m (id lawId) ≡ m
    lawFunctor2 (inj₁ IdentTC) IdentB m = refl
    lawFunctor2 (inj₂ M) (r , b) m = begin
      (bind (inj₂ M) Id (inj₂ M) (r , b)) m (id lawId)
        ≡⟨ refl ⟩
      (functorB r b) m (id lawId)
        ≡⟨ refl ⟩
      Functor.fmap (functor M) (id lawId) m
        ≡⟨ cong (λ X → X m) (Functor.lawId (SuperMonad.functor monad M)) ⟩
      m ∎
-}

{-
    lawMorph1 : ∀ (M N : TyCons) 
              → (B[ M , Id ]▷ N → B[ Id , M ]▷ N)
    lawMorph1 (inj₁ IdentTC) (inj₁ IdentTC) IdentB = IdentB
    lawMorph1 (inj₁ IdentTC) (inj₂ M) b with decR M
    lawMorph1 (inj₁ IdentTC) (inj₂ M) (ReturnB .M r) | yes r' = ReturnB M r
    lawMorph1 (inj₁ IdentTC) (inj₂ M) (lift ()) | no ¬r
    lawMorph1 (inj₂ M) (inj₁ IdentTC) (lift ())
    lawMorph1 (inj₂ M) (inj₂ .M) (FunctorB .M) = ApplyB M
    
    lawMorph2 : ∀ (M N : TyCons) 
              → (B[ Id , M ]▷ N → B[ M , Id ]▷ N)
    lawMorph2 (inj₁ IdentTC) (inj₁ IdentTC) IdentB = IdentB
    lawMorph2 (inj₁ IdentTC) (inj₂ M) b with decR M
    lawMorph2 (inj₁ IdentTC) (inj₂ M) (ReturnB .M r) | yes r' = ReturnB M r
    lawMorph2 (inj₁ IdentTC) (inj₂ M) (lift ()) | no ¬r
    lawMorph2 (inj₂ M) (inj₁ IdentTC) (lift ())
    lawMorph2 (inj₂ M) (inj₂ .M) (ApplyB .M) = FunctorB M
    
    lawMorph3 : ∀ (M N : TyCons) (b₁ : B[ M , Id ]▷ N) (b₂ : B[ Id , M ]▷ N)
              → ∀ {α β : Type} (v : α) (f : α → ⟨ M ⟩ β) 
              → (bind M Id N b₁) (f v) (id lawId) ≡ (bind Id M N b₂) ((id lawId) v) f
    lawMorph3 (inj₁ IdentTC) (inj₁ IdentTC) IdentB IdentB v f = refl
    lawMorph3 (inj₁ IdentTC) (inj₂ M) b₁ b₂ v f with decR M
    lawMorph3 (inj₁ IdentTC) (inj₂ M) (ReturnB .M r₁) (ReturnB .M r₂) v f | yes rCompat = begin
      bindReturn M monad r₁ (f v) (id lawId)
        ≡⟨ refl ⟩
      SuperMonad.return monad r₁ (f v)
        ≡⟨ cong (λ X → SuperMonad.return monad X (f v)) {!!} ⟩
      SuperMonad.return monad r₂ (f v)
        ≡⟨ refl ⟩
      bindReturn M monad r₂ (id lawId v) f ∎
    lawMorph3 (inj₁ IdentTC) (inj₂ M) (lift ()) (lift ()) v f | no ¬r
    lawMorph3 (inj₂ M) (inj₁ IdentTC) (lift ()) (lift ()) v f
    lawMorph3 (inj₂ M) (inj₂ .M) (FunctorB .M) (ApplyB .M) v f = begin
      bindFunctor M monad (f v) (id lawId) 
        ≡⟨ refl ⟩
      Functor.fmap (SuperMonad.functor monad M) (id lawId) (f v)
        ≡⟨ cong (λ X → X (f v)) (Functor.lawId (SuperMonad.functor monad M)) ⟩
      f v
        ≡⟨ refl ⟩
      bindApply M monad (id lawId v) f ∎
    
    lawDiamond1 : ∀ (M N R T : TyCons)
                → (∃ λ(P : TyCons) → B[ M , N ]▷ P × B[ P , R ]▷ T)
                → (∃ λ(S : TyCons) → B[ N , R ]▷ S × B[ M , S ]▷ T)
    lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC , IdentB , IdentB) = idTC , IdentB , IdentB
    lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ R) (inj₁ IdentTC) (inj₁ IdentTC , IdentB , lift ())
    lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ M) (inj₁ IdentTC , IdentB , b) = idTC , IdentB , b
    lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ R) (inj₂ .R) (inj₁ IdentTC , IdentB , ApplyB .R) = inj₂ R , ApplyB R , ApplyB R
    lawDiamond1 (inj₁ IdentTC) (inj₂ N) R T (inj₁ IdentTC , lift () , b₂)
    lawDiamond1 (inj₂ M) (inj₁ IdentTC) R T (inj₁ IdentTC , lift () , b₂)
    lawDiamond1 (inj₂ M) (inj₂ N) R T (inj₁ IdentTC , lift () , b₂)
    lawDiamond1 M N (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ P , b₁ , lift ())
    lawDiamond1 M N (inj₂ R) (inj₁ IdentTC) (inj₂ P , b₁ , lift ())
    lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ M) (inj₂ .M , b , FunctorB .M) = idTC , IdentB , b
    lawDiamond1 (inj₁ IdentTC) (inj₂ N) (inj₁ IdentTC) (inj₂ .N) (inj₂ .N , ApplyB .N , FunctorB .N) = inj₂ N , FunctorB N , ApplyB N
    lawDiamond1 (inj₂ M) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ .M) (inj₂ .M , FunctorB .M , FunctorB .M) = idTC , IdentB , FunctorB M
    lawDiamond1 (inj₂ M) (inj₂ N) (inj₁ IdentTC) (inj₂ T) (inj₂ ._ , b , FunctorB ._) = inj₂ N , FunctorB N , b
    lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ R) (inj₂ T) (inj₂ M , br , bm) = inj₂ R , ApplyB R , {!!}
    lawDiamond1 (inj₁ IdentTC) (inj₂ N) (inj₂ R) (inj₂ T) (inj₂ .N , ApplyB .N , bm) = {!!}
    lawDiamond1 (inj₂ M) (inj₁ IdentTC) (inj₂ R) (inj₂ T) (inj₂ .M , FunctorB .M , bm) = {!!}
    lawDiamond1 (inj₂ M) (inj₂ N) (inj₂ R) (inj₂ T) (inj₂ P , bm1 , bm2) = {!!}
    -}

    {-
    lawDiamond2 : ∀ (M N R T : TyCons)
                → (∃ λ(S : TyCons) → B[ N , R ]▷ S × B[ M , S ]▷ T)
                → (∃ λ(P : TyCons) → B[ M , N ]▷ P × B[ P , R ]▷ T)
    lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC , IdentB , IdentB) = idTC , IdentB , IdentB
    lawDiamond2 (inj₂ M) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC , IdentB , lift ())
    lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ M) (inj₁ IdentTC , IdentB , ReturnB .M rCompat) = idTC , IdentB , ReturnB M rCompat
    lawDiamond2 (inj₂ M) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ .M) (inj₁ IdentTC , IdentB , FunctorB .M) = inj₂ M , FunctorB M , FunctorB M
    lawDiamond2 M (inj₁ IdentTC) (inj₂ R) T (inj₁ IdentTC , lift () , b₂)
    lawDiamond2 M (inj₂ N) (inj₁ IdentTC) T (inj₁ IdentTC , lift () , b₂)
    lawDiamond2 M (inj₂ N) (inj₂ R) T (inj₁ IdentTC , lift () , b₂)
    lawDiamond2 (inj₁ IdentTC) N R (inj₁ IdentTC) (inj₂ S , b₁ , lift ())
    lawDiamond2 (inj₂ M) N R (inj₁ IdentTC) (inj₂ S , b₁ , lift ())
    lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ M) (inj₂ .M , ReturnB .M rCompat , ApplyB .M) = idTC , IdentB , ReturnB M rCompat
    lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ R) (inj₂ .R) (inj₂ .R , ApplyB .R , ApplyB .R) = idTC , IdentB , ApplyB R
    lawDiamond2 (inj₁ IdentTC) (inj₂ N) (inj₁ IdentTC) (inj₂ .N) (inj₂ .N , FunctorB .N , ApplyB .N) = inj₂ N , ApplyB N , FunctorB N
    lawDiamond2 (inj₁ IdentTC) (inj₂ N) (inj₂ R) (inj₂ ._) (inj₂ ._ , MonadB .N .R bCompat , ApplyB ._) = {!!}
    lawDiamond2 (inj₂ M) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ ._) (inj₂ M₁ , ReturnB .M₁ rCompat , MonadB .M .M₁ bCompat) = {!!}
    lawDiamond2 (inj₂ M) (inj₁ IdentTC) (inj₂ R) (inj₂ ._) (inj₂ .R , ApplyB .R , MonadB .M .R bCompat) = {!!}
    lawDiamond2 (inj₂ M) (inj₂ N) (inj₁ IdentTC) (inj₂ ._) (inj₂ .N , FunctorB .N , MonadB .M .N bCompat) = {!!}
    lawDiamond2 (inj₂ M) (inj₂ N) (inj₂ R) (inj₂ ._) (inj₂ ._ , MonadB .N .R bCompat₁ , MonadB .M ._ bCompat₂) = {!!}
    
    lawAssoc : ∀ (M N P R T S : TyCons) 
             → (b₁ : B[ M , N ]▷ P) → (b₂ : B[ P , R ]▷ T) 
             → (b₃ : B[ N , R ]▷ S) → (b₄ : B[ M , S ]▷ T)
             → ∀ {α β γ : Type} (m : ⟨ M ⟩ α) (f : α → ⟨ N ⟩ β) (g : β → ⟨ R ⟩ γ)
             → (bind P R T b₂) ((bind M N P b₁) m f) g ≡ (bind M S T b₄) m (λ x → (bind N R S b₃) (f x) g)
    lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) IdentB IdentB IdentB IdentB m f g = refl
    lawAssoc (inj₂ M) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (lift ()) IdentB IdentB (lift ()) m f g
    lawAssoc M (inj₂ N) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) b₁ IdentB (lift ()) b₄ m f g
    lawAssoc (inj₁ IdentTC) N (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ S) b₁ IdentB b₃ (lift ()) m f g
    lawAssoc (inj₂ M) N (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ S) b₁ IdentB b₃ (lift ()) m f g
    lawAssoc M N (inj₁ IdentTC) (inj₂ R) (inj₁ IdentTC) S b₁ (lift ()) b₃ b₄ m f g
    lawAssoc M N (inj₂ P) (inj₁ IdentTC) (inj₁ IdentTC) S b₁ (lift ()) b₃ b₄ m f g
    lawAssoc M N (inj₂ P) (inj₂ R) (inj₁ IdentTC) S b₁ (lift ()) b₃ b₄ m f g
    lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ M) (inj₁ IdentTC) IdentB (ReturnB .M rCompat₁) IdentB (ReturnB .M rCompat₂) m f g
      = {!!}
    lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ R) (inj₂ .R) (inj₁ IdentTC) IdentB (ApplyB .R) (lift ()) (ReturnB .R rCompat) m f g
    lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ M) (inj₂ .M) IdentB (ReturnB .M rCompat₁) (ReturnB .M rCompat₂) (ApplyB .M) m f g
      = {!!}
    lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ M) (inj₂ .M) (inj₂ .M) IdentB (ApplyB .M) (ApplyB .M) (ApplyB .M) m f g
      = {!!}
    lawAssoc (inj₁ IdentTC) (inj₂ N) (inj₁ IdentTC) R (inj₂ T) S (lift ()) b₂ b₃ b₄ m f g
    lawAssoc (inj₂ M) (inj₁ IdentTC) (inj₁ IdentTC) R (inj₂ T) S (lift ()) b₂ b₃ b₄ m f g
    lawAssoc (inj₂ M) (inj₂ N) (inj₁ IdentTC) R (inj₂ T) S (lift ()) b₂ b₃ b₄ m f g
    lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ M) (inj₁ IdentTC) (inj₂ .M) (inj₁ IdentTC) (ReturnB .M rCompat₁) (FunctorB .M) IdentB (ReturnB .M rCompat₂) m f g
      = {!!}
    lawAssoc (inj₂ M) (inj₁ IdentTC) (inj₂ .M) (inj₁ IdentTC) (inj₂ .M) (inj₁ IdentTC) (FunctorB .M) (FunctorB .M) IdentB (FunctorB .M) m f g
      = {!!}
    lawAssoc M (inj₁ IdentTC) (inj₂ P) (inj₂ R) (inj₂ T) (inj₁ IdentTC) b₁ b₂ (lift ()) b₄ m f g
    lawAssoc M (inj₂ N) (inj₂ P) (inj₁ IdentTC) (inj₂ T) (inj₁ IdentTC) b₁ b₂ (lift ()) b₄ m f g
    lawAssoc M (inj₂ N) (inj₂ P) (inj₂ R) (inj₂ T) (inj₁ IdentTC) b₁ b₂ (lift ()) b₄ m f g
    lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ P) (inj₁ IdentTC) (inj₂ .P) (inj₂ .P) (ReturnB .P rCompat) (FunctorB .P) (ReturnB .P x) (ApplyB .P) m f g
      = {!!}
    lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ P) (inj₂ R) (inj₂ ._) (inj₂ ._) (ReturnB .P rCompat) (MonadB .P .R bCompat) b₃ (ApplyB ._) m f g
      = {!!}
    lawAssoc (inj₁ IdentTC) (inj₂ M) (inj₂ .M) (inj₁ IdentTC) (inj₂ .M) (inj₂ .M) (ApplyB .M) (FunctorB .M) (FunctorB .M) (ApplyB .M) m f g
      = {!!}
    lawAssoc (inj₁ IdentTC) (inj₂ N) (inj₂ .N) (inj₂ R) (inj₂ ._) (inj₂ ._) (ApplyB .N) (MonadB .N .R bCompat₁) (MonadB .N .R bCompat₂) (ApplyB ._) m f g
      = {!!}
    lawAssoc (inj₂ M) (inj₁ IdentTC) (inj₂ .M) (inj₁ IdentTC) (inj₂ .M) (inj₂ S) (FunctorB .M) (FunctorB .M) (ReturnB .S rCompat) b₄ m f g
      = {!!}
    lawAssoc (inj₂ M) (inj₁ IdentTC) (inj₂ .M) (inj₂ R) (inj₂ ._) (inj₂ .R) (FunctorB .M) (MonadB .M .R bCompat₁) (ApplyB .R) (MonadB .M .R bCompat₂) m f g
      = {!!}
    lawAssoc (inj₂ M) (inj₂ N) (inj₂ ._) (inj₁ IdentTC) (inj₂ ._) (inj₂ .N) (MonadB .M .N bCompat₁) (FunctorB ._) (FunctorB .N) (MonadB .M .N bCompat₂) m f g
      = {!!}
    lawAssoc (inj₂ M) (inj₂ N) (inj₂ ._) (inj₂ R) (inj₂ ._) (inj₂ ._) (MonadB .M .N bCompat₁) (MonadB ._ .R bCompat₂) (MonadB .N .R bCompat₃) b₄ m f g
      = {!!}
-}
   {-
    lawClosure : ∀ (M N P S T U : TyCons)
               → ( B[ M , N ]▷ P × B[ S , Id ]▷ M × B[ T , Id ]▷ N × B[ P , Id ]▷ U )
               → B[ S , T ]▷ U
    lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (IdentB , IdentB , IdentB , IdentB) = IdentB
    lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ T) (inj₁ IdentTC) (IdentB , IdentB , lift () , IdentB)
    lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ S) T (inj₁ IdentTC) (IdentB , lift () , b₃ , IdentB)
    lawClosure (inj₁ IdentTC) (inj₂ N) (inj₁ IdentTC) S T (inj₁ IdentTC) (lift () , b₂ , b₃ , IdentB)
    lawClosure (inj₂ M) (inj₁ IdentTC) (inj₁ IdentTC) S T (inj₁ IdentTC) (lift () , b₂ , b₃ , IdentB)
    lawClosure (inj₂ M) (inj₂ N) (inj₁ IdentTC) S T (inj₁ IdentTC) (lift () , b₂ , b₃ , IdentB)
    lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ U) (IdentB , IdentB , IdentB , bRet) = bRet
    lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ S) (inj₁ IdentTC) (inj₂ U) (IdentB , lift () , IdentB , bRet)
    lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ T) (inj₂ U) (IdentB , IdentB , lift () , bRet)
    lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ S) (inj₂ T) (inj₂ U) (IdentB , lift () , lift () , bRet)
    lawClosure (inj₁ IdentTC) (inj₂ N) (inj₁ IdentTC) S T (inj₂ U) (lift () , b₂ , b₃ , bRet)
    lawClosure (inj₂ M) (inj₁ IdentTC) (inj₁ IdentTC) S T (inj₂ U) (lift () , b₂ , b₃ , bRet)
    lawClosure (inj₂ M) (inj₂ N) (inj₁ IdentTC) S T (inj₂ U) (lift () , b₂ , b₃ , bRet)
    lawClosure M N (inj₂ P) S T (inj₁ IdentTC) (b₁ , b₂ , b₃ , lift ())
    lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ M) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ .M) (bRet , IdentB , IdentB , FunctorB .M) = bRet
    lawClosure (inj₁ IdentTC) (inj₂ M) (inj₂ .M) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ .M) (ApplyB .M , IdentB , bRet , FunctorB .M) = bRet
    lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ P) (inj₁ IdentTC) (inj₂ T) (inj₂ .P) (bRet , IdentB , lift () , FunctorB .P)
    lawClosure (inj₁ IdentTC) (inj₂ N) (inj₂ .N) (inj₁ IdentTC) (inj₂ .N) (inj₂ .N) (ApplyB .N , IdentB , FunctorB .N , FunctorB .N) = ApplyB N
    lawClosure (inj₁ IdentTC) N (inj₂ P) (inj₂ S) T (inj₂ .P) (b₁ , lift () , b₃ , FunctorB .P)
    lawClosure (inj₂ M) (inj₁ IdentTC) (inj₂ .M) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ .M) (FunctorB .M , bRet , IdentB , FunctorB .M) = bRet
    lawClosure (inj₂ M) (inj₂ N) (inj₂ P) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ ._) (bMon , bRet₁ , bRet₂ , FunctorB ._) with decR P
    lawClosure (inj₂ M) (inj₂ N) (inj₂ P) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ .P) (bMon , bRet₁ , bRet₂ , FunctorB .P) | yes rCompat = ReturnB P rCompat
    lawClosure (inj₂ M) (inj₂ N) (inj₂ P) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ .P) (bMon , bRet₁ , bRet₂ , FunctorB .P) | no ¬p = lift {!!}
    lawClosure (inj₂ M) (inj₁ IdentTC) (inj₂ .M) (inj₁ IdentTC) (inj₂ T) (inj₂ .M) (FunctorB .M , bRet , lift () , FunctorB .M)
    lawClosure (inj₂ M) (inj₂ N) (inj₂ P) (inj₁ IdentTC) (inj₂ .N) (inj₂ .P) (bMon , bRet , FunctorB .N , FunctorB .P) with decR M
    lawClosure (inj₂ M) (inj₂ N) (inj₂ P) (inj₁ IdentTC) (inj₂ .N) (inj₂ .P) (bMon , ReturnB .M rCompat , FunctorB .N , FunctorB .P) | yes rCompat' with decB M N
    lawClosure (inj₂ M) (inj₂ N) (inj₂ P) (inj₁ IdentTC) (inj₂ .N) (inj₂ .P) (bMon , ReturnB .M rCompat , FunctorB .N , FunctorB .P) | yes rCompat' | yes bCompat' = {!!}
    lawClosure (inj₂ M) (inj₂ N) (inj₂ P) (inj₁ IdentTC) (inj₂ .N) (inj₂ .P) (lift () , ReturnB .M rCompat , FunctorB .N , FunctorB .P) | yes rCompat' | no ¬bCompat
    lawClosure (inj₂ M) (inj₂ N) (inj₂ P) (inj₁ IdentTC) (inj₂ .N) (inj₂ .P) (bMon , lift () , FunctorB .N , FunctorB .P) | no ¬rCompat
    lawClosure (inj₂ M) (inj₁ IdentTC) (inj₂ .M) (inj₂ .M) (inj₁ IdentTC) (inj₂ .M) (FunctorB .M , FunctorB .M , IdentB , FunctorB .M) = FunctorB M
    lawClosure (inj₂ M) (inj₁ IdentTC) (inj₂ .M) (inj₂ .M) (inj₂ T) (inj₂ .M) (FunctorB .M , FunctorB .M , lift () , FunctorB .M)
    lawClosure (inj₂ M) (inj₂ N) (inj₂ P) (inj₂ .M) (inj₁ IdentTC) (inj₂ ._) (bMon , FunctorB .M , bRet , FunctorB ._) = {!!}
    lawClosure (inj₂ M) (inj₂ N) (inj₂ P) (inj₂ .M) (inj₂ .N) (inj₂ ._) (bMon , FunctorB .M , FunctorB .N , FunctorB ._) = bMon
-}
