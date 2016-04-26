
module SuperMonad.EffectMonad where

-- Stdlib
open import Level
open import Function
open import Agda.Primitive
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Data.Nat
open import Data.Vec hiding ( _>>=_ )
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Local
open import Utilities
open import Haskell
open import Identity
open import Functor
open import Polymonad
open import Parameterized.PhantomIndices
open import Parameterized.EffectMonad
open import SuperMonad.Definition
--open import SuperMonad.HaskSuperMonad

open Parameterized.EffectMonad.Monoid

-- -----------------------------------------------------------------------------
-- Indexed Monads are Super Monads
-- -----------------------------------------------------------------------------

EffectMonad→SuperMonad : ∀ {n}
                       → (Effect : Set n)
                       → (EffectMonoid : Monoid Effect)
                       → (M : Effect → TyCon)
                       → EffectMonad Effect {{EffectMonoid}} M → SuperMonad (EffMonadTyCons Effect)
EffectMonad→SuperMonad {n = n} Effect monoid M monad = record
  { ⟨_⟩ = ⟨_⟩
  ; Binds = Binds
  ; Returns = Returns
  ; functor = functor
  ; tyConArity = tyConArity
  ; tyConArgTys = tyConArgTys
  ; tyCon = tyCon
  ; bind = bind
  ; return = return
  ; lawSingleTyCon = lawSingleTyCon
  ; lawUniqueBind = lawUniqueBind
  ; lawUniqueReturn = lawUniqueReturn
  ; lawIdR = lawIdR
  ; lawIdL = lawIdL
  ; lawAssoc = lawAssoc
  ; lawMonadFmap = lawMonadFmap
  } where
    TyCons = EffMonadTyCons Effect

    _∙_ = Monoid._∙_ monoid
    ε = Monoid.ε monoid
    
    ⟨_⟩ : TyCons → TyCon
    ⟨_⟩ (EffMonadTC e) = M e
    
    Binds : TyCons → TyCons → TyCons → Set n
    Binds (EffMonadTC m) (EffMonadTC n) (EffMonadTC p) = p ≡ m ∙ n 
    
    Returns : TyCons → Set n
    Returns (EffMonadTC m) = m ≡ ε

    tyConArity : ℕ
    tyConArity = 1

    tyConArgTys : Vec (Set n) tyConArity
    tyConArgTys = Effect ∷ []
    
    tyCon : ParamTyCon tyConArgTys
    tyCon e = lift $ M e
    
    _>>=_ = EffectMonad._>>=_ monad
    return' = EffectMonad.return monad
    
    bind : {M N P : TyCons} → Binds M N P → [ ⟨ M ⟩ , ⟨ N ⟩ ]▷ ⟨ P ⟩
    bind {M = EffMonadTC m} {N = EffMonadTC n} {P = EffMonadTC .(m ∙ n)} refl = _>>=_
    
    return : ∀ {α : Type} → {M : TyCons} → Returns M → α → ⟨ M ⟩ α
    return {M = EffMonadTC ._} refl = return'
    
    fmap : ∀ {m : Monoid.carrier monoid} {α β : Type} → (α → β) → M m α → M m β
    fmap {m = m} {β = β} f ma = subst₂ M (Monoid.lawIdR monoid m) refl (ma >>= (return' ∘ f))
    
    lawSingleTyCon : ∀ (M : TyCons) 
                   → ∃Indices tyConArgTys tyCon (λ X → Lift {ℓ = lsuc n} (⟨ M ⟩ ≡ X))
    lawSingleTyCon (EffMonadTC m) = m , lift refl
    
    lawUniqueBind : {M N P : TyCons} 
                  → (b₁ b₂ : Binds M N P) 
                  → b₁ ≡ b₂
    lawUniqueBind {M = EffMonadTC m} {N = EffMonadTC n} {P = EffMonadTC .(m ∙ n)} refl refl = refl
    
    lawUniqueReturn : {M : TyCons} 
                    → (r₁ r₂ : Returns M) 
                    → r₁ ≡ r₂
    lawUniqueReturn {M = EffMonadTC .ε} refl refl = refl
    {-
    Mε◆Me≡Me : (e : Monoid.carrier monoid) → EffMonadTC ε ◆ EffMonadTC e ≡ EffMonadTC e
    Mε◆Me≡Me e with Monoid.lawIdL monoid e
    Mε◆Me≡Me e | p with ε ∙ e 
    Mε◆Me≡Me e | refl | .e = refl
    
    Me◆Mε≡Me : (e : Monoid.carrier monoid) → EffMonadTC e ◆ EffMonadTC ε ≡ EffMonadTC e
    Me◆Mε≡Me e with Monoid.lawIdR monoid e
    Me◆Mε≡Me e | p with e ∙ ε 
    Me◆Mε≡Me e | refl | .e = refl
    
    helpSubst1 : ∀ {β : Type}
               → (e : Monoid.carrier monoid)
               → (N◆M≡M : EffMonadTC ε ◆ EffMonadTC e ≡ EffMonadTC e )
               → (m : ⟨ EffMonadTC e ⟩ β) 
               → subst₂ M (sym (Monoid.lawIdL monoid e)) refl m ≡ subst (λ X → ⟨ X ⟩ β) (sym N◆M≡M) m
    helpSubst1 e N◆M≡M m with Monoid.lawIdL monoid e 
    helpSubst1 e N◆M≡M m | p with ε ∙ e
    helpSubst1 e refl m | refl | .e = refl
    
    helpSubst2 : ∀ {β : Type}
               → (e : Monoid.carrier monoid)
               → (N◆M≡M : EffMonadTC e ◆ EffMonadTC ε ≡ EffMonadTC e )
               → (m : ⟨ EffMonadTC e ⟩ β) 
               → subst₂ M (sym (Monoid.lawIdR monoid e)) refl m ≡ subst (λ X → ⟨ X ⟩ β) (sym N◆M≡M) m
    helpSubst2 e N◆M≡M m with Monoid.lawIdR monoid e 
    helpSubst2 e N◆M≡M m | p with e ∙ ε
    helpSubst2 e refl m | refl | .e = refl
    
    helpSubst3 : ∀ {β : Type}
               → (e₁ e₂ e₃ : Monoid.carrier monoid)
               → (assoc : EffMonadTC e₁ ◆ (EffMonadTC e₂ ◆ EffMonadTC e₃) ≡ (EffMonadTC e₁ ◆ EffMonadTC e₂) ◆ EffMonadTC e₃) 
               → (m : ⟨ EffMonadTC ((e₁ ∙ e₂) ∙ e₃) ⟩ β) 
               → subst₂ M (Monoid.lawAssoc monoid e₁ e₂ e₃) refl m ≡ subst (λ X → ⟨ X ⟩ β) (sym assoc) m
    helpSubst3 e₁ e₂ e₃ assoc m with Monoid.lawAssoc monoid e₁ e₂ e₃
    helpSubst3 e₁ e₂ e₃ assoc m | p with e₁ ∙ (e₂ ∙ e₃)
    helpSubst3 e₁ e₂ e₃ refl m | refl | ._ = refl
    
    helpSubst4 : ∀ {β : Type}
               → (e : Monoid.carrier monoid)
               → (N◆M≡M : EffMonadTC e ◆ EffMonadTC ε ≡ EffMonadTC e )
               → (m : ⟨ EffMonadTC (e ∙ ε) ⟩ β) 
               → subst₂ M (Monoid.lawIdR monoid e) refl m ≡ subst (λ X → ⟨ X ⟩ β) N◆M≡M m
    helpSubst4 e N◆M≡M m with Monoid.lawIdR monoid e 
    helpSubst4 e N◆M≡M m | p with e ∙ ε
    helpSubst4 e refl m | refl | .e = refl
-}
    bindEq : {α β : Type} {m n p : Effect}
           → (b : Binds (EffMonadTC m) (EffMonadTC n) (EffMonadTC p))
           → bind b {α} {β} ≡ subst (λ X → [ ⟨ EffMonadTC m ⟩ , ⟨ EffMonadTC n ⟩ ]▷ ⟨ EffMonadTC X ⟩ ) (sym b) (_>>=_) {α} {β}
    bindEq refl = refl

    bindSubstShift : {α β : Type} {m n p : Effect}
                   → (b : Binds (EffMonadTC m) (EffMonadTC n) (EffMonadTC p) )
                   → (ma : ⟨ EffMonadTC m ⟩ α) → (f : α → ⟨ EffMonadTC n ⟩ β)
                   → subst (λ X → [ ⟨ EffMonadTC m ⟩ , ⟨ EffMonadTC n ⟩ ]▷ ⟨ EffMonadTC X ⟩ ) (sym b) (_>>=_) ma f ≡ subst (λ X → ⟨ EffMonadTC X ⟩ β) (sym b) (ma >>= f)
    bindSubstShift refl ma f = refl

    subst₂ToSubst : {α : Type} {m n : Effect}
                  → (eq : m ≡ n)
                  → (ma : ⟨ EffMonadTC m ⟩ α)
                  → subst₂ M eq refl ma ≡ subst (λ X → ⟨ EffMonadTC X ⟩ α) eq ma 
    subst₂ToSubst refl ma = refl
    
    lawIdR : ∀ {α β : Type} 
           → (M N : TyCons)
           → (b : Binds M N N) → (r : Returns M)
           → (a : α) → (k : α → ⟨ N ⟩ β)
           → bind b (return r a) k ≡ k a
    lawIdR {β = β} (EffMonadTC .ε) (EffMonadTC x) b refl a k = begin
      bind b (return' a) k
        ≡⟨ cong (λ X → X (return' a) k) (bindEq b) ⟩
      subst (λ X → [ ⟨ EffMonadTC ε ⟩ , ⟨ EffMonadTC x ⟩ ]▷ ⟨ EffMonadTC X ⟩ ) (sym b) (_>>=_) (return' a) k
        ≡⟨ bindSubstShift b (return' a) k ⟩
      subst (λ X → ⟨ EffMonadTC X ⟩ β) (sym b) (return' a >>= k)
        ≡⟨ cong (λ X → subst (λ X → ⟨ EffMonadTC X ⟩ β) (sym b) X) (EffectMonad.lawIdL monad a k) ⟩
      subst (λ X → ⟨ EffMonadTC X ⟩ β) (sym b) (subst₂ M (sym (Monoid.lawIdL monoid x)) refl (k a))
        ≡⟨ cong (λ X → subst (λ X → ⟨ EffMonadTC X ⟩ β) (sym b) X) (subst₂ToSubst (sym (Monoid.lawIdL monoid x)) (k a)) ⟩
      subst (λ X → ⟨ EffMonadTC X ⟩ β) (sym b) (subst (λ X → ⟨ EffMonadTC X ⟩ β) (sym (Monoid.lawIdL monoid x)) (k a))
        ≡⟨ cong (λ Y → subst (λ X → ⟨ EffMonadTC X ⟩ β) (sym b) (subst (λ X → ⟨ EffMonadTC X ⟩ β) Y (k a))) 
                (proof-irrelevance (sym (Monoid.lawIdL monoid x)) b) ⟩
      subst (λ X → ⟨ EffMonadTC X ⟩ β) (sym b) (subst (λ X → ⟨ EffMonadTC X ⟩ β) b (k a))
        ≡⟨ subst²≡id' b (λ X → ⟨ EffMonadTC X ⟩ β) (k a) ⟩
      k a ∎

    lawIdL : ∀ {α : Type} 
           → (M N : TyCons)
           → (b : Binds M N M) → (r : Returns N)
           → (m : ⟨ M ⟩ α)
           → bind b m (return r) ≡ m
    lawIdL {α = α} (EffMonadTC e) (EffMonadTC .ε) b refl m = begin
      bind b m return' 
        ≡⟨ cong (λ X → X m return') (bindEq b) ⟩
      subst (λ X → [ ⟨ EffMonadTC e ⟩ , ⟨ EffMonadTC ε ⟩ ]▷ ⟨ EffMonadTC X ⟩ ) (sym b) (_>>=_) m return' 
        ≡⟨ bindSubstShift b m return' ⟩
      subst (λ X → ⟨ EffMonadTC X ⟩ α) (sym b) (m >>= return') 
        ≡⟨ cong (λ X → subst (λ X → ⟨ EffMonadTC X ⟩ α) (sym b) X) (EffectMonad.lawIdR monad m) ⟩
      subst (λ X → ⟨ EffMonadTC X ⟩ α) (sym b) (subst₂ M (sym (Monoid.lawIdR monoid e)) refl m) 
        ≡⟨ cong (λ Y → subst (λ X → ⟨ EffMonadTC X ⟩ α) (sym b) Y) (subst₂ToSubst (sym (Monoid.lawIdR monoid e)) m) ⟩
      subst (λ X → ⟨ EffMonadTC X ⟩ α) (sym b) (subst (λ X → ⟨ EffMonadTC X ⟩ α) (sym (Monoid.lawIdR monoid e)) m) 
        ≡⟨ cong (λ Y → subst (λ X → ⟨ EffMonadTC X ⟩ α) (sym b) (subst (λ X → ⟨ EffMonadTC X ⟩ α) Y m) ) (proof-irrelevance (sym (Monoid.lawIdR monoid e)) b) ⟩
      subst (λ X → ⟨ EffMonadTC X ⟩ α) (sym b) (subst (λ X → ⟨ EffMonadTC X ⟩ α) b m) 
        ≡⟨ subst²≡id' b (λ X → ⟨ EffMonadTC X ⟩ α) m ⟩
      m ∎

    lawAssoc : ∀ {α β γ : Type} 
             → (M N P S T : TyCons)
             → (b₁ : Binds M N P) → (b₂ : Binds S T N)
             → (b₃ : Binds N T P) → (b₄ : Binds M S N)
             → (m : ⟨ M ⟩ α) → (f : α → ⟨ S ⟩ β) → (g : β → ⟨ T ⟩ γ)
             → bind b₁ m (λ x → bind b₂ (f x) g) ≡ bind b₃ (bind b₄ m f) g
    lawAssoc {γ = γ} (EffMonadTC e₁) (EffMonadTC e₂) (EffMonadTC e₃) b c d e m f g = {!!} {- begin 
      subst (λ X → ⟨ X ⟩ γ) assoc (m >>= (λ x → f x >>= g))
        ≡⟨ cong (λ X → subst (λ Y → ⟨ Y ⟩ γ) assoc X) (EffectMonad.lawAssoc monad m f g) ⟩
      subst (λ X → ⟨ X ⟩ γ) assoc (subst₂ M (Monoid.lawAssoc monoid e₁ e₂ e₃) refl ((m >>= f) >>= g))
        ≡⟨ cong (λ X → subst (λ Y → ⟨ Y ⟩ γ) assoc X) (helpSubst3 e₁ e₂ e₃ assoc (((m >>= f) >>= g))) ⟩
      subst (λ X → ⟨ X ⟩ γ) assoc (subst (λ X → ⟨ X ⟩ γ) (sym assoc) ((m >>= f) >>= g))
        ≡⟨ subst²≡id assoc (λ X → ⟨ X ⟩ γ) (((m >>= f) >>= g)) ⟩
      (m >>= f) >>= g ∎ -}
    
    shiftSubstHelp3 : ∀ {γ : Type} {e₁ e₂ : Monoid.carrier monoid}
                    → (ma : ⟨ EffMonadTC e₁ ⟩ γ)
                    → (eq1 : EffMonadTC e₁ ≡ EffMonadTC e₂ )
                    → (eq2 : e₁ ≡ e₂)
                    → subst (λ X → ⟨ X ⟩ γ) eq1 ma ≡ subst₂ M eq2 refl ma
    shiftSubstHelp3 ma refl refl = refl
    
    functor : (M : TyCons) → Functor ⟨ M ⟩
    functor (EffMonadTC m) = record 
      { fmap = fmap
      ; lawId = lawId
      ; lawDist = lawDist
      } where
        lawId : ∀ {α : Type} → fmap {α = α} identity ≡ identity
        lawId {α = α} = {!!} {- funExt (λ ma → begin
          fmap identity ma 
            ≡⟨ refl ⟩
          subst₂ M (Monoid.lawIdR monoid m) refl (ma >>= return')
            ≡⟨ cong (λ X → subst₂ M (Monoid.lawIdR monoid m) refl X) (sym (subst²≡id' (Me◆Mε≡Me m) (λ X → ⟨ X ⟩ α) (ma >>= return'))) ⟩
          subst₂ M (Monoid.lawIdR monoid m) refl (subst (λ X → ⟨ X ⟩ α) (sym (Me◆Mε≡Me m)) (subst (λ X → ⟨ X ⟩ α) (Me◆Mε≡Me m) (ma >>= return') ) )
            ≡⟨ cong (λ X → subst₂ M (Monoid.lawIdR monoid m) refl (subst (λ X → ⟨ X ⟩ α) (sym (Me◆Mε≡Me m)) X )) 
                    (lawIdL (EffMonadTC m) (EffMonadTC ε) (Me◆Mε≡Me m) (lift tt) refl ma) ⟩
          subst₂ M (Monoid.lawIdR monoid m) refl (subst (λ X → ⟨ X ⟩ α) (sym (Me◆Mε≡Me m)) ma)
            ≡⟨ helpSubst4 m (Me◆Mε≡Me m) (subst (λ X → ⟨ X ⟩ α) (sym (Me◆Mε≡Me m)) ma) ⟩
          subst (λ X → ⟨ X ⟩ α) (Me◆Mε≡Me m) (subst (λ X → ⟨ X ⟩ α) (sym (Me◆Mε≡Me m)) ma)
            ≡⟨ subst²≡id (Me◆Mε≡Me m) (λ X → ⟨ X ⟩ α) ma ⟩
          identity ma ∎) -}

        Meεε≡Meε : EffMonadTC (m ∙ (ε ∙ ε)) ≡ EffMonadTC (m ∙ ε)
        Meεε≡Meε = cong (λ X → EffMonadTC (m ∙ X)) (Monoid.lawIdL monoid ε)
        
        eεε≡eε : (m ∙ ε) ∙ ε ≡ m ∙ ε
        eεε≡eε = cong (λ X → X ∙ ε) (Monoid.lawIdR monoid m)
        
        assoc : EffMonadTC (m ∙ (ε ∙ ε)) ≡ EffMonadTC ((m ∙ ε) ∙ ε)
        assoc = cong (λ X → EffMonadTC X) ((begin
          m ∙ (ε ∙ ε) 
            ≡⟨ cong (λ X → m ∙ X) (Monoid.lawIdR monoid ε) ⟩
          m ∙ ε
            ≡⟨ cong (λ X → X ∙ ε) (sym (Monoid.lawIdR monoid m)) ⟩
          (m ∙ ε) ∙ ε ∎))
        
        shiftSubstHelp1 : ∀ {α β : Type} {e e₁ e₂ m : Monoid.carrier monoid}
                       → (eqInner : EffMonadTC (e₁ ∙ e₂) ≡ EffMonadTC m)
                       → (eqOuter : EffMonadTC (e ∙ (e₁ ∙ e₂)) ≡ EffMonadTC (e ∙ m) )
                       → (ma : ⟨ EffMonadTC e ⟩ α) → (f : α → ⟨ EffMonadTC (e₁ ∙ e₂) ⟩ β)
                       → ma >>= (λ x → subst (λ X → ⟨ X ⟩ β) eqInner (f x)) ≡ subst (λ X → ⟨ X ⟩ β) eqOuter (ma >>= f)
        shiftSubstHelp1 refl refl ma f = refl
        
        shiftSubstHelp2 : ∀ {α β : Type} {e e₁ e₂ m : Monoid.carrier monoid}
                       → (eqInner : e₁ ∙ e₂ ≡ m)
                       → (eqOuter : (e₁ ∙ e₂) ∙ e ≡ m ∙ e)
                       → (ma : ⟨ EffMonadTC (e₁ ∙ e₂) ⟩ α) → (f : α → ⟨ EffMonadTC e ⟩ β)
                       → subst₂ M eqOuter refl (ma >>= f) ≡ (subst₂ M eqInner refl ma) >>= f
        shiftSubstHelp2 refl refl ma f = refl

        shiftSubstHelp4 : ∀ {γ : Type} {e e₁ e₂ m : Monoid.carrier monoid}
                        → (ma : ⟨ EffMonadTC ((m ∙ e₁) ∙ e₂) ⟩ γ)
                        → (eq1 : EffMonadTC (m ∙ (e₁ ∙ e₂)) ≡ EffMonadTC e )
                        → (eq2 : EffMonadTC ((m ∙ e₁) ∙ e₂) ≡ EffMonadTC (m ∙ (e₁ ∙ e₂)))
                        → subst (λ X → ⟨ X ⟩ γ) eq1 (subst (λ X → ⟨ X ⟩ γ) eq2 ma) ≡ subst (λ X → ⟨ X ⟩ γ) (trans eq2 eq1) ma
        shiftSubstHelp4 {e₁ = e₁} {e₂ = e₂} {m = m} ma refl eq2 with (m ∙ e₁) ∙ e₂
        shiftSubstHelp4 ma refl refl | ._ = refl

        lawDist : ∀ {α β γ : Type} 
                → (f : β → γ) → (g : α → β) 
                → fmap (f ∘ g) ≡ fmap f ∘ fmap g
        lawDist {β = β} {γ = γ} f g = {!!} {- funExt (λ ma → begin 
          fmap (f ∘ g) ma
            ≡⟨ refl ⟩
          subst₂ M (Monoid.lawIdR monoid m) refl (ma >>= (λ x → return' (f (g x))))
            ≡⟨ cong (λ X → subst₂ M (Monoid.lawIdR monoid m) refl (ma >>= X)) 
                    (funExt (λ x → sym (lawIdR (EffMonadTC ε) (EffMonadTC ε) (Mε◆Me≡Me ε) (lift tt) refl (g x) (return' ∘ f)))) ⟩
          subst₂ M (Monoid.lawIdR monoid m) refl (ma >>= (λ x → subst (λ X → ⟨ X ⟩ γ) (Mε◆Me≡Me ε) (return' (g x) >>= (return' ∘ f))))
            ≡⟨ cong (λ X → subst₂ M (Monoid.lawIdR monoid m) refl X) (shiftSubstHelp1 (Mε◆Me≡Me ε) Meεε≡Meε ma (λ x → return' (g x) >>= (return' ∘ f))) ⟩
          subst₂ M (Monoid.lawIdR monoid m) refl (subst (λ X → ⟨ X ⟩ γ) Meεε≡Meε (ma >>= (λ x → return' (g x) >>= (return' ∘ f))))
            ≡⟨ cong (λ X → subst₂ M (Monoid.lawIdR monoid m) refl (subst (λ X → ⟨ X ⟩ γ) Meεε≡Meε X)) 
                    (sym (subst²≡id' assoc (λ X → ⟨ X ⟩ γ) (ma >>= (λ x → return' (g x) >>= (return' ∘ f))))) ⟩
          subst₂ M (Monoid.lawIdR monoid m) refl 
                 (subst (λ X → ⟨ X ⟩ γ) Meεε≡Meε 
                        (subst (λ X → ⟨ X ⟩ γ) (sym assoc) 
                               (subst (λ X → ⟨ X ⟩ γ) assoc (ma >>= (λ x → return' (g x) >>= (return' ∘ f))))))
            ≡⟨ cong (λ X → subst₂ M (Monoid.lawIdR monoid m) refl (subst (λ X → ⟨ X ⟩ γ) Meεε≡Meε (subst (λ X → ⟨ X ⟩ γ) (sym assoc) X))) 
                    (lawAssoc (EffMonadTC m) (EffMonadTC ε) (EffMonadTC ε) assoc (lift tt) (lift tt) (lift tt) (lift tt) ma (return' ∘ g) (return' ∘ f)) ⟩
          subst₂ M (Monoid.lawIdR monoid m) refl (subst (λ X → ⟨ X ⟩ γ) Meεε≡Meε (subst (λ X → ⟨ X ⟩ γ) (sym assoc) ((ma >>= (return' ∘ g)) >>= (return' ∘ f))) )
            ≡⟨ cong (λ X → subst₂ M (Monoid.lawIdR monoid m) refl X) (shiftSubstHelp4 ((ma >>= (return' ∘ g)) >>= (return' ∘ f)) Meεε≡Meε (sym assoc)) ⟩
          subst₂ M (Monoid.lawIdR monoid m) refl (subst (λ X → ⟨ X ⟩ γ) (trans (sym assoc) Meεε≡Meε) ((ma >>= (return' ∘ g)) >>= (return' ∘ f)) )
            ≡⟨ cong (λ X → subst₂ M (Monoid.lawIdR monoid m) refl X) (shiftSubstHelp3 ((ma >>= (return' ∘ g)) >>= (return' ∘ f)) ((trans (sym assoc) Meεε≡Meε)) eεε≡eε) ⟩
          subst₂ M (Monoid.lawIdR monoid m) refl (subst₂ M eεε≡eε refl ((ma >>= (return' ∘ g)) >>= (return' ∘ f)))
            ≡⟨ cong (λ X → subst₂ M (Monoid.lawIdR monoid m) refl X) (shiftSubstHelp2 (Monoid.lawIdR monoid m) eεε≡eε (ma >>= (return' ∘ g)) (return' ∘ f)) ⟩
          subst₂ M (Monoid.lawIdR monoid m) refl ((subst₂ M (Monoid.lawIdR monoid m) refl (ma >>= (return' ∘ g))) >>= (return' ∘ f))
            ≡⟨ refl ⟩
          (fmap f ∘ fmap g) ma ∎) -}
    
    lawMonadFmap : ∀ {α β : Type}
                 → (M N : TyCons)
                 → (b : Binds M N M) → (r : Returns N)
                 → (f : α → β) → (m : ⟨ M ⟩ α)
                 → bind b m (return r ∘ f) ≡ Functor.fmap (functor M) f m
    lawMonadFmap {β = β} (EffMonadTC x) (EffMonadTC ._) b refl f ma = {!!} {- begin
      subst (λ X → ⟨ X ⟩ β) M◆N≡M (ma >>= (return' ∘ f))
        ≡⟨ shiftSubstHelp3 (ma >>= (return' ∘ f)) M◆N≡M (Monoid.lawIdR monoid x) ⟩
      subst₂ M (Monoid.lawIdR monoid x) refl (ma >>= (return' ∘ f))
        ≡⟨ refl ⟩
      fmap f ma ∎ -}
{-
EffectMonad→HaskSuperMonad : ∀ {n}
                     → (Effect : Set n)
                     → (EffectMonoid : Monoid Effect)
                     → (M : Effect → TyCon)
                     → EffectMonad Effect {{EffectMonoid}} M → HaskSuperMonad (EffMonadTyCons Effect)
EffectMonad→HaskSuperMonad Effect monoid M monad = record
  { supermonad = supermonad
  ; lawUniqueBind = lawUniqueBind
  ; lawCommuteFmapBind = lawCommuteFmapBind
  ; lawDecomposeFmapIntro = lawDecomposeFmapIntro
  } where
    supermonad : SuperMonad (EffMonadTyCons Effect)
    supermonad = EffectMonad→SuperMonad Effect monoid M monad
    
    TyCons = EffMonadTyCons Effect
    Binds = SuperMonad.Binds supermonad
    ⟨_⟩ = SuperMonad.⟨_⟩ supermonad
    bind = SuperMonad.bind supermonad
    functor = SuperMonad.functor supermonad
    _◆_ = SuperMonad._◆_ supermonad
    
    _>>=_ = EffectMonad._>>=_ monad
    return = EffectMonad.return monad
    
    _∙_ = Monoid._∙_ monoid
    ε = Monoid.ε monoid
    
    open Functor.Functor
    
    lawUniqueBind : {α β : Type}
                  → (M N : TyCons)
                  → (b₁ b₂ : Binds M N)
                  → (m : ⟨ M ⟩ α) → (f : α → ⟨ N ⟩ β)
                  → bind b₁ m f ≡ bind b₂ m f
    lawUniqueBind (EffMonadTC x) (EffMonadTC y) (lift tt) (lift tt) m f = refl
    
    
    shiftSubstHelp1 : ∀ {α β : Type} {e e₁ e₂ m : Monoid.carrier monoid}
                    → (eqInner : e₁ ∙ e₂ ≡ m)
                    → (eqOuter : e ∙ (e₁ ∙ e₂) ≡ e ∙ m)
                    → (ma : ⟨ EffMonadTC e ⟩ α) → (f : α → ⟨ EffMonadTC (e₁ ∙ e₂) ⟩ β)
                    → subst₂ M eqOuter refl (ma >>= f) ≡ ma >>= (λ x → (subst₂ M eqInner refl (f x)))
    shiftSubstHelp1 refl refl ma f = refl
    
    shiftSubstHelp2 : ∀ {α β : Type} {e e₁ e₂ m : Monoid.carrier monoid}
                    → (eqInner : e₁ ∙ e₂ ≡ m)
                    → (eqOuter : (e₁ ∙ e₂) ∙ e ≡ m ∙ e)
                    → (ma : ⟨ EffMonadTC (e₁ ∙ e₂) ⟩ α) → (f : α → ⟨ EffMonadTC e ⟩ β)
                    → subst₂ M eqOuter refl (ma >>= f) ≡ (subst₂ M eqInner refl ma) >>= f
    shiftSubstHelp2 refl refl ma f = refl
    
    liftMonLaw : {e₁ e₂ : Monoid.carrier monoid} → (e₁ ≡ e₂) → EffMonadTC e₁ ≡ EffMonadTC e₂
    liftMonLaw refl = refl
    
    helpSubst1 : ∀ {β : Type}
               → {x y : Monoid.carrier monoid}
               → (monEq : x ≡ y)
               → (m : ⟨ EffMonadTC x ⟩ β) 
               → subst (λ X → ⟨ X ⟩ β) (liftMonLaw monEq) m
                 ≡ subst₂ M monEq refl m
    helpSubst1 refl m = refl
    
    helpSubstTrans : ∀ {β : Type}
                   → {x y z : Monoid.carrier monoid}
                   → (eq₁ : y ≡ z)
                   → (eq₂ : x ≡ y)
                   → (m : ⟨ EffMonadTC x ⟩ β) 
                   → subst₂ M eq₁ refl (subst₂ M eq₂ refl m)
                     ≡ subst₂ M (trans eq₂ eq₁) refl m
    helpSubstTrans refl refl m = refl
    
    lawCommuteFmapBind : {α β γ : Type} 
                       → (M N : TyCons)
                       → (b : Binds M N)
                       → (m : ⟨ M ⟩ α) → (f : α → ⟨ N ⟩ β) → (g : β → γ)
                       → fmap (functor (M ◆ N)) g (bind b m f) ≡ bind b m (λ x → fmap (functor N) g (f x))
    lawCommuteFmapBind {γ = γ} (EffMonadTC x) (EffMonadTC y) (lift tt) m f g = begin
      subst₂ M (Monoid.lawIdR monoid (x ∙ y)) refl ((m >>= f) >>= (return ∘ g))
        ≡⟨ cong (λ X → subst₂ M (Monoid.lawIdR monoid (x ∙ y)) refl X) 
                (sym (SuperMonad.lawAssoc supermonad (EffMonadTC x) (EffMonadTC y) (EffMonadTC ε) (liftMonLaw (sym (Monoid.lawAssoc monoid x y ε))) 
                                          (lift tt) (lift tt) (lift tt) (lift tt) m f (return ∘ g))) ⟩
      subst₂ M (Monoid.lawIdR monoid (x ∙ y)) refl (subst (λ X → ⟨ X ⟩ γ) (liftMonLaw (sym (Monoid.lawAssoc monoid x y ε))) (m >>= (λ x → f x >>= (return ∘ g))))
        ≡⟨ cong (λ X → subst₂ M (Monoid.lawIdR monoid (x ∙ y)) refl X) (helpSubst1 (sym (Monoid.lawAssoc monoid x y ε)) (m >>= (λ x → f x >>= (return ∘ g)))) ⟩
      subst₂ M (Monoid.lawIdR monoid (x ∙ y)) refl (subst₂ M (sym (Monoid.lawAssoc monoid x y ε)) refl (m >>= (λ x → f x >>= (return ∘ g))))
        ≡⟨ helpSubstTrans (Monoid.lawIdR monoid (x ∙ y)) (sym (Monoid.lawAssoc monoid x y ε)) (m >>= (λ x → f x >>= (return ∘ g))) ⟩
      subst₂ M (trans (sym (Monoid.lawAssoc monoid x y ε)) (Monoid.lawIdR monoid (x ∙ y))) refl (m >>= (λ x → f x >>= (return ∘ g)))
        ≡⟨ shiftSubstHelp1 (Monoid.lawIdR monoid y) (trans (sym (Monoid.lawAssoc monoid x y ε)) (Monoid.lawIdR monoid (x ∙ y))) m (λ x → f x >>= (return ∘ g)) ⟩
      m >>= (λ x → subst₂ M (Monoid.lawIdR monoid y) refl (f x >>= (return ∘ g))) ∎
    
    
    [xε]y≡xy : {x y : Monoid.carrier monoid} → (x ∙ ε) ∙ y ≡ x ∙ y
    [xε]y≡xy {x = x} {y = y} = cong (λ X → X ∙ y) (Monoid.lawIdR monoid x)
    
    [xε]y≡x[εy] : {x y : Monoid.carrier monoid} → (x ∙ ε) ∙ y ≡ x ∙ (ε ∙ y)
    [xε]y≡x[εy] {x = x} {y = y} = Monoid.lawAssoc monoid x ε y
    
    εx≡x : {x : Monoid.carrier monoid} → ε ∙ x ≡ x
    εx≡x {x = x} = Monoid.lawIdL monoid x
    
    shiftSubstHelp3 : ∀ {α β : Type} {e e₁ e₂ m : Monoid.carrier monoid}
                    → (eqInner : e₁ ∙ e₂ ≡ m)
                    → (eqOuter : e ∙ (e₁ ∙ e₂) ≡ e ∙ m)
                    → (ma : ⟨ EffMonadTC e ⟩ α) → (f : α → ⟨ EffMonadTC m ⟩ β)
                    → subst₂ M (sym eqOuter) refl (ma >>= f) ≡ ma >>= (λ x → (subst₂ M (sym eqInner) refl (f x)))
    shiftSubstHelp3 refl refl ma f = refl

    lawDecomposeFmapIntro : {α β γ : Type} 
                          → (M N : TyCons)
                          → (b : Binds M N)
                          → (m : ⟨ M ⟩ α) → (f : α → β) → (g : β → ⟨ N ⟩ γ)
                          → bind b m (g ∘ f) ≡ bind b (fmap (functor M) f m) g
    lawDecomposeFmapIntro {γ = γ} (EffMonadTC x) (EffMonadTC y) (lift tt) m f g = begin 
      m >>= (g ∘ f) 
        ≡⟨ sym (subst₂²≡id1 (trans (sym [xε]y≡x[εy]) [xε]y≡xy) refl M (m >>= (g ∘ f))) ⟩
      subst₂ M (trans (sym [xε]y≡x[εy]) [xε]y≡xy) refl (subst₂ M (sym (trans (sym [xε]y≡x[εy]) [xε]y≡xy)) refl (m >>= (g ∘ f)))
        ≡⟨ sym (helpSubstTrans [xε]y≡xy (sym [xε]y≡x[εy]) (subst₂ M (sym (trans (sym [xε]y≡x[εy]) [xε]y≡xy)) refl (m >>= (g ∘ f)))) ⟩
      subst₂ M [xε]y≡xy refl 
             (subst₂ M (sym [xε]y≡x[εy]) refl 
                     (subst₂ M (sym (trans (sym [xε]y≡x[εy]) [xε]y≡xy)) refl (m >>= (g ∘ f))))
        ≡⟨ cong (λ X → subst₂ M [xε]y≡xy refl (subst₂ M (sym [xε]y≡x[εy]) refl X)) (shiftSubstHelp3 εx≡x (trans (sym [xε]y≡x[εy]) [xε]y≡xy) m (g ∘ f)) ⟩
      subst₂ M [xε]y≡xy refl 
             (subst₂ M (sym [xε]y≡x[εy]) refl 
                     (m >>= (λ x → subst₂ M (sym εx≡x) refl (g (f x)))))
        ≡⟨ cong (λ X → subst₂ M [xε]y≡xy refl (subst₂ M (sym [xε]y≡x[εy]) refl (m >>= X))) (funExt (λ x → sym (helpSubst1 (sym εx≡x) (g (f x))))) ⟩
      subst₂ M [xε]y≡xy refl 
             (subst₂ M (sym [xε]y≡x[εy]) refl 
                     (m >>= (λ x → subst (λ X → ⟨ X ⟩ γ) (liftMonLaw (sym εx≡x)) (g (f x)))))
        ≡⟨ cong (λ X → subst₂ M [xε]y≡xy refl (subst₂ M (sym [xε]y≡x[εy]) refl (m >>= X))) 
                (funExt (λ x → cong (λ X → subst (λ X → ⟨ X ⟩ γ) X (g (f x))) (proof-irrelevance (liftMonLaw (sym εx≡x)) (sym (liftMonLaw εx≡x))))) ⟩
      subst₂ M [xε]y≡xy refl 
             (subst₂ M (sym [xε]y≡x[εy]) refl 
                     (m >>= (λ x → subst (λ X → ⟨ X ⟩ γ) (sym (liftMonLaw εx≡x)) (g (f x)))))
        ≡⟨ cong (λ X → subst₂ M [xε]y≡xy refl (subst₂ M (sym [xε]y≡x[εy]) refl (m >>= X))) 
                (funExt (λ x → cong (λ X → subst (λ X → ⟨ X ⟩ γ) (sym (liftMonLaw εx≡x)) X) 
                                    (sym (SuperMonad.lawIdR supermonad (EffMonadTC y) (EffMonadTC ε) (liftMonLaw εx≡x) (lift tt) refl (f x) g)))) ⟩
      subst₂ M [xε]y≡xy refl 
             (subst₂ M (sym [xε]y≡x[εy]) refl 
                     (m >>= (λ x → subst (λ X → ⟨ X ⟩ γ) (sym (liftMonLaw εx≡x)) (subst (λ X → ⟨ X ⟩ γ) (liftMonLaw εx≡x) (return (f x) >>= g)))))
        ≡⟨ cong (λ X → subst₂ M [xε]y≡xy refl (subst₂ M (sym [xε]y≡x[εy]) refl (m >>= X))) 
                (funExt (λ x → subst²≡id' (liftMonLaw εx≡x) (λ X → ⟨ X ⟩ γ) ((return (f x) >>= g)))) ⟩
      subst₂ M [xε]y≡xy refl (subst₂ M (sym [xε]y≡x[εy]) refl (m >>= (λ x → return (f x) >>= g)))
        ≡⟨ cong (λ X → subst₂ M [xε]y≡xy refl X) (sym (helpSubst1 (sym (Monoid.lawAssoc monoid x ε y)) (m >>= (λ x → return (f x) >>= g)))) ⟩
      subst₂ M [xε]y≡xy refl (subst (λ X → ⟨ X ⟩ γ) (liftMonLaw (sym (Monoid.lawAssoc monoid x ε y))) (m >>= (λ x → return (f x) >>= g)))
        ≡⟨ cong (λ X → subst₂ M [xε]y≡xy refl X) 
                (SuperMonad.lawAssoc supermonad (EffMonadTC x) (EffMonadTC ε) (EffMonadTC y) 
                                     (liftMonLaw (sym [xε]y≡x[εy])) 
                                     (lift tt) (lift tt) (lift tt) (lift tt) 
                                     m (return ∘ f) g) ⟩
      subst₂ M [xε]y≡xy refl ((m >>= (return ∘ f)) >>= g)
        ≡⟨ shiftSubstHelp2 (Monoid.lawIdR monoid x) [xε]y≡xy ((m >>= (return ∘ f))) g ⟩
      (subst₂ M (Monoid.lawIdR monoid x) refl (m >>= (return ∘ f))) >>= g ∎

-}
