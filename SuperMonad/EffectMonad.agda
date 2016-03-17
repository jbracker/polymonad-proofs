
module SuperMonad.EffectMonad where

-- Stdlib
open import Level
open import Function
open import Agda.Primitive
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
open import Functor
open import Polymonad
open import Parameterized.EffectMonad
open import SuperMonad.Definition

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
  ; _◆_ = _◆_
  ; bind = bind
  ; return = return
  ; lawIdR = lawIdR
  ; lawIdL = lawIdL
  ; lawAssoc = lawAssoc
  } where
    TyCons = EffMonadTyCons Effect

    _∙_ = Monoid._∙_ monoid
    ε = Monoid.ε monoid
    
    ⟨_⟩ : TyCons → TyCon
    ⟨_⟩ (EffMonadTC e) = M e
    
    Binds : TyCons → TyCons → Set n
    Binds (EffMonadTC m) (EffMonadTC n) = Lift ⊤
    
    Returns : TyCons → Set n
    Returns (EffMonadTC m) = m ≡ ε
    
    _◆_ : TyCons → TyCons → TyCons
    EffMonadTC m ◆ EffMonadTC n = EffMonadTC (m ∙ n)
    
    _>>=_ = EffectMonad._>>=_ monad
    return' = EffectMonad.return monad
    
    bind : {M N : TyCons} → Binds M N → [ ⟨ M ⟩ , ⟨ N ⟩ ]▷ ⟨ M ◆ N ⟩
    bind {M = EffMonadTC m} {N = EffMonadTC n} (lift tt) = _>>=_
    
    return : ∀ {α : Type} → {M : TyCons} → Returns M → α → ⟨ M ⟩ α
    return {M = EffMonadTC ._} refl = return'
    
    fmap : ∀ {m : Monoid.carrier monoid} {α β : Type} → (α → β) → M m α → M m β
    fmap {m = m} {β = β} f ma = subst₂ M (Monoid.lawIdR monoid m) refl (ma >>= (return' ∘ f))
    
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

    lawIdR : ∀ {α β : Type} 
           → (M N : TyCons)
           → (N◆M≡M : N ◆ M ≡ M )
           → (b : Binds N M) → (r : Returns N)
           → (a : α) → (k : α → ⟨ M ⟩ β)
           → subst (λ X → ⟨ X ⟩ β) N◆M≡M (bind b (return r a) k) ≡ k a
    lawIdR {α = α} {β = β} (EffMonadTC e) (EffMonadTC ._) N◆M≡M (lift tt) refl a k = begin
      subst (λ X → ⟨ X ⟩ β) N◆M≡M (return' a >>= k) 
        ≡⟨ cong (λ X → subst (λ Y → ⟨ Y ⟩ β) N◆M≡M X) (EffectMonad.lawIdL monad a k) ⟩
      subst (λ X → ⟨ X ⟩ β) N◆M≡M (subst₂ M (sym (Monoid.lawIdL monoid e)) refl (k a)) 
        ≡⟨ cong (λ X → subst (λ Y → ⟨ Y ⟩ β) N◆M≡M X) (helpSubst1 e N◆M≡M (k a)) ⟩
      subst (λ X → ⟨ X ⟩ β) N◆M≡M (subst (λ X → ⟨ X ⟩ β) (sym N◆M≡M) (k a)) 
        ≡⟨ subst²≡id N◆M≡M (λ X → ⟨ X ⟩ β) (k a) ⟩
      k a ∎
    
    lawIdL : ∀ {α : Type} 
           → (M N : TyCons)
           → (M◆N≡M : M ◆ N ≡ M)
           → (b : Binds M N) → (r : Returns N)
           → (m : ⟨ M ⟩ α)
           → subst (λ X → ⟨ X ⟩ α) M◆N≡M (bind b m (return r)) ≡ m
    lawIdL {α = α} (EffMonadTC e) (EffMonadTC ._) M◆N≡M (lift tt) refl m = begin
      subst (λ X → ⟨ X ⟩ α) M◆N≡M (m >>= return')
        ≡⟨ cong (λ X → subst (λ Y → ⟨ Y ⟩ α) M◆N≡M X) (EffectMonad.lawIdR monad m) ⟩
      subst (λ X → ⟨ X ⟩ α) M◆N≡M (subst₂ M (sym (Monoid.lawIdR monoid e)) refl m)
        ≡⟨ cong (λ X → subst (λ Y → ⟨ Y ⟩ α) M◆N≡M X) (helpSubst2 e M◆N≡M m) ⟩
      subst (λ X → ⟨ X ⟩ α) M◆N≡M (subst (λ X → ⟨ X ⟩ α) (sym M◆N≡M) m)
        ≡⟨ subst²≡id M◆N≡M (λ X → ⟨ X ⟩ α) m ⟩
      m ∎

    lawAssoc : ∀ {α β γ : Type} 
             → (M N P : TyCons)
             → (assoc : M ◆ (N ◆ P) ≡ (M ◆ N) ◆ P) 
             → (b₁ : Binds M (N ◆ P)) → (b₂ : Binds N P)
             → (b₃ : Binds (M ◆ N) P) → (b₄ : Binds M N)
             → (m : ⟨ M ⟩ α) → (f : α → ⟨ N ⟩ β) → (g : β → ⟨ P ⟩ γ)
             → subst (λ X → ⟨ X ⟩ γ) assoc (bind b₁ m (λ x → bind b₂ (f x) g)) 
               ≡ bind b₃ (bind b₄ m f) g
    lawAssoc {γ = γ} (EffMonadTC e₁) (EffMonadTC e₂) (EffMonadTC e₃) assoc (lift tt) (lift tt) (lift tt) (lift tt) m f g = begin 
      subst (λ X → ⟨ X ⟩ γ) assoc (m >>= (λ x → f x >>= g))
        ≡⟨ cong (λ X → subst (λ Y → ⟨ Y ⟩ γ) assoc X) (EffectMonad.lawAssoc monad m f g) ⟩
      subst (λ X → ⟨ X ⟩ γ) assoc (subst₂ M (Monoid.lawAssoc monoid e₁ e₂ e₃) refl ((m >>= f) >>= g))
        ≡⟨ cong (λ X → subst (λ Y → ⟨ Y ⟩ γ) assoc X) (helpSubst3 e₁ e₂ e₃ assoc (((m >>= f) >>= g))) ⟩
      subst (λ X → ⟨ X ⟩ γ) assoc (subst (λ X → ⟨ X ⟩ γ) (sym assoc) ((m >>= f) >>= g))
        ≡⟨ subst²≡id assoc (λ X → ⟨ X ⟩ γ) (((m >>= f) >>= g)) ⟩
      (m >>= f) >>= g ∎
    
    functor : (M : TyCons) → Functor ⟨ M ⟩
    functor (EffMonadTC m) = record 
      { fmap = fmap
      ; lawId = lawId
      ; lawDist = lawDist
      } where
        lawId : ∀ {α : Type} → fmap {α = α} identity ≡ identity
        lawId {α = α} = funExt (λ ma → begin
          fmap identity ma 
            ≡⟨ refl ⟩
          subst₂ M (Monoid.lawIdR monoid m) refl (ma >>= return')
            ≡⟨ cong (λ X → subst₂ M (Monoid.lawIdR monoid m) refl X) (sym (subst²≡id' (Me◆Mε≡Me m) (λ X → ⟨ X ⟩ α) (ma >>= return'))) ⟩
          subst₂ M (Monoid.lawIdR monoid m) refl (subst (λ X → ⟨ X ⟩ α) (sym (Me◆Mε≡Me m)) (subst (λ X → ⟨ X ⟩ α) (Me◆Mε≡Me m) (ma >>= return') ) )
            ≡⟨ cong (λ X → subst₂ M (Monoid.lawIdR monoid m) refl (subst (λ X → ⟨ X ⟩ α) (sym (Me◆Mε≡Me m)) X )) (lawIdL (EffMonadTC m) (EffMonadTC ε) (Me◆Mε≡Me m) (lift tt) refl ma) ⟩
          subst₂ M (Monoid.lawIdR monoid m) refl (subst (λ X → ⟨ X ⟩ α) (sym (Me◆Mε≡Me m)) ma)
            ≡⟨ helpSubst4 m (Me◆Mε≡Me m) (subst (λ X → ⟨ X ⟩ α) (sym (Me◆Mε≡Me m)) ma) ⟩
          subst (λ X → ⟨ X ⟩ α) (Me◆Mε≡Me m) (subst (λ X → ⟨ X ⟩ α) (sym (Me◆Mε≡Me m)) ma)
            ≡⟨ subst²≡id (Me◆Mε≡Me m) (λ X → ⟨ X ⟩ α) ma ⟩
          identity ma ∎)

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
        
        shiftSubstHelp3 : ∀ {γ : Type} {e₁ e₂ : Monoid.carrier monoid}
                        → (ma : ⟨ EffMonadTC e₁ ⟩ γ)
                        → (eq1 : EffMonadTC e₁ ≡ EffMonadTC e₂ )
                        → (eq2 : e₁ ≡ e₂)
                        → subst (λ X → ⟨ X ⟩ γ) eq1 ma ≡ subst₂ M eq2 refl ma
        shiftSubstHelp3 ma refl refl = refl

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
        lawDist {β = β} {γ = γ} f g = funExt (λ ma → begin 
          fmap (f ∘ g) ma
            ≡⟨ refl ⟩
          subst₂ M (Monoid.lawIdR monoid m) refl (ma >>= (λ x → return' (f (g x))))
            ≡⟨ cong (λ X → subst₂ M (Monoid.lawIdR monoid m) refl (ma >>= X)) (funExt (λ x → sym (lawIdR (EffMonadTC ε) (EffMonadTC ε) (Mε◆Me≡Me ε) (lift tt) refl (g x) (return' ∘ f)))) ⟩
          subst₂ M (Monoid.lawIdR monoid m) refl (ma >>= (λ x → subst (λ X → ⟨ X ⟩ γ) (Mε◆Me≡Me ε) (return' (g x) >>= (return' ∘ f))))
            ≡⟨ cong (λ X → subst₂ M (Monoid.lawIdR monoid m) refl X) (shiftSubstHelp1 (Mε◆Me≡Me ε) Meεε≡Meε ma (λ x → return' (g x) >>= (return' ∘ f))) ⟩
          subst₂ M (Monoid.lawIdR monoid m) refl (subst (λ X → ⟨ X ⟩ γ) Meεε≡Meε (ma >>= (λ x → return' (g x) >>= (return' ∘ f))))
            ≡⟨ cong (λ X → subst₂ M (Monoid.lawIdR monoid m) refl (subst (λ X → ⟨ X ⟩ γ) Meεε≡Meε X)) 
                    (sym (subst²≡id' assoc (λ X → ⟨ X ⟩ γ) (ma >>= (λ x → return' (g x) >>= (return' ∘ f))))) ⟩
          subst₂ M (Monoid.lawIdR monoid m) refl (subst (λ X → ⟨ X ⟩ γ) Meεε≡Meε (subst (λ X → ⟨ X ⟩ γ) (sym assoc) (subst (λ X → ⟨ X ⟩ γ) assoc (ma >>= (λ x → return' (g x) >>= (return' ∘ f))))))
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
          (fmap f ∘ fmap g) ma ∎)

