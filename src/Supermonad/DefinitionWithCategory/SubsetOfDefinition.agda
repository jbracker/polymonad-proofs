 
module Supermonad.DefinitionWithCategory.SubsetOfDefinition where

-- Stdlib
open import Level
open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Agda.Primitive
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Data.Nat hiding ( _⊔_ )
open import Data.Vec hiding ( _>>=_ )
open import Data.List hiding ( sequence )
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning


open import Utilities
open import Haskell
open import Haskell.Constrained.ConstrainedFunctor
open import Theory.Category
open import Supermonad.Definition
open import Supermonad.DefinitionWithCategory

open Category renaming ( left-id to catIdL ; right-id to catIdR ; assoc to catAssoc ; _∘_ to comp )

SupermonadC→Supermonad : {ℓ₀ ℓ₁ : Level} {C : Category {ℓ₀} {ℓ₁}} {F : ∀ {a b} → Hom C a b → Type → Type}
                       → UniqueIdHomomorphisms C
                       → SupermonadC {ℓ₀} {ℓ₁} {ℓ₀ ⊔ ℓ₁} C F → Supermonad (∃ λ a → ∃ λ b → Hom C a b)
SupermonadC→Supermonad {ℓ₀} {ℓ₁} {C = C} {F = F} uniqueHom smc = record
  { ⟨_⟩ = ⟨_⟩
  ; Binds = Binds
  ; Returns = Returns
  ; functor = functor
  ; tyConArity = 1
  ; tyConArgTys = HomIx ∷ []
  ; tyCon = tyCon
  ; bind = bind
  ; return = return
  ; lawSingleTyCon = lawSingleTyCon
  ; lawUniqueBind = λ {α} {β} → lawUniqueBind {α} {β}
  ; lawUniqueReturn = λ {α} {M} → lawUniqueReturn {α} {M}
  ; lawIdR = lawIdR
  ; lawIdL = lawIdL
  ; lawAssoc = lawAssoc
  ; lawMonadFmap = lawMonadFmap
  }
  where
    _∘_ = comp C
    
    HomIx : Set (ℓ₁ ⊔ ℓ₀)
    HomIx = ∃ λ a → ∃ λ b → Hom C a b
    
    ⟨_⟩ : HomIx → TyCon
    ⟨_⟩ (a , b , f) = F f

    tyCon : HomIx → Lift {ℓ = lsuc (ℓ₀ ⊔ ℓ₁)} TyCon
    tyCon (a , b , f) = lift (F f)
    
    Binds : HomIx → HomIx → HomIx → Type → Type → Set (ℓ₁ ⊔ ℓ₀)
    Binds (a , b , f) (b' , c , g) (a' , c' , h) α β = Lift {ℓ = ℓ₁} $ 
      ∃ λ (eqA : a' ≡ a) → 
      ∃ λ (eqB : b ≡ b') → 
      ∃ λ (eqC : c' ≡ c) → 
          (g ∘ subst (Hom C a) eqB f) ≡ (subst₂ (Hom C) eqA eqC h)
    
    Returns : HomIx → Type → Set (ℓ₁ ⊔ ℓ₀)
    Returns (a , a' , f) α = Lift {ℓ = ℓ₁} (a ≡ a')
    
    _>>=_ = SupermonadC.bind smc
    ret = SupermonadC.return smc
    
    bind : {α β : Type} {M N P : HomIx} → Binds M N P α β 
         → ⟨ M ⟩ α → (α → ⟨ N ⟩ β) → ⟨ P ⟩ β
    bind {M = a , b , f} {.b , c , g} {.a , .c , .(g ∘ f)} (lift (refl , refl , refl , refl)) = _>>=_
    
    return : {α : Type} {M : HomIx} → Returns M α 
           → α → ⟨ M ⟩ α
    return {M = a , .a , f} (lift refl) with uniqueHom f
    return {α} {a , .a , .(id C {a})} (lift refl) | refl = ret
    
    bindReplace : {α β : Type} {a b c : Obj C} 
                → {f : Hom C a b} {g : Hom C b c} {h : Hom C a c}
                → (eq : g ∘ f ≡ h)
                → (b : Binds (a , b , f) (b , c , g) (a , c , h) α β)
                → (m : F f α) (k : α → F g β)
                → bind b m k ≡ subst (λ X → F X β) eq (m >>= k) 
    bindReplace refl (lift (refl , refl , refl , refl)) m k = refl
    
    functor : (M : HomIx) → ConstrainedFunctor (F (proj₂ (proj₂ M)))
    functor (a , b , f) = record 
      { FunctorCts = ConstrainedFunctor.FunctorCts (SupermonadC.functor smc f)
      ; fmap = ConstrainedFunctor.fmap (SupermonadC.functor smc f)
      ; lawId = ConstrainedFunctor.lawId (SupermonadC.functor smc f)
      ; lawCompose = ConstrainedFunctor.lawCompose (SupermonadC.functor smc f)
      }
    
    fmap :  (M : HomIx) → {α β : Type} → ConstrainedFunctor.FunctorCts (functor M) α β → ( (α → β) → (F (proj₂ (proj₂ M)) α → F (proj₂ (proj₂ M)) β) )
    fmap (a , b , f) = ConstrainedFunctor.fmap (SupermonadC.functor smc f)
    
    lawMonadFmap : {α β : Type} (M N : HomIx)
                 → (fcts : ConstrainedFunctor.FunctorCts (functor M) α β)
                 → (b : Binds M N M α β) (r : Returns N β) 
                 → (k : α → β) (m : ⟨ M ⟩ α) 
                 → bind b m ((return r) ∘F k) ≡ fmap M fcts k m
    lawMonadFmap {α} {β} (a , b , f) (.b , .b , g) fcts (lift (refl , refl , refl , g∘f≡f)) (lift refl) k m with uniqueHom g
    lawMonadFmap {α} {β} (a , b , f) (.b , .b , .(id C {b})) fcts (lift (refl , refl , refl , g∘f≡f)) (lift refl) k m | refl = begin
      bind (lift (refl , refl , refl , g∘f≡f)) m (ret ∘F k)
        ≡⟨ cong (λ X → bind (lift (refl , refl , refl , X)) m (ret ∘F k)) (proof-irrelevance g∘f≡f (catIdR C {f = f})) ⟩
      bind (lift (refl , refl , refl , catIdR C {f = f})) m (ret ∘F k)
        ≡⟨ bindReplace (catIdR C {f = f}) (lift (refl , refl , refl , catIdR C {f = f})) m (ret ∘F k) ⟩
      subst (λ X → F X β) (catIdR C {f = f}) (m >>= (ret ∘F k)) 
        ≡⟨ SupermonadC.monadFmap smc fcts m k ⟩
      ConstrainedFunctor.fmap (SupermonadC.functor smc f) fcts k m
        ≡⟨ refl ⟩
      fmap (a , b , f) fcts k m ∎
    
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
    lawIdR {α} {β} (a , .a , f) (.a , b , g) (lift (refl , refl , refl , f∘g≡g)) (lift refl) x k with uniqueHom f
    lawIdR {α} {β} (a , .a , .(id C {a})) (.a , b , g) (lift (refl , refl , refl , f∘g≡g)) (lift refl) x k | refl = begin
      bind (lift (refl , refl , refl , f∘g≡g)) (ret x) k
        ≡⟨ bindReplace f∘g≡g (lift (refl , refl , refl , f∘g≡g)) (ret x) k ⟩
      subst (λ X → F X β) f∘g≡g (ret x >>= k)
        ≡⟨ cong (λ Y → subst (λ X → F X β) Y (ret x >>= k)) (proof-irrelevance f∘g≡g (catIdL C {f = g})) ⟩
      subst (λ X → F X β) (catIdL C {f = g}) (ret x >>= k)
        ≡⟨ SupermonadC.right-id smc x k ⟩
      k x ∎
    
    lawIdL : {α : Type} 
           → (M N : HomIx)
           → (b : Binds M N M α α) → (r : Returns N α)
           → (m : ⟨ M ⟩ α) 
           → bind b m (return r) ≡ m
    lawIdL {α} (a , b , f) (.b , .b , g) (lift (refl , refl , refl , g∘f≡f)) (lift refl) m with uniqueHom g
    lawIdL {α} (a , b , f) (.b , .b , .(id C {b})) (lift (refl , refl , refl , g∘f≡f)) (lift refl) m | refl = begin
      bind (lift (refl , refl , refl , g∘f≡f)) m ret 
        ≡⟨ bindReplace g∘f≡f (lift (refl , refl , refl , g∘f≡f)) m ret ⟩
      subst (λ X → F X α) g∘f≡f (m >>= ret) 
        ≡⟨ cong (λ Y → subst (λ X → F X α) Y (m >>= ret)) (proof-irrelevance g∘f≡f (catIdR C {f = f})) ⟩
      subst (λ X → F X α) (catIdR C {f = f}) (m >>= ret) 
        ≡⟨ SupermonadC.left-id smc m ⟩
      m ∎
    
    lawAssoc : {α β γ : Type} 
             → (M N P S T : HomIx)
             → (b₁ : Binds M N P α γ) → (b₂ : Binds S T N β γ)
             → (b₃ : Binds N T P β γ) → (b₄ : Binds M S N α β) 
             → (m : ⟨ M ⟩ α) → (f : α → ⟨ S ⟩ β) → (g : β → ⟨ T ⟩ γ)
             → bind b₁ m (λ x → bind b₂ (f x) g) ≡ bind b₃ (bind b₄ m f) g
    lawAssoc {α} {β} {γ} (a1 , .a1 , f1) (.a1 , b2 , .(f5 ∘ f4)) (.a1 , .b2 , .((f5 ∘ f4) ∘ f1)) (.a1 , .b2 , f4) (.b2 , .b2 , f5) 
             (lift (refl , refl , refl , refl)) (lift (refl , refl , refl , refl)) (lift (refl , refl , refl , f4∘f1≡f5∘f4)) (lift (refl , refl , refl , f5∘f5∘f4≡f5∘f4∘f1))
             m k l with uniqueHom f1 | uniqueHom f5
    lawAssoc {α} {β} {γ} (a1 , .a1 , .(id C {a = a1})) (.a1 , b2 , .(id C {a = b2} ∘ f4)) (.a1 , .b2 , .((id C {a = b2} ∘ f4) ∘ id C {a = a1})) (.a1 , .b2 , f4) (.b2 , .b2 , .(id C {a = b2})) 
             (lift (refl , refl , refl , refl)) (lift (refl , refl , refl , refl)) (lift (refl , refl , refl , f5∘f5∘f4≡f5∘f4∘f1)) (lift (refl , refl , refl , f4∘f1≡f5∘f4))
             m k l | refl | refl = begin
      m >>= (λ x → k x >>= l)
        ≡⟨ sym (SupermonadC.assoc smc m k l) ⟩
      subst (λ X → F X γ) (catAssoc C) ((m >>= k) >>= l)
        ≡⟨ cong (λ Y → subst (λ X → F X γ) Y ((m >>= k) >>= l)) (proof-irrelevance (catAssoc C) (trans (cong (_∘_ (id C {b2})) f4∘f1≡f5∘f4) f5∘f5∘f4≡f5∘f4∘f1)) ⟩
      subst (λ X → F X γ) (trans (cong (_∘_ (id C {b2})) f4∘f1≡f5∘f4) f5∘f5∘f4≡f5∘f4∘f1) ((m >>= k) >>= l)
        ≡⟨ sym (substTrans (cong (_∘_ (id C {b2})) f4∘f1≡f5∘f4) f5∘f5∘f4≡f5∘f4∘f1 (λ Z → F Z γ) ((m >>= k) >>= l)) ⟩
      subst (λ X → F X γ) f5∘f5∘f4≡f5∘f4∘f1 (subst (λ X → F X γ) (cong (_∘_ (id C {b2})) f4∘f1≡f5∘f4) ((m >>= k) >>= l))
        ≡⟨ cong (λ Y → subst (λ X → F X γ) f5∘f5∘f4≡f5∘f4∘f1 Y) (sym (help (m >>= k) l f4∘f1≡f5∘f4)) ⟩
      subst (λ X → F X γ) f5∘f5∘f4≡f5∘f4∘f1 ((subst (λ X → F X β) f4∘f1≡f5∘f4 (m >>= k)) >>= l)
        ≡⟨ cong (λ Y → subst (λ X → F X γ) f5∘f5∘f4≡f5∘f4∘f1 (Y >>= l)) (sym (bindReplace f4∘f1≡f5∘f4 (lift (refl , refl , refl , f4∘f1≡f5∘f4)) m k)) ⟩
      subst (λ X → F X γ) f5∘f5∘f4≡f5∘f4∘f1 ((bind (lift (refl , refl , refl , f4∘f1≡f5∘f4)) m k) >>= l)
        ≡⟨ sym (bindReplace f5∘f5∘f4≡f5∘f4∘f1 (lift (refl , refl , refl , f5∘f5∘f4≡f5∘f4∘f1)) (bind (lift (refl , refl , refl , f4∘f1≡f5∘f4)) m k) l) ⟩
      bind (lift (refl , refl , refl , f5∘f5∘f4≡f5∘f4∘f1)) (bind (lift (refl , refl , refl , f4∘f1≡f5∘f4)) m k) l ∎
      where
        help : {α β : Type} {a b c : Obj C} {f g : Hom C a b} {h : Hom C b c}
             → (m : F f α) → (k : α → F h β)
             → (eq : f ≡ g)
             → ((subst (λ X → F X α) eq m) >>= k) ≡ subst (λ X → F X β) (cong (_∘_ h) eq) (m >>= k)
        help m k refl = refl
