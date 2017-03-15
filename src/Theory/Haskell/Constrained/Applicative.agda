
open import Level
open import Function hiding ( id ) renaming ( _∘_ to _∘F_ )

open import Data.Unit
open import Data.Product

open import Relation.Binary.PropositionalEquality

open import Theory.Category
open import Theory.Category.Closed
open import Theory.Category.Closed.Examples
open import Theory.Category.Dependent
open import Theory.Category.Examples

open import Theory.Functor
open import Theory.Functor.Closed

open import Theory.Haskell.Constrained.Functor

module Theory.Haskell.Constrained.Applicative where

private
  Hask : {ℓ : Level} → ClosedCategory (setCategory {ℓ})
  Hask {ℓ} = setClosedCategory {ℓ}

record ConstrainedApplicative {ℓ ℓ₀ ℓ₁ : Level} (F : ConstrainedFunctor {ℓ} {ℓ₀} {ℓ₁}) : Set {!!} where
  
  open ConstrainedFunctor F
  open DependentCategory Cts
  open Category

  private
    _∘DepCat_ = _∘_ DepCat
    _∘DC×DC_ = _∘_ (DepCat op ×C DepCat)
  
  field
    CtInternal₀ : {A B : Set ℓ} → DepObj A → DepObj B → DepObj (A → B)
    
    CtInternal₁ : {A B C D : Set ℓ}
                → (ctA : DepObj A) (ctB : DepObj B) (ctC : DepObj C) (ctD : DepObj D)
                → (f : C → A) (g : B → D)
                → DepHom (CtInternal₀ {A} {B} ctA ctB) (CtInternal₀ {C} {D} ctC ctD) (λ h → g ∘F h ∘F f)

    ct-internal-id : {A B : Set ℓ}
                   → (ctA : DepObj A) (ctB : DepObj B)
                   → CtInternal₁ ctA ctB ctA ctB (λ x → x) (λ x → x) ≡ depId
    
    CtI : DepObj (Lift ⊤)
  
  open ≡-Reasoning
  
  CtInternalHom : Functor ((DepCat op) ×C DepCat) DepCat
  CtInternalHom = functor InternalF₀ InternalF₁ internal-id (λ {a} {b} {c} {f} {g} → internal-compose {a} {b} {c} {f} {g})
    where
      InternalF₀ : Obj ((DepCat op) ×C DepCat) → Obj DepCat
      InternalF₀ ((A , ctA) , (B , ctB)) = (A → B) , CtInternal₀ {A} {B} ctA ctB
      
      InternalF₁ : {a b : Obj ((DepCat op) ×C DepCat)} 
                 → Hom ((DepCat op) ×C DepCat) a b → Hom DepCat (InternalF₀ a) (InternalF₀ b)
      InternalF₁ {(A , ctA) , (B , ctB)} {(C , ctC) , (D , ctD)} ((f , ct-f) , (g , ct-g))
        = (λ h → g ∘F h ∘F f) , CtInternal₁ {A} {B} {C} {D} ctA ctB ctC ctD f g
      
      internal-id : {a : Obj ((DepCat op) ×C DepCat)} → InternalF₁ {a} {a} (id ((DepCat op) ×C DepCat)) ≡ id DepCat
      internal-id {(A , ctA) , (B , ctB)} = cong (_,_ (λ x → x)) (ct-internal-id ctA ctB)
      
      internal-compose : {a b c : Obj ((DepCat op) ×C DepCat)}
                       → {f : Hom ((DepCat op) ×C DepCat) a b} {g : Hom ((DepCat op) ×C DepCat) b c}
                       → InternalF₁ (g ∘DC×DC f) ≡ InternalF₁ g ∘DepCat InternalF₁ f
      internal-compose {a} {b} {c} {f} {g} = {!!}
      
  CtClosedCategory : ClosedCategory DepCat 
  CtClosedCategory = record
    { InternalHom = CtInternalHom
    ; I = Lift ⊤ , CtI
    ; i-natural-isomorphism = {!!}
    ; j = {!!}
    ; L = {!!}
    ; γ-inv = {!!}
    ; j-extranatural-a = {!!}
    ; L-natural-c = {!!}
    ; L-natural-b = {!!}
    ; L-extranatural-a = {!!}
    ; coher-1 = {!!}
    ; coher-2 = {!!}
    ; coher-3 = {!!}
    ; coher-4 = {!!}
    ; γ-right-id = {!!}
    ; γ-left-id = {!!}
    }
  
  
  CtApplicative : ClosedFunctor CtClosedCategory (Hask {ℓ})
  CtApplicative = record 
    { lax-closed-functor = record
      { F = CtFunctor
      ; F̂ = {!!}
      ; F⁰ = {!!}
      ; F̂-natural-x = {!!}
      ; F̂-natural-y = {!!}
      ; coher-1 = {!!}
      ; coher-2 = {!!}
      ; coher-3 = {!!}
      }
    ; F̂-iso = {!!}
    ; F⁰-iso = {!!}
    }
