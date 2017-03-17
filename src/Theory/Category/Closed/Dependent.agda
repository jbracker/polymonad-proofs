
open import Level
open import Function hiding ( id ) renaming ( _∘_ to _∘F_ )

open import Data.Unit
open import Data.Product renaming ( _,_ to _,'_ )

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality

open import Equality

open import Theory.Category
open import Theory.Category.Closed
open import Theory.Category.Dependent

open import Theory.Functor

module Theory.Category.Closed.Dependent where 

record DependentClosedCategory {ℓ₀ ℓ₁ : Level} {C : Category {ℓ₀} {ℓ₁}} (CC : ClosedCategory C) : Set {!!} where
  
  field 
    DC : DependentCategory C
  
  open DependentCategory DC
  open ClosedCategory CC hiding ( _∘_ ; Obj ; Hom ; id )
  open Category
  
  private
    _∘C_ = _∘_ C
    _∘Cop_ = _∘_ (C op)
    _∘DC_ = _∘_ DepCat
    _∘DC×DC_ = _∘_ (DepCat op ×C DepCat)
  
  field
    DepInternal₀ : {a b : Obj C} → DepObj a → DepObj b → DepObj [ a , b ]₀
    
    DepInternal₁ : {a b c d : Obj C}
                 → (a' : DepObj a) (b' : DepObj b) (c' : DepObj c) (d' : DepObj d)
                 → (f : Hom (C op) a b) (g : Hom C c d)
                 → DepHom (DepInternal₀ {a} {c} a' c') (DepInternal₀ {b} {d} b' d') [ f , g ]₁

    dep-internal-id : {a b : Obj C}
                    → (a' : DepObj a) (b' : DepObj b)
                    → DepInternal₁ a' a' b' b' (id (C op)) (id C) ≅ depId {[ a , b ]₀} {DepInternal₀ a' b'}
    
    dep-internal-compose : {a b c d e x : Obj C}
                         → (a' : DepObj a) (b' : DepObj b) (c' : DepObj c) (d' : DepObj d) (e' : DepObj e) (x' : DepObj x)
                         → (f : Hom (C op) a c) (g : Hom C b d) (h : Hom (C op) c e) (k : Hom C d x)
                         → DepInternal₁ a' e' b' x' (h ∘Cop f) (k ∘C g)
                         ≅ DepInternal₁ c' e' d' x' h k ∘dep DepInternal₁ a' c' b' d' f g
    
    CtI : DepObj I
  
  open ≡-Reasoning
  
  DepInternalHom : Functor ((DepCat op) ×C DepCat) DepCat
  DepInternalHom = functor InternalF₀ InternalF₁ internal-id (λ {a} {b} {c} {f} {g} → internal-compose {a} {b} {c} {f} {g})
    where
      InternalF₀ : Obj ((DepCat op) ×C DepCat) → Obj DepCat
      InternalF₀ ((a ,' ctA) ,' (b ,' ctB)) = [ a , b ]₀ ,' DepInternal₀ {a} {b} ctA ctB
      
      InternalF₁ : {a b : Obj ((DepCat op) ×C DepCat)} 
                 → Hom ((DepCat op) ×C DepCat) a b → Hom DepCat (InternalF₀ a) (InternalF₀ b)
      InternalF₁ {(a ,' a') ,' (b ,' b')} {(c ,' c') ,' (d ,' d')} ((f ,' ct-f) ,' (g ,' ct-g))
        = [ f , g ]₁ ,' DepInternal₁ a' c' b' d' f g
      
      internal-id : {a : Obj ((DepCat op) ×C DepCat)} → InternalF₁ {a} {a} (id ((DepCat op) ×C DepCat)) ≡ id DepCat
      internal-id {(a ,' a') ,' (b ,' b')} = Σ-eq (Functor.id InternalHom) (dep-internal-id a' b')
      
      internal-compose : {a b c : Obj ((DepCat op) ×C DepCat)}
                       → {f : Hom ((DepCat op) ×C DepCat) a b} {g : Hom ((DepCat op) ×C DepCat) b c}
                       → InternalF₁ (g ∘DC×DC f) ≡ InternalF₁ g ∘DC InternalF₁ f
      internal-compose {(a ,' a') ,' (b ,' b')} {(c ,' c') ,' (d ,' d')} {(e ,' e') ,' (x ,' x')} {(f ,' f') ,' (g ,' g')} {(h ,' h') ,' (k ,' k')} 
        = Σ-eq (Functor.compose InternalHom) (dep-internal-compose a' b' c' d' e' x' f g h k)
      
  DepClosedCat : ClosedCategory DepCat 
  DepClosedCat = record
    { InternalHom = DepInternalHom
    ; I = {!!} ,' CtI
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
