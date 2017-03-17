
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
open import Theory.Category.Isomorphism

open import Theory.Functor

open import Theory.Natural.Transformation
open import Theory.Natural.Isomorphism

module Theory.Category.Closed.Dependent where 

record DependentClosedCategory {ℓ₀ ℓ₁ ℓDep₀ ℓDep₁ : Level} {C : Category {ℓ₀} {ℓ₁}} (CC : ClosedCategory C) : Set (ℓ₀ ⊔ ℓ₁ ⊔ suc (ℓDep₀ ⊔ ℓDep₁)) where
  
  field 
    DC : DependentCategory {ℓDep₀ = ℓDep₀} {ℓDep₁} C
  
  open DependentCategory DC
  open ClosedCategory CC hiding ( _∘_ ; Obj ; Hom ; id )
  open Category
  
  private
    _∘C_ = _∘_ C
    _∘Cop_ = _∘_ (C op)
    _∘DC_ = _∘_ DepCat
    _∘DC×DC_ = _∘_ (DepCat op ×C DepCat)
  
  field
    Dep[_,_]₀ : {a b : Obj C} → DepObj a → DepObj b → DepObj [ a , b ]₀
    
    Dep[_,_]₁ : {a b c d : Obj C}
              → {a' : DepObj a} {b' : DepObj b} {c' : DepObj c} {d' : DepObj d}
              → {f : Hom (C op) a b} {g : Hom C c d}
              → (f' : DepHom b' a' f) (g' : DepHom c' d' g)
              → DepHom Dep[ a' , c' ]₀ Dep[ b' , d' ]₀ [ f , g ]₁
  
    dep-internal-id : {a b : Obj C}
                    → (a' : DepObj a) (b' : DepObj b)
                    → Dep[ depId {a} {a'} , depId {b} {b'} ]₁ ≅ depId {[ a , b ]₀} {Dep[ a' , b' ]₀}
    
    dep-internal-compose : {a b c d e x : Obj C}
                         → {a' : DepObj a} {b' : DepObj b} {c' : DepObj c} {d' : DepObj d} {e' : DepObj e} {x' : DepObj x}
                         → {f : Hom (C op) a c} {g : Hom C b d} {h : Hom (C op) c e} {k : Hom C d x}
                         → (f' : DepHom c' a' f) (g' : DepHom b' d' g) (h' : DepHom e' c' h) (k' : DepHom d' x' k)
                         → Dep[ f' ∘dep h' , k' ∘dep g' ]₁ ≅ Dep[ h' , k' ]₁ ∘dep Dep[ f' , g' ]₁
    
    depI : DepObj I
    
    dep-i : {x : Obj C} → (x' : DepObj x) → DepHom x' Dep[ depI , x' ]₀ (i x)
    
    dep-i-natural : {a b : Obj C} {a' : DepObj a} {b' : DepObj b} 
                  → {f : Hom C a b} {f' : DepHom a' b' f}
                  → Dep[ depId {I} {depI} , f' ]₁ ∘dep dep-i {a} a' ≅ dep-i b' ∘dep f'
    
    dep-i-inv : {x : Obj C} → (x' : DepObj x) → DepHom Dep[ depI , x' ]₀ x' (i-inv x)

    dep-i-inv-left-id : {x : Obj C} → (x' : DepObj x) → dep-i x' ∘dep dep-i-inv x' ≅ depId {[ I , x ]₀} {Dep[ depI , x' ]₀}
    
    dep-i-inv-right-id : {x : Obj C} → (x' : DepObj x) → dep-i-inv x' ∘dep dep-i x' ≅ depId {x} {x'}
    
    dep-j : {a : Obj C} → (a' : DepObj a) → DepHom depI Dep[ a' , a' ]₀ (j a)
    
    dep-L : {a b c : Obj C} → (a' : DepObj a) → (b' : DepObj b) → (c' : DepObj c) 
          → DepHom Dep[ b' , c' ]₀ Dep[ Dep[ a' , b' ]₀ , Dep[ a' , c' ]₀ ]₀ (L a b c)
    
    dep-γ-inv : {x y : Obj C} {x' : DepObj x} {y' : DepObj y} 
              → {f : Hom C I [ x , y ]₀} → (f' : DepHom depI Dep[ x' , y' ]₀ f)
              → DepHom x' y' (γ-inv f)
    
    dep-j-extranatural-a : {a b : Obj C} {a' : DepObj a} {b' : DepObj b} 
                         → {f : Hom C a b} → (f' : DepHom a' b' f) 
                         → Dep[ f' , depId ]₁ ∘dep dep-j b' ≅ Dep[ depId , f' ]₁ ∘dep dep-j a'
    
    dep-L-natural-c : {a b c₀ c₁ : Obj C} (a' : DepObj a) → (b' : DepObj b) → (c₀' : DepObj c₀) → (c₁' : DepObj c₁)
                    → {f : Hom C c₀ c₁} → (f' : DepHom c₀' c₁' f) 
                    → Dep[ Dep[ depId , depId ]₁ , Dep[ depId , f' ]₁ ]₁ ∘dep dep-L a' b' c₀'
                    ≅ dep-L a' b' c₁' ∘dep Dep[ depId , f' ]₁

    dep-L-natural-b : {a b₀ b₁ c : Obj C} 
                    → (a' : DepObj a) (b₀' : DepObj b₀) (b₁' : DepObj b₁) (c' : DepObj c) 
                    → {f : Hom C b₀ b₁} → (f' : DepHom b₀' b₁' f)
                    → Dep[ Dep[ depId , f' ]₁ , Dep[ depId , depId ]₁ ]₁ ∘dep dep-L a' b₁' c'
                    ≅ dep-L a' b₀' c' ∘dep Dep[ f' , depId ]₁
    
    dep-L-extranatural-a : {a₀ a₁ b c : Obj C} (a₀' : DepObj a₀) (a₁' : DepObj a₁) (b' : DepObj b) (c' : DepObj c)
                         → {f : Hom C a₀ a₁} (f' : DepHom a₀' a₁' f)
                         → Dep[ depId , Dep[ f' , depId ]₁ ]₁ ∘dep dep-L a₁' b' c'
                         ≅ Dep[ Dep[ f' , depId ]₁ , depId ]₁ ∘dep dep-L a₀' b' c'
    
    dep-coher-1 : {x y : Obj C} → (x' : DepObj x) → (y' : DepObj y) 
                → dep-L x' y' y' ∘dep dep-j y' ≅ dep-j Dep[ x' , y' ]₀
  
    dep-coher-2 : {x y : Obj C} → (x' : DepObj x) → (y' : DepObj y) 
                → Dep[ dep-j x' , depId ]₁ ∘dep dep-L x' x' y' ≅ dep-i Dep[ x' , y' ]₀

    dep-coher-3 : {y z : Obj C} → (y' : DepObj y) → (z' : DepObj z) 
                → Dep[ dep-i y' , depId ]₁ ∘dep dep-L depI y' z' ≅ Dep[ depId {y} {y'} , dep-i z' ]₁

    dep-coher-4 : {x y u v : Obj C} 
                → (x' : DepObj x) → (y' : DepObj y) → (u' : DepObj u) → (v' : DepObj v)
                → Dep[ depId , dep-L x' y' v' ]₁ ∘dep dep-L y' u' v'
                ≅ Dep[ dep-L x' y' u' , depId ]₁ ∘dep (dep-L Dep[ x' , y' ]₀ Dep[ x' , u' ]₀ Dep[ x' , v' ]₀ ∘dep dep-L x' u' v')
    
    dep-γ-right-id : {x y : Obj C} {x' : DepObj x} {y' : DepObj y}
                   → {f : Hom C I [ x , y ]₀} → (f' : DepHom depI Dep[ x' , y' ]₀ f)
                   → Dep[ depId , dep-γ-inv f' ]₁ ∘dep dep-j x' ≅ f'

    dep-γ-left-id : {x y : Obj C} {x' : DepObj x} {y' : DepObj y}
                  → {f : Hom C x y} → (f' : DepHom x' y' f) → dep-γ-inv (Dep[ depId , f' ]₁ ∘dep dep-j x') ≅ f'

  DepInternalHom : Functor ((DepCat op) ×C DepCat) DepCat
  DepInternalHom = functor InternalF₀ InternalF₁ internal-id (λ {a} {b} {c} {f} {g} → internal-compose {a} {b} {c} {f} {g})
    where
      InternalF₀ : Obj ((DepCat op) ×C DepCat) → Obj DepCat
      InternalF₀ ((a ,' a') ,' (b ,' b')) = [ a , b ]₀ ,' Dep[ a' , b' ]₀
      
      InternalF₁ : {a b : Obj ((DepCat op) ×C DepCat)} 
                 → Hom ((DepCat op) ×C DepCat) a b → Hom DepCat (InternalF₀ a) (InternalF₀ b)
      InternalF₁ {(a ,' a') ,' (b ,' b')} {(c ,' c') ,' (d ,' d')} ((f ,' f') ,' (g ,' g'))
        = [ f , g ]₁ ,' Dep[ f' , g' ]₁
      
      internal-id : {a : Obj ((DepCat op) ×C DepCat)} → InternalF₁ {a} {a} (id ((DepCat op) ×C DepCat)) ≡ id DepCat
      internal-id {(a ,' a') ,' (b ,' b')} = Σ-eq (Functor.id InternalHom) (dep-internal-id a' b')
      
      internal-compose : {a b c : Obj ((DepCat op) ×C DepCat)}
                       → {f : Hom ((DepCat op) ×C DepCat) a b} {g : Hom ((DepCat op) ×C DepCat) b c}
                       → InternalF₁ (g ∘DC×DC f) ≡ InternalF₁ g ∘DC InternalF₁ f
      internal-compose {(a ,' a') ,' (b ,' b')} {(c ,' c') ,' (d ,' d')} {(e ,' e') ,' (x ,' x')} {(f ,' f') ,' (g ,' g')} {(h ,' h') ,' (k ,' k')} 
        = Σ-eq (Functor.compose InternalHom) (dep-internal-compose f' g' h' k')
  
  DCC[_,_]₀ : (a : Obj (DepCat op)) → (b : Obj DepCat) → Obj DepCat
  DCC[_,_]₀ a b = Functor.F₀ DepInternalHom (a ,' b)
  
  DCC[_,_]₁ : {a b c d : Obj DepCat} → (f : Hom (DepCat op) a b) → (g : Hom DepCat c d) → Hom DepCat DCC[ a , c ]₀ DCC[ b , d ]₀
  DCC[_,_]₁ f g = Functor.F₁ DepInternalHom (f ,' g)
  
  DepClosedCat : ClosedCategory DepCat 
  DepClosedCat = record
    { InternalHom = DepInternalHom
    ; I = I ,' depI
    ; i-natural-isomorphism = record 
      { natural-transformation = record
        { η = λ x → i (proj₁ x) ,' dep-i (proj₂ x)
        ; natural = Σ-eq i-natural dep-i-natural
        }
      ; isomorphic = λ x → record
        { f⁻¹ = i-inv (proj₁ x) ,' dep-i-inv (proj₂ x)
        ; left-id = Σ-eq (i-inv-left-id (proj₁ x)) (dep-i-inv-left-id (proj₂ x))
        ; right-id = Σ-eq (i-inv-right-id (proj₁ x)) (dep-i-inv-right-id (proj₂ x))
        }
      }
    ; j = λ a → j (proj₁ a) ,' dep-j (proj₂ a)
    ; L = λ a b c → L (proj₁ a) (proj₁ b) (proj₁ c) ,' dep-L (proj₂ a) (proj₂ b) (proj₂ c)
    ; γ-inv = λ f → γ-inv (proj₁ f) ,' dep-γ-inv (proj₂ f)
    ; j-extranatural-a = λ f → Σ-eq (j-extranatural-a (proj₁ f)) (dep-j-extranatural-a (proj₂ f))
    ; L-natural-c = λ a b {c₀} {c₁} {f} → Σ-eq (L-natural-c (proj₁ a) (proj₁ b)) (dep-L-natural-c (proj₂ a) (proj₂ b) (proj₂ c₀) (proj₂ c₁) (proj₂ f))
    ; L-natural-b = λ a c {b₀} {b₁} {f} → Σ-eq (L-natural-b (proj₁ a) (proj₁ c)) (dep-L-natural-b (proj₂ a) (proj₂ b₀) (proj₂ b₁) (proj₂ c) (proj₂ f))
    ; L-extranatural-a = λ b c {a₀} {a₁} f → Σ-eq (L-extranatural-a (proj₁ b) (proj₁ c) (proj₁ f)) (dep-L-extranatural-a (proj₂ a₀) (proj₂ a₁) (proj₂ b) (proj₂ c) (proj₂ f))
    ; coher-1 = λ x y → Σ-eq (coher-1 (proj₁ x) (proj₁ y)) (dep-coher-1 (proj₂ x) (proj₂ y))
    ; coher-2 = λ x y → Σ-eq (coher-2 (proj₁ x) (proj₁ y)) (dep-coher-2 (proj₂ x) (proj₂ y))
    ; coher-3 = λ y z → Σ-eq (coher-3 (proj₁ y) (proj₁ z)) (dep-coher-3 (proj₂ y) (proj₂ z))
    ; coher-4 = λ x y u v → Σ-eq (coher-4 (proj₁ x) (proj₁ y) (proj₁ u) (proj₁ v)) (dep-coher-4 (proj₂ x) (proj₂ y) (proj₂ u) (proj₂ v))
    ; γ-right-id = λ f → Σ-eq (γ-right-id (proj₁ f)) (dep-γ-right-id (proj₂ f))
    ; γ-left-id  = λ f → Σ-eq (γ-left-id  (proj₁ f)) (dep-γ-left-id  (proj₂ f))
    }
