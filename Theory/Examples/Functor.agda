
module Theory.Examples.Functor where 

-- Stdlib
open import Level renaming ( suc to lsuc ; zero to lzero )
open import Function hiding ( id ) renaming ( _∘_ to _∘F_ )
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning 

open import Theory.Category
open import Theory.Functor

-------------------------------------------------------------------------------
-- Creating a Tri-Functor from two Bi-Functors (Variant: C × (D × E))
-------------------------------------------------------------------------------
biFunctor→triFunctor₁ 
  : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ ℓE₀ ℓE₁ ℓJ₀ ℓJ₁ ℓK₀ ℓK₁ : Level} 
  → {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}} {E : Category {ℓE₀} {ℓE₁}} 
  → {J : Category {ℓJ₀} {ℓJ₁}} {K : Category {ℓK₀} {ℓK₁}}
  → Functor (C ×C J) K → Functor (D ×C E) J → Functor (C ×C (D ×C E)) K
biFunctor→triFunctor₁ {C = C} {D} {E} {J} {K} C×J→K D×E→J = record 
  { F₀ = F₀
  ; F₁ = F₁ 
  ; id = idF 
  ; dist = distF
  } where
    open Category
    
    F₀ : Obj (C ×C (D ×C E)) → Obj K
    F₀ (c , d×e) = [ C×J→K ]₀ (c , [ D×E→J ]₀ d×e)

    F₁ : {a b : Obj (C ×C (D ×C E))} → Hom (C ×C (D ×C E)) a b → Hom K (F₀ a) (F₀ b)
    F₁ (c , d×e) = [ C×J→K ]₁ (c , [ D×E→J ]₁ d×e)
    
    idF : {a : Obj (C ×C (D ×C E))} 
        → F₁ {a} {a} (id (C ×C (D ×C E))) ≡ id K
    idF {a} = begin 
      F₁ (id (C ×C (D ×C E))) 
        ≡⟨ refl ⟩ 
      [ C×J→K ]₁ (id C , [ D×E→J ]₁ (id (D ×C E)))
        ≡⟨ cong (λ X → [ C×J→K ]₁ (id C , X)) (Functor.id D×E→J) ⟩ 
      [ C×J→K ]₁ (id C , id J)
        ≡⟨ Functor.id C×J→K ⟩ 
      id K ∎
    
    _∘K_ = _∘_ K
    _∘C_ = _∘_ C
    _∘J_ = _∘_ J
    _∘CJ_ = _∘_ (C ×C J)
    _∘CDE_ = _∘_ (C ×C (D ×C E))
    _∘DE_ = _∘_ (D ×C E)
    
    distF : {a b c : Obj (C ×C (D ×C E))} {f : Hom (C ×C (D ×C E)) a b} {g : Hom (C ×C (D ×C E)) b c} 
         → F₁ (((C ×C (D ×C E)) ∘ g) f) ≡ (K ∘ F₁ g) (F₁ f)
    distF {f = fC , fDE} {g = gC , gDE} = begin
      F₁ ((gC , gDE) ∘CDE (fC , fDE))
        ≡⟨ refl ⟩
      [ C×J→K ]₁ (gC ∘C fC , [ D×E→J ]₁ (gDE ∘DE fDE))
        ≡⟨ cong (λ X → [ C×J→K ]₁ (gC ∘C fC , X)) (Functor.dist D×E→J) ⟩ 
      [ C×J→K ]₁ (gC ∘C fC , [ D×E→J ]₁ gDE ∘J [ D×E→J ]₁ fDE)
        ≡⟨ refl ⟩ 
      [ C×J→K ]₁ ((gC , [ D×E→J ]₁ gDE) ∘CJ (fC , [ D×E→J ]₁ fDE))
        ≡⟨ Functor.dist C×J→K ⟩ 
      ([ C×J→K ]₁ (gC , [ D×E→J ]₁ gDE)) ∘K ([ C×J→K ]₁ (fC , [ D×E→J ]₁ fDE))
        ≡⟨ refl ⟩
      (F₁ (gC , gDE)) ∘K (F₁ (fC , fDE)) ∎
