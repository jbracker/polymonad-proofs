
open import Level
open import Function hiding ( _∘_ ; id )

open import Data.Product renaming ( _,_ to _,'_ )

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Theory.Category
open import Theory.Category.Closed
open import Theory.Functor
open import Theory.Natural.Transformation

module Theory.Functor.Closed where

-------------------------------------------------------------------------------
-- Definition of lax closed functors
-------------------------------------------------------------------------------
record LaxClosedFunctor {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} 
                        {C' : Category {ℓC₀} {ℓC₁}} {D' : Category {ℓD₀} {ℓD₁}} 
                        (C : ClosedCategory C') (D : ClosedCategory D')
                        : Set (ℓC₀ ⊔ ℓC₁ ⊔ ℓD₀ ⊔ ℓD₁) where
  field
    F : Functor C' D'
  
  open ClosedCategory renaming ( id to idC ) hiding ( coher-1 ; coher-2 ; coher-3 ; coher-4 )
  open Functor F public
  
  private
    C[_,_]₀ = [_,_]₀ C
    C[_,_]₁ = [_,_]₁ C
    D[_,_]₀ = [_,_]₀ D
    D[_,_]₁ = [_,_]₁ D
    _∘D_ = _∘_ D
    _∘C_ = _∘_ C
  
  field
    F̂ : (x y : Obj C) → Hom D (F₀ C[ x , y ]₀) (D[ F₀ x , F₀ y ]₀)
    
    F⁰ : Hom D (I D) (F₀ (I C))
    
    F̂-natural-x : (y : Obj C) → {x x' : Obj C} {f : Hom C x' x} 
                → D[ F₁ f , F₁ (idC C {y}) ]₁ ∘D F̂ x y ≡ F̂ x' y ∘D F₁ C[ f , idC C {y} ]₁
    
    F̂-natural-y : (x : Obj C) → {y y' : Obj C} {f : Hom C y y'} 
                → D[ F₁ (idC C {x}) , F₁ f ]₁ ∘D F̂ x y ≡ F̂ x y' ∘D F₁ C[ idC C {x} , f ]₁
    
    coher-1 : (x : Obj C) → j D (F₀ x) ≡ F̂ x x ∘D (F₁ (j C x) ∘D F⁰)
    
    coher-2 : (x : Obj C) → i D (F₀ x) ∘D F₁ (i-inv C x) ≡ D[ F⁰ , idC D ]₁ ∘D F̂ (I C) x
    
    coher-3 : (x y z : Obj C) 
            → D[ idC D , F̂ x z ]₁ ∘D (F̂ C[ x , y ]₀ C[ x , z ]₀ ∘D F₁ (L C x y z)) 
            ≡ D[ F̂ x y , idC D ]₁ ∘D (L D (F₀ x) (F₀ y) (F₀ z) ∘D F̂ y z)
  
  import Theory.Functor.Application
  open import Theory.Functor.Composition
  open Theory.Functor.Application.BiFunctor
  open Theory.Functor.Composition.BiFunctor
  
  F̂-natural-transformation-x : (y : Obj C) → NaturalTransformation ([-, y ] ([ F ]∘[ InternalHom C ])) ([-, y ] ([ [ F ]op , F ]∘[ InternalHom D ]))
  F̂-natural-transformation-x y = naturalTransformation (flip F̂ y) (F̂-natural-x y)
  
  F̂-natural-transformation-y : (x : Obj C) → NaturalTransformation ([ x ,-] ([ F ]∘[ InternalHom C ])) ([ x ,-] ([ [ F ]op , F ]∘[ InternalHom D ]))
  F̂-natural-transformation-y x = naturalTransformation (F̂ x) (F̂-natural-y x)
  
  F̂-natural-xy : {x x' y y' : Obj C} {f : Hom C y x} {g : Hom C x' y'} 
               → D[ F₁ f , F₁ g ]₁ ∘D F̂ x x' ≡ F̂ y y' ∘D F₁ C[ f , g ]₁
  F̂-natural-xy {x} {x'} {y} {y'} {f} {g} = begin
    D[ F₁ f , F₁ g ]₁ ∘D F̂ x x' 
      ≡⟨ cong (λ X → X ∘D F̂ x x') (sym $ InternalHom-compose-eq D) ⟩
    (D[ F₁ f , idC D ]₁ ∘D D[ idC D , F₁ g ]₁) ∘D F̂ x x' 
      ≡⟨ sym (assoc D) ⟩
    D[ F₁ f , idC D ]₁ ∘D (D[ idC D , F₁ g ]₁ ∘D F̂ x x')
      ≡⟨ cong₂ (λ X Y → D[ F₁ f , X ]₁ ∘D (D[ Y , F₁ g ]₁ ∘D F̂ x x')) (sym $ id) (sym $ id) ⟩
    D[ F₁ f , F₁ (idC C) ]₁ ∘D (D[ F₁ (idC C) , F₁ g ]₁ ∘D F̂ x x')
      ≡⟨ cong (λ X → D[ F₁ f , F₁ (idC C) ]₁ ∘D X) (F̂-natural-y x) ⟩
    D[ F₁ f , F₁ (idC C) ]₁ ∘D (F̂ x y' ∘D F₁ C[ idC C , g ]₁)
      ≡⟨ assoc D ⟩
    (D[ F₁ f , F₁ (idC C) ]₁ ∘D F̂ x y') ∘D F₁ C[ idC C , g ]₁
      ≡⟨ cong (λ X → X ∘D F₁ C[ idC C , g ]₁) (F̂-natural-x y') ⟩
    (F̂ y y' ∘D F₁ C[ f , idC C ]₁) ∘D F₁ C[ idC C , g ]₁
      ≡⟨ sym (assoc D) ⟩
    F̂ y y' ∘D (F₁ C[ f , idC C ]₁ ∘D F₁ C[ idC C , g ]₁)
      ≡⟨ cong (λ X → F̂ y y' ∘D X) (sym $ compose) ⟩
    F̂ y y' ∘D F₁ (C[ f , idC C ]₁ ∘C C[ idC C , g ]₁)
      ≡⟨ cong (λ X → F̂ y y' ∘D F₁ X) (InternalHom-compose-eq C) ⟩
    F̂ y y' ∘D F₁ C[ f , g ]₁ ∎
  
  F̂-natural-transformation : NaturalTransformation ([ F ]∘[ InternalHom C ]) ([ [ F ]op , F ]∘[ InternalHom D ])
  F̂-natural-transformation = naturalTransformation (uncurry F̂)
                           $ λ {a} {b} {f} → F̂-natural-xy {proj₁ a} {proj₂ a} {proj₁ b} {proj₂ b} {proj₁ f} {proj₂ f}
