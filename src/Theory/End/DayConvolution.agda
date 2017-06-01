
open import Level
open import Function renaming ( _∘_ to _∘F_ ; id to idF )

open import Data.Product

open import Theory.Category.Definition
open import Theory.Category.Examples
open import Theory.Category.Monoidal
open import Theory.Functor.Definition
open import Theory.End.Definition
open import Theory.End.Wedge

module Theory.End.DayConvolution {ℓSet ℓC₀ ℓC₁ : Level} {C : Category {ℓC₀} {ℓC₁}} (CMon : MonoidalCategory C) where

open Category
open Functor

private
  Set' = setCategory {ℓSet ⊔ ℓC₁}

  _⊗C₀_ = MonoidalCategory._⊗₀_ CMon
  _⊗C₁_ = MonoidalCategory._⊗₁_ CMon
  _∘C_ = _∘_ C



dayConvolution : Functor ([ C , Set' ] ×C [ C , Set' ]) [ C , Set' ]
dayConvolution = functor day₀ day₁ {!!} {!!}
  where
    dayFunctor : Functor (C op) Set' → Functor C Set' → Obj C → Functor (C op ×C C) Set'
    dayFunctor F G c = functor dayF₀ dayF₁ {!!} {!!}
      where
        dayF₀ : Obj (C op ×C C) → Obj Set'
        dayF₀ (c₁ , c₂) = Hom C (c₁ ⊗C₀ c₂) c × (F₀ F c₁) × (F₀ G c₂)
        
        dayF₁ : {a b : Obj (C op ×C C)} → Hom (C op ×C C) a b → Hom Set' (dayF₀ a) (dayF₀ b)
        dayF₁ {a₁ , a₂} {b₁ , b₂} (f₁ , f₂) (homC , Fc₁ , Fc₂) = {!f₁ ⊗C₁ f₂!} , F₁ F f₁ Fc₁ , F₁ G f₂ Fc₂
       
    dayEnd : (F : Functor (C op) Set') (G : Functor C Set') → (c : Obj C) → CoEnd (dayFunctor F G c)
    dayEnd F G c = record { co-w = {!!} ; co-e = cowedge {!!} {!!} ; co-universal = {!!} }
    
    day₀ : Obj ([ C , Set' ] ×C [ C , Set' ]) → Obj [ C , Set' ]
    day₀ (F , G) = functor d0₀ d0₁ {!!} {!!}
      where
        
        d0₀ : Obj C → Obj Set'
        d0₀ c = {!!}
        
        d0₁ : {a b : Obj C} → Hom C a b → Hom Set' (d0₀ a) (d0₀ b)
        d0₁ f = {!!}
    
    day₁ : {a b : Obj ([ C , Set' ] ×C [ C , Set' ])} → Hom ([ C , Set' ] ×C [ C , Set' ]) a b → Hom [ C , Set' ] (day₀ a) (day₀ b)
    day₁ = {!!}
    
{-
_⊗Day_ : {C : Category {ℓC₀} {ℓC₁}} → (F G : Functor C Set') → CoEnd ? ?
_⊗Day_ = ?
-}
