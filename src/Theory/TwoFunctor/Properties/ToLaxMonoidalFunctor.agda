
-- Stdlib
open import Level
open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Data.Unit
open import Data.Product
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( refl to hrefl ; sym to hsym ; trans to htrans ; cong to hcong ; cong₂ to hcong₂ ; subst₂ to hsubst₂ ; proof-irrelevance to hproof-irrelevance )
open ≡-Reasoning hiding ( _≅⟨_⟩_ )
open ≅-Reasoning hiding ( _≡⟨⟩_ ; _≡⟨_⟩_ ) renaming ( begin_ to hbegin_ ; _∎ to _∎h )

-- Local
open import Extensionality
open import Utilities
open import Theory.Monoid
open import Theory.Category.Definition
open import Theory.Category.Examples.Monoid
open import Theory.Category.Examples.Discrete
open import Theory.Category.Examples.Functor
open import Theory.Category.Monoidal
open import Theory.Category.Monoidal.Examples.Monoid
open import Theory.Category.Monoidal.Examples.FunctorWithComposition renaming ( functorMonoidalCategory to Fun )
open import Theory.Functor.Definition hiding ( functor )
open import Theory.Functor.Composition
open import Theory.Functor.Monoidal
open import Theory.Natural.Transformation
open import Theory.Natural.Transformation.Examples
open import Theory.Natural.Transformation.Examples.FunctorCompositionAssociator
open import Theory.TwoCategory.Definition
open import Theory.TwoCategory.Examples.Functor renaming ( Cat to Cat' )
open import Theory.TwoCategory.Examples.DiscreteHomCat
open import Theory.TwoFunctor.ConstZeroCell
open import Theory.TwoFunctor.Definition

open Category hiding ( left-id ; right-id ; assoc )
open StrictTwoCategory hiding ( left-id ; right-id ; assoc )

module Theory.TwoFunctor.Properties.ToLaxMonoidalFunctor where 

open ConstLaxTwoFunctor
open StrictTwoCategory
open MonoidalCategory

LaxTwoFunctor→LaxMonoidalFunctor : {ℓE ℓC₀ ℓC₁ : Level}
                                 → {Eff : Set ℓE}
                                 → (mon : Monoid Eff)
                                 → (C : Category {ℓC₀} {ℓC₁})
                                 → ConstLaxTwoFunctor (discreteHomCatTwoCategory (monoidCategory mon)) Cat' C
                                 → LaxMonoidalFunctor (monoidMonoidalCategory mon) (Fun C)
LaxTwoFunctor→LaxMonoidalFunctor {ℓE} {ℓC₀} {ℓC₁} {Eff} mon C F 
  = laxMonoidalFunctor (P₁ F {lift tt} {lift tt}) (η F {lift tt}) μ' assoc' left-unitality' right-unitality'
  where
    open Monoid mon
    open NaturalTransformation renaming ( η to nat-η)
    
    Mon = monoidMonoidalCategory mon
    Mon₂ = discreteHomCatTwoCategory (monoidCategory mon)
    
    μ' : NaturalTransformation [ tensor (Fun C) ]∘[ [ P₁ F ]×[ P₁ F ] ] [ P₁ F ]∘[ tensor Mon ]
    μ' = naturalTransformation μ'-η μ'-natural
      where
        μ'-η : (x : Eff × Eff)
             → NaturalTransformation ([ [ tensor (Fun C) ]∘[ [ P₁ F ]×[ P₁ F ] ] ]₀ x) ([ [ P₁ F ]∘[ tensor Mon ] ]₀ x)
        μ'-η (i , j) = μ F {lift tt} {lift tt} {lift tt} {j} {i}
        
        abstract
          μ'-natural : {a b : Eff × Eff}
                     → {f : Hom (HomCat Mon₂ (lift tt) (lift tt) ×C HomCat Mon₂ (lift tt) (lift tt)) a b}
                     → ⟨ [ [ P₁ F ]∘[ tensor Mon ] ]₁ f ⟩∘ᵥ⟨ μ'-η a ⟩
                     ≡ ⟨ μ'-η b ⟩∘ᵥ⟨ [ [ tensor (Fun C) ]∘[ [ P₁ F ]×[ P₁ F ] ] ]₁ f ⟩
          μ'-natural {i , j} {.i , .j} {refl , refl} = begin
            ⟨ [ [ P₁ F ]∘[ tensor Mon ] ]₁ (refl , refl) ⟩∘ᵥ⟨ μ'-η (i , j) ⟩
              ≡⟨⟩
            ⟨ [ P₁ F ]₁ refl ⟩∘ᵥ⟨ μ'-η (i , j) ⟩
              ≡⟨⟩
            ⟨ [ P₁ F ]₁ (id₂ Mon₂ {lift tt}) ⟩∘ᵥ⟨ μ'-η (i , j) ⟩
              ≡⟨ cong (λ X → ⟨ X ⟩∘ᵥ⟨ μ'-η (i , j) ⟩) (Functor.id (P₁ F)) ⟩
            ⟨ id₂ Cat' {C} ⟩∘ᵥ⟨ μ'-η (i , j) ⟩
              ≡⟨ vertical-right-id Cat' ⟩
            μ'-η (i , j)
              ≡⟨ sym (vertical-left-id Cat') ⟩
            ⟨ μ'-η (i , j) ⟩∘ᵥ⟨ id₂ Cat' {C} ⟩
              ≡⟨ cong (λ X → ⟨ μ'-η (i , j) ⟩∘ᵥ⟨ X ⟩) (sym (Functor.id (tensor (Fun C)))) ⟩
            ⟨ μ'-η (i , j) ⟩∘ᵥ⟨ [ tensor (Fun C) ]₁ (id₂ Cat' {C} , id₂ Cat' {C}) ⟩
              ≡⟨ cong₂ (λ X Y → ⟨ μ'-η (i , j) ⟩∘ᵥ⟨ [ tensor (Fun C) ]₁ (X , Y) ⟩) (sym (Functor.id (P₁ F))) (sym (Functor.id (P₁ F))) ⟩
            ⟨ μ'-η (i , j) ⟩∘ᵥ⟨ [ tensor (Fun C) ]₁ ([ P₁ F ]₁ refl , [ P₁ F ]₁ refl) ⟩
              ≡⟨⟩
            ⟨ μ'-η (i , j) ⟩∘ᵥ⟨ [ [ tensor (Fun C) ]∘[ [ P₁ F ]×[ P₁ F ] ] ]₁ (refl , refl) ⟩ ∎
    
    private
      abstract
        nat-trans-subst : {ℓ₀ ℓ₁ : Level} {C D : Category {ℓ₀} {ℓ₁}} {F G H : Functor C D} 
                        → (X : NaturalTransformation F G) → (Y : NaturalTransformation F H) 
                        → (c : Obj C) 
                        → G ≡ H
                        → X ≅ Y 
                        → nat-η X c ≅ nat-η Y c
        nat-trans-subst X Y c refl hrefl = hrefl
    
    abstract
      assoc' : (x y z : Eff)
             → ⟨ [ P₁ F ]₁ (MonoidalCategory.α Mon x y z) ⟩∘ᵥ⟨ ⟨ μ F {f = z} {x ∙ y} ⟩∘ᵥ⟨ ⟨ μ F {f = y} {x} ⟩∘ₕ⟨ Id⟨ [ P₁ F ]₀ z ⟩ ⟩ ⟩ ⟩
             ≡ ⟨ μ F {f = y ∙ z} {x} ⟩∘ᵥ⟨ ⟨ ⟨ Id⟨ [ P₁ F ]₀ x ⟩ ⟩∘ₕ⟨ μ F {f = z} {y} ⟩ ⟩∘ᵥ⟨ MonoidalCategory.α (Fun C) ([ P₁ F ]₀ x) ([ P₁ F ]₀ y) ([ P₁ F ]₀ z) ⟩ ⟩
      assoc' x y z = begin
        ⟨ [ P₁ F ]₁ (MonoidalCategory.α Mon x y z) ⟩∘ᵥ⟨ ⟨ μ F {f = z} {x ∙ y} ⟩∘ᵥ⟨ ⟨ μ F {f = y} {x} ⟩∘ₕ⟨ Id⟨ [ P₁ F ]₀ z ⟩ ⟩ ⟩ ⟩
          ≡⟨ cong (λ X → ⟨ [ P₁ F ]₁ X ⟩∘ᵥ⟨ ⟨ μ F {f = z} {x ∙ y} ⟩∘ᵥ⟨ ⟨ μ F {f = y} {x} ⟩∘ₕ⟨ Id⟨ [ P₁ F ]₀ z ⟩ ⟩ ⟩ ⟩) (proof-irrelevance (MonoidalCategory.α Mon x y z) (α' Mon₂ z y x)) ⟩
        ⟨ [ P₁ F ]₁ (StrictTwoCategory.α' Mon₂ z y x) ⟩∘ᵥ⟨ ⟨ μ F {f = z} {x ∙ y} ⟩∘ᵥ⟨ ⟨ μ F {f = y} {x} ⟩∘ₕ⟨ Id⟨ [ P₁ F ]₀ z ⟩ ⟩ ⟩ ⟩
          ≡⟨ LaxTwoFunctor.laxFunAssoc-α' (laxTwoFunctor F) ⟩
        ⟨ μ F {f = y ∙ z} {x} ⟩∘ᵥ⟨ ⟨ ⟨ Id⟨ [ P₁ F ]₀ x ⟩ ⟩∘ₕ⟨ μ F {f = z} {y} ⟩ ⟩∘ᵥ⟨ StrictTwoCategory.α' Cat' ([ P₁ F ]₀ z) ([ P₁ F ]₀ y) ([ P₁ F ]₀ x) ⟩ ⟩
          ≡⟨ cong (λ X → ⟨ μ F {f = y ∙ z} {x} ⟩∘ᵥ⟨ ⟨ ⟨ Id⟨ [ P₁ F ]₀ x ⟩ ⟩∘ₕ⟨ μ F {f = z} {y} ⟩ ⟩∘ᵥ⟨ X ⟩ ⟩) (natural-transformation-eq associator-eq) ⟩
        ⟨ μ F {f = y ∙ z} {x} ⟩∘ᵥ⟨ ⟨ ⟨ Id⟨ [ P₁ F ]₀ x ⟩ ⟩∘ₕ⟨ μ F {f = z} {y} ⟩ ⟩∘ᵥ⟨ MonoidalCategory.α (Fun C) ([ P₁ F ]₀ x) ([ P₁ F ]₀ y) ([ P₁ F ]₀ z) ⟩ ⟩ ∎
          where
            abstract
              associator-eq : (λ c → nat-η (StrictTwoCategory.α' Cat' ([ P₁ F ]₀ z) ([ P₁ F ]₀ y) ([ P₁ F ]₀ x)) c) ≡ (λ c → nat-η (MonoidalCategory.α (Fun C) ([ P₁ F ]₀ x) ([ P₁ F ]₀ y) ([ P₁ F ]₀ z)) c)
              associator-eq = fun-ext $ λ (c : Obj C) → ≅-to-≡ $ hbegin
                nat-η (α' Cat' ([ P₁ F ]₀ z) ([ P₁ F ]₀ y) ([ P₁ F ]₀ x)) c 
                  ≅⟨ nat-trans-subst (α' Cat' ([ P₁ F ]₀ z) ([ P₁ F ]₀ y) ([ P₁ F ]₀ x)) (id₂ Cat' {f = [ [ [ P₁ F ]₀ x ]∘[ [ P₁ F ]₀ y ] ]∘[ [ P₁ F ]₀ z ]}) c (assoc Cat') (α'≅id₂ Cat' ([ P₁ F ]₀ z) ([ P₁ F ]₀ y) ([ P₁ F ]₀ x)) ⟩
                nat-η (id₂ Cat' {f = [ [ [ P₁ F ]₀ x ]∘[ [ P₁ F ]₀ y ] ]∘[ [ P₁ F ]₀ z ]}) c 
                  ≅⟨ hrefl ⟩
                Category.id C {[ [ P₁ F ]₀ x ]₀ ([ [ P₁ F ]₀ y ]₀ ([ [ P₁ F ]₀ z ]₀ c))}
                  ≅⟨ hrefl ⟩
                nat-η (MonoidalCategory.α (Fun C) ([ P₁ F ]₀ x) ([ P₁ F ]₀ y) ([ P₁ F ]₀ z)) c ∎h
    
    abstract
      left-unitality' : (x : Eff)
                      → MonoidalCategory.λ' (Fun C) ([ P₁ F ]₀ x)
                      ≡ ⟨ [ P₁ F ]₁ (MonoidalCategory.λ' Mon x) ⟩∘ᵥ⟨ ⟨ μ F {f = x} {unit Mon} ⟩∘ᵥ⟨ ⟨ η F ⟩∘ₕ⟨ MonoidalCategory.id (Fun C) ⟩ ⟩ ⟩
      left-unitality' x = begin
        MonoidalCategory.λ' (Fun C) ([ P₁ F ]₀ x)
          ≡⟨ natural-transformation-eq left-unitor-eq ⟩ 
        StrictTwoCategory.ρ Cat' ([ P₁ F ]₀ x)
          ≡⟨ sym $ LaxTwoFunctor.laxFunId-ρ (ConstLaxTwoFunctor.laxTwoFunctor F) {lift tt} {lift tt} {x} ⟩ 
        ⟨ [ P₁ F ]₁ (StrictTwoCategory.ρ Mon₂ x) ⟩∘ᵥ⟨ ⟨ μ F {f = x} {unit Mon} ⟩∘ᵥ⟨ ⟨ η F ⟩∘ₕ⟨ MonoidalCategory.id (Fun C) ⟩ ⟩ ⟩
          ≡⟨ cong (λ X → ⟨ [ P₁ F ]₁ X ⟩∘ᵥ⟨ ⟨ μ F {f = x} {unit Mon} ⟩∘ᵥ⟨ ⟨ η F ⟩∘ₕ⟨ MonoidalCategory.id (Fun C) ⟩ ⟩ ⟩) (proof-irrelevance (StrictTwoCategory.ρ Mon₂ x) (MonoidalCategory.λ' Mon x)) ⟩ 
        ⟨ [ P₁ F ]₁ (MonoidalCategory.λ' Mon x) ⟩∘ᵥ⟨ ⟨ μ F {f = x} {unit Mon} ⟩∘ᵥ⟨ ⟨ η F ⟩∘ₕ⟨ MonoidalCategory.id (Fun C) ⟩ ⟩ ⟩ ∎ 
          where
            abstract
              left-unitor-eq : (λ c → nat-η (MonoidalCategory.λ' (Fun C) ([ P₁ F ]₀ x)) c) ≡ (λ c → nat-η (StrictTwoCategory.ρ Cat' ([ P₁ F ]₀ x)) c)
              left-unitor-eq = fun-ext $ λ (c : Obj C) → ≅-to-≡ 
                             $ nat-trans-subst (id₂ Cat' {f = [ id₁ Cat' ]∘[ [ P₁ F ]₀ x ]}) 
                                               (StrictTwoCategory.ρ Cat' ([ P₁ F ]₀ x)) 
                                               c 
                                               (right-id Cat') 
                                               (hsym (htrans (ρ≅id₂ Cat' ([ P₁ F ]₀ x)) (id≅id Cat' (sym (right-id Cat')))))

    abstract
      right-unitality' : (x : Eff) 
                       → MonoidalCategory.ρ (Fun C) ([ P₁ F ]₀ x) 
                       ≡ ⟨ [ P₁ F ]₁ (MonoidalCategory.ρ Mon x) ⟩∘ᵥ⟨ ⟨ nat-η μ' (x , unit Mon) ⟩∘ᵥ⟨ ⟨ MonoidalCategory.id (Fun C) ⟩∘ₕ⟨ η F ⟩ ⟩ ⟩
      right-unitality' x = begin
        MonoidalCategory.ρ (Fun C) ([ P₁ F ]₀ x) 
          ≡⟨ natural-transformation-eq right-unitor-eq ⟩
        StrictTwoCategory.λ' Cat' ([ P₁ F ]₀ x) 
          ≡⟨ sym $ LaxTwoFunctor.laxFunId-λ' (ConstLaxTwoFunctor.laxTwoFunctor F) {lift tt} {lift tt} {x} ⟩
        ⟨ [ P₁ F ]₁ (StrictTwoCategory.λ' Mon₂ x) ⟩∘ᵥ⟨ ⟨ nat-η μ' (x , unit Mon) ⟩∘ᵥ⟨ ⟨ MonoidalCategory.id (Fun C) ⟩∘ₕ⟨ η F ⟩ ⟩ ⟩
          ≡⟨ cong (λ X → ⟨ [ P₁ F ]₁ X ⟩∘ᵥ⟨ ⟨ nat-η μ' (x , unit Mon) ⟩∘ᵥ⟨ ⟨ MonoidalCategory.id (Fun C) ⟩∘ₕ⟨ η F ⟩ ⟩ ⟩) (proof-irrelevance (StrictTwoCategory.λ' Mon₂ x) (MonoidalCategory.ρ Mon x)) ⟩
        ⟨ [ P₁ F ]₁ (MonoidalCategory.ρ Mon x) ⟩∘ᵥ⟨ ⟨ nat-η μ' (x , unit Mon) ⟩∘ᵥ⟨ ⟨ MonoidalCategory.id (Fun C) ⟩∘ₕ⟨ η F ⟩ ⟩ ⟩ ∎
          where
            abstract
              right-unitor-eq : (λ c → nat-η (MonoidalCategory.ρ (Fun C) ([ P₁ F ]₀ x)) c) ≡ (λ c → nat-η (StrictTwoCategory.λ' Cat' ([ P₁ F ]₀ x)) c)
              right-unitor-eq = fun-ext $ λ (c : Obj C) → ≅-to-≡ 
                              $ nat-trans-subst (id₂ Cat' {f = [ [ P₁ F ]₀ x ]∘[ id₁ Cat' ]}) 
                                                (StrictTwoCategory.λ' Cat' ([ P₁ F ]₀ x)) 
                                                c 
                                                (left-id Cat')
                                                (hsym (htrans (λ'≅id₂ Cat' ([ P₁ F ]₀ x)) (id≅id Cat' (sym (left-id Cat')))))
