
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
open import Theory.TwoCategory.Examples.Monoid
open import Theory.TwoFunctor.ConstZeroCell
open import Theory.TwoFunctor.Definition

open Category hiding ( left-id ; right-id ; assoc )
open StrictTwoCategory hiding ( left-id ; right-id ; assoc )

module Theory.TwoFunctor.Properties.FromLaxMonoidalFunctor where 

open StrictTwoCategory
open MonoidalCategory

LaxMonoidalFunctor→LaxTwoFunctor : {ℓE ℓC₀ ℓC₁ : Level}
                                 → {Eff : Set ℓE}
                                 → (mon : Monoid Eff)
                                 → (C : Category {ℓC₀} {ℓC₁})
                                 → LaxMonoidalFunctor (monoidMonoidalCategory mon) (Fun C)
                                 → ConstLaxTwoFunctor (monoidTwoCategory mon) Cat' C
LaxMonoidalFunctor→LaxTwoFunctor {ℓE} {ℓC₀} {ℓC₁} {Eff} mon C MonF
  = const-lax-two-functor F MonF-ε (λ {x y z} {f} {g} → μ g f) 
                          laxFunId₁ laxFunId₂ laxFunAssoc μ-natural₁ μ-natural₂
  where
    open Monoid mon
    open NaturalTransformation renaming ( η to nat-η)
    open LaxMonoidalFunctor MonF renaming (ε to MonF-ε)
    
    Mon = monoidMonoidalCategory mon
    Mon₂ = monoidTwoCategory mon
    
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
      laxFunId₁ : {x y : Cell₀ Mon₂} {f : Cell₁ Mon₂ x y}
                → ⟨ μ f (id₁ Mon₂) ⟩∘ᵥ⟨ ⟨ id₂ Cat' ⟩∘ₕ⟨ MonF-ε ⟩ ⟩ ≅ id₂ Cat' {f = [ F ]₀ f}
      laxFunId₁ {tt} {tt} {f} = hbegin
        ⟨ μ f (id₁ Mon₂) ⟩∘ᵥ⟨ ⟨ id₂ Cat' ⟩∘ₕ⟨ MonF-ε ⟩ ⟩ 
          ≅⟨ hsym (≡-to-≅ (vertical-right-id Cat')) ⟩
        ⟨ id₂ Cat' ⟩∘ᵥ⟨ ⟨ μ f (id₁ Mon₂) ⟩∘ᵥ⟨ ⟨ id₂ Cat' ⟩∘ₕ⟨ MonF-ε ⟩ ⟩  ⟩
          ≅⟨ hcong (λ X → ⟨ X ⟩∘ᵥ⟨ ⟨ μ f (id₁ Mon₂) ⟩∘ᵥ⟨ ⟨ id₂ Cat' ⟩∘ₕ⟨ MonF-ε ⟩ ⟩  ⟩) (hsym (≡-to-≅ (Functor.id F))) ⟩
        ⟨ [ F ]₁ (Cell₂ Mon₂ (f ∙ id₁ Mon₂) (f ∙ id₁ Mon₂) ∋ id₂ Mon₂) ⟩∘ᵥ⟨ ⟨ μ f (id₁ Mon₂) ⟩∘ᵥ⟨ ⟨ id₂ Cat' ⟩∘ₕ⟨ MonF-ε ⟩ ⟩  ⟩
          ≅⟨ hcong₂ (λ X Y → ⟨ [ F ]₁ (Cell₂ Mon₂ (f ∙ id₁ Mon₂) X ∋ Y) ⟩∘ᵥ⟨ ⟨ μ f (id₁ Mon₂) ⟩∘ᵥ⟨ ⟨ id₂ Cat' ⟩∘ₕ⟨ MonF-ε ⟩ ⟩  ⟩) 
                    (≡-to-≅ (Monoid.right-id mon)) 
                    (hsym (htrans (λ'≅id₂ Mon₂ f) (id≅id Mon₂ (sym (Monoid.right-id mon))))) ⟩
        ⟨ [ F ]₁ (Cell₂ Mon₂ (f ∙ id₁ Mon₂) f ∋ StrictTwoCategory.λ' Mon₂ f) ⟩∘ᵥ⟨ ⟨ μ f (id₁ Mon₂) ⟩∘ᵥ⟨ ⟨ id₂ Cat' ⟩∘ₕ⟨ MonF-ε ⟩ ⟩  ⟩
          ≅⟨ hcong (λ X → ⟨ [ F ]₁ X ⟩∘ᵥ⟨ ⟨ μ f (id₁ Mon₂) ⟩∘ᵥ⟨ ⟨ id₂ Cat' ⟩∘ₕ⟨ MonF-ε ⟩ ⟩  ⟩) (≡-to-≅ (proof-irrelevance (StrictTwoCategory.λ' Mon₂ f) (MonoidalCategory.ρ Mon f))) ⟩
        ⟨ [ F ]₁ (MonoidalCategory.ρ Mon f) ⟩∘ᵥ⟨ ⟨ μ f (id₁ Mon₂) ⟩∘ᵥ⟨ ⟨ id₂ Cat' ⟩∘ₕ⟨ MonF-ε ⟩ ⟩  ⟩
          ≅⟨ hsym (≡-to-≅ (right-unitality f)) ⟩ 
        MonoidalCategory.ρ (Fun C) ([ F ]₀ f) 
          ≅⟨ ≡-to-≅ (natural-transformation-eq right-unitor-eq) ⟩
        StrictTwoCategory.λ' Cat' ([ F ]₀ f)
          ≅⟨ λ'≅id₂ Cat' ([ F ]₀ f) ⟩
        id₂ Cat' {f = [ F ]₀ f} ∎h
          where
            abstract
              right-unitor-eq : (λ c → nat-η (MonoidalCategory.ρ (Fun C) ([ F ]₀ f)) c) ≡ (λ c → nat-η (StrictTwoCategory.λ' Cat' ([ F ]₀ f)) c)
              right-unitor-eq = fun-ext $ λ (c : Obj C) → ≅-to-≡ 
                              $ nat-trans-subst (id₂ Cat' {f = [ [ F ]₀ f ]∘[ id₁ Cat' ]}) 
                                                (StrictTwoCategory.λ' Cat' ([ F ]₀ f)) 
                                                c 
                                                (left-id Cat')
                                                (hsym (htrans (λ'≅id₂ Cat' ([ F ]₀ f)) (id≅id Cat' (sym (left-id Cat')))))
    
    abstract
      laxFunId₂ : {x y : Cell₀ Mon₂} {f : Cell₁ Mon₂ x y}
                → ⟨ μ (id₁ Mon₂) f ⟩∘ᵥ⟨ ⟨ MonF-ε ⟩∘ₕ⟨ id₂ Cat' ⟩ ⟩ ≅ id₂ Cat' {f = [ F ]₀ f}
      laxFunId₂ {tt} {tt} {f} = hbegin
        ⟨ μ (id₁ Mon₂) f ⟩∘ᵥ⟨ ⟨ MonF-ε ⟩∘ₕ⟨ id₂ Cat' ⟩ ⟩ 
          ≅⟨ hsym (≡-to-≅ (vertical-right-id Cat')) ⟩
        ⟨ id₂ Cat' ⟩∘ᵥ⟨ ⟨ μ (id₁ Mon₂) f ⟩∘ᵥ⟨ ⟨ MonF-ε ⟩∘ₕ⟨ id₂ Cat' ⟩ ⟩ ⟩
          ≅⟨ hcong (λ X → ⟨ X ⟩∘ᵥ⟨ ⟨ μ (id₁ Mon₂) f ⟩∘ᵥ⟨ ⟨ MonF-ε ⟩∘ₕ⟨ id₂ Cat' ⟩ ⟩ ⟩) (hsym (≡-to-≅ (Functor.id F))) ⟩
        ⟨ [ F ]₁ (Cell₂ Mon₂ (id₁ Mon₂ ∙ f) (id₁ Mon₂ ∙ f) ∋ id₂ Mon₂) ⟩∘ᵥ⟨ ⟨ μ (id₁ Mon₂) f ⟩∘ᵥ⟨ ⟨ MonF-ε ⟩∘ₕ⟨ id₂ Cat' ⟩ ⟩ ⟩
          ≅⟨ hcong₂ (λ X Y → ⟨ [ F ]₁ (Cell₂ Mon₂ (id₁ Mon₂ ∙ f) X ∋ Y) ⟩∘ᵥ⟨ ⟨ μ (id₁ Mon₂) f ⟩∘ᵥ⟨ ⟨ MonF-ε ⟩∘ₕ⟨ id₂ Cat' ⟩ ⟩ ⟩) 
                    (≡-to-≅ (Monoid.left-id mon)) 
                    (hsym (htrans (ρ≅id₂ Mon₂ f) (id≅id Mon₂ (sym (Monoid.left-id mon))))) ⟩
        ⟨ [ F ]₁ (Cell₂ Mon₂ (id₁ Mon₂ ∙ f) f ∋ StrictTwoCategory.ρ Mon₂ f) ⟩∘ᵥ⟨ ⟨ μ (id₁ Mon₂) f ⟩∘ᵥ⟨ ⟨ MonF-ε ⟩∘ₕ⟨ id₂ Cat' ⟩ ⟩ ⟩
          ≅⟨ hcong (λ X → ⟨ [ F ]₁ X ⟩∘ᵥ⟨ ⟨ μ (id₁ Mon₂) f ⟩∘ᵥ⟨ ⟨ MonF-ε ⟩∘ₕ⟨ id₂ Cat' ⟩ ⟩ ⟩) (≡-to-≅ (proof-irrelevance (StrictTwoCategory.ρ Mon₂ f) (MonoidalCategory.λ' Mon f))) ⟩
        ⟨ [ F ]₁ (MonoidalCategory.λ' Mon f) ⟩∘ᵥ⟨ ⟨ μ (id₁ Mon₂) f ⟩∘ᵥ⟨ ⟨ MonF-ε ⟩∘ₕ⟨ id₂ Cat' ⟩ ⟩  ⟩
          ≅⟨ hsym (≡-to-≅ (left-unitality f)) ⟩ 
        MonoidalCategory.λ' (Fun C) ([ F ]₀ f)
          ≅⟨ ≡-to-≅ (natural-transformation-eq left-unitor-eq) ⟩
        StrictTwoCategory.ρ Cat' ([ F ]₀ f)
          ≅⟨ ρ≅id₂ Cat' ([ F ]₀ f) ⟩
        id₂ Cat' {f = [ F ]₀ f} ∎h
          where
            abstract
              left-unitor-eq : (λ c → nat-η (MonoidalCategory.λ' (Fun C) ([ F ]₀ f)) c) ≡ (λ c → nat-η (StrictTwoCategory.ρ Cat' ([ F ]₀ f)) c)
              left-unitor-eq = fun-ext $ λ (c : Obj C) → ≅-to-≡ 
                             $ nat-trans-subst (id₂ Cat' {f = [ id₁ Cat' ]∘[ [ F ]₀ f ]}) 
                                               (StrictTwoCategory.ρ Cat' ([ F ]₀ f)) 
                                               c 
                                               (right-id Cat') 
                                               (hsym (htrans (ρ≅id₂ Cat' ([ F ]₀ f)) (id≅id Cat' (sym (right-id Cat')))))
    
    abstract
      laxFunAssoc : {w x y z : Cell₀ Mon₂} {f : Cell₁ Mon₂ w x} {g : Cell₁ Mon₂ x y} {h : Cell₁ Mon₂ y z} 
                  → ⟨ μ h (g ∙ f) ⟩∘ᵥ⟨ ⟨ id₂ Cat' ⟩∘ₕ⟨ μ g f ⟩ ⟩
                  ≅ ⟨ μ (h ∙ g) f ⟩∘ᵥ⟨ ⟨ μ h g ⟩∘ₕ⟨ id₂ Cat' ⟩ ⟩
      laxFunAssoc {tt} {tt} {tt} {tt} {f} {g} {h} = hbegin
        ⟨ μ h (g ∙ f) ⟩∘ᵥ⟨ ⟨ id₂ Cat' ⟩∘ₕ⟨ μ g f ⟩ ⟩
          ≅⟨ hcong (λ X → ⟨ μ h (g ∙ f) ⟩∘ᵥ⟨ X ⟩) (≡-to-≅ (sym (vertical-left-id Cat'))) ⟩
        ⟨ μ h (g ∙ f) ⟩∘ᵥ⟨ ⟨ ⟨ id₂ Cat' ⟩∘ₕ⟨ μ g f ⟩ ⟩∘ᵥ⟨ (Cell₂ Cat' ([ [ F ]₀ h ]∘[ [ [ F ]₀ g ]∘[ [ F ]₀ f ] ]) ([ [ F ]₀ h ]∘[ [ [ F ]₀ g ]∘[ [ F ]₀ f ] ]) ∋ id₂ Cat') ⟩ ⟩
          ≅⟨ hcong₂ (λ X Y → ⟨ μ h (g ∙ f) ⟩∘ᵥ⟨ ⟨ ⟨ id₂ Cat' ⟩∘ₕ⟨ μ g f ⟩ ⟩∘ᵥ⟨ (Cell₂ Cat' X ([ [ F ]₀ h ]∘[ [ [ F ]₀ g ]∘[ [ F ]₀ f ] ]) ∋ Y) ⟩ ⟩) 
                    (≡-to-≅ (StrictTwoCategory.assoc Cat')) 
                    (hsym (htrans (α'≅id₂ Cat' ([ F ]₀ f) ([ F ]₀ g) ([ F ]₀ h)) (id≅id Cat' (sym $ StrictTwoCategory.assoc Cat')))) ⟩
        ⟨ μ h (g ∙ f) ⟩∘ᵥ⟨ ⟨ ⟨ id₂ Cat' ⟩∘ₕ⟨ μ g f ⟩ ⟩∘ᵥ⟨ (Cell₂ Cat' ([ [ [ F ]₀ h ]∘[ [ F ]₀ g ] ]∘[ [ F ]₀ f ]) ([ [ F ]₀ h ]∘[ [ [ F ]₀ g ]∘[ [ F ]₀ f ] ]) ∋ StrictTwoCategory.α' Cat' ([ F ]₀ f) ([ F ]₀ g) ([ F ]₀ h)) ⟩ ⟩
          ≅⟨ hcong (λ X → ⟨ μ h (g ∙ f) ⟩∘ᵥ⟨ ⟨ ⟨ id₂ Cat' ⟩∘ₕ⟨ μ g f ⟩ ⟩∘ᵥ⟨ X ⟩ ⟩) (≡-to-≅ (natural-transformation-eq associator-eq)) ⟩
        ⟨ μ h (g ∙ f) ⟩∘ᵥ⟨ ⟨ ⟨ id₂ Cat' ⟩∘ₕ⟨ μ g f ⟩ ⟩∘ᵥ⟨ MonoidalCategory.α (Fun C) ([ F ]₀ h) ([ F ]₀ g) ([ F ]₀ f) ⟩ ⟩
          ≅⟨ ≡-to-≅ (sym $ LaxMonoidalFunctor.assoc MonF h g f) ⟩
        ⟨ [ F ]₁ (MonoidalCategory.α Mon h g f) ⟩∘ᵥ⟨ ⟨ μ (h ∙ g) f ⟩∘ᵥ⟨ ⟨ μ h g ⟩∘ₕ⟨ id₂ Cat' ⟩ ⟩ ⟩
          ≅⟨ hcong (λ X → ⟨ [ F ]₁ X ⟩∘ᵥ⟨ ⟨ μ (h ∙ g) f ⟩∘ᵥ⟨ ⟨ μ h g ⟩∘ₕ⟨ id₂ Cat' ⟩ ⟩ ⟩) (≡-to-≅ (proof-irrelevance (MonoidalCategory.α Mon h g f) (StrictTwoCategory.α' Mon₂ f g h))) ⟩
        ⟨ [ F ]₁ (Cell₂ Mon₂ ((h ∙ g) ∙ f) (h ∙ (g ∙ f)) ∋ StrictTwoCategory.α' Mon₂ f g h) ⟩∘ᵥ⟨ ⟨ μ (h ∙ g) f ⟩∘ᵥ⟨ ⟨ μ h g ⟩∘ₕ⟨ id₂ Cat' ⟩ ⟩ ⟩
          ≅⟨ hcong₂ (λ X Y → ⟨ [ F ]₁ (Cell₂ Mon₂ ((h ∙ g) ∙ f) X ∋ Y) ⟩∘ᵥ⟨ ⟨ μ (h ∙ g) f ⟩∘ᵥ⟨ ⟨ μ h g ⟩∘ₕ⟨ id₂ Cat' ⟩ ⟩ ⟩) 
                    (≡-to-≅ (Monoid.assoc mon)) 
                    (α'≅id₂ Mon₂ f g h) ⟩
        ⟨ [ F ]₁ (Cell₂ Mon₂ ((h ∙ g) ∙ f) ((h ∙ g) ∙ f) ∋ id₂ Mon₂) ⟩∘ᵥ⟨ ⟨ μ (h ∙ g) f ⟩∘ᵥ⟨ ⟨ μ h g ⟩∘ₕ⟨ id₂ Cat' ⟩ ⟩ ⟩
          ≅⟨ hcong (λ X → ⟨ X ⟩∘ᵥ⟨ ⟨ μ (h ∙ g) f ⟩∘ᵥ⟨ ⟨ μ h g ⟩∘ₕ⟨ id₂ Cat' ⟩ ⟩ ⟩) (≡-to-≅ $ Functor.id F) ⟩
        ⟨ id₂ Cat' ⟩∘ᵥ⟨ ⟨ μ (h ∙ g) f ⟩∘ᵥ⟨ ⟨ μ h g ⟩∘ₕ⟨ id₂ Cat' ⟩ ⟩ ⟩
          ≅⟨ ≡-to-≅ (vertical-right-id Cat') ⟩
        ⟨ μ (h ∙ g) f ⟩∘ᵥ⟨ ⟨ μ h g ⟩∘ₕ⟨ id₂ Cat' ⟩ ⟩ ∎h
          where
            abstract
              associator-eq : (λ c → nat-η (StrictTwoCategory.α' Cat' ([ F ]₀ f) ([ F ]₀ g) ([ F ]₀ h)) c) ≡ (λ c → nat-η (MonoidalCategory.α (Fun C) ([ F ]₀ h) ([ F ]₀ g) ([ F ]₀ f)) c)
              associator-eq = fun-ext $ λ (c : Obj C) → ≅-to-≡ $ hbegin
                nat-η (α' Cat' ([ F ]₀ f) ([ F ]₀ g) ([ F ]₀ h)) c 
                  ≅⟨ nat-trans-subst (α' Cat' ([ F ]₀ f) ([ F ]₀ g) ([ F ]₀ h)) (id₂ Cat' {f = [ [ [ F ]₀ h ]∘[ [ F ]₀ g ] ]∘[ [ F ]₀ f ]}) c (assoc Cat') (α'≅id₂ Cat' ([ F ]₀ f) ([ F ]₀ g) ([ F ]₀ h)) ⟩
                nat-η (id₂ Cat' {f = [ [ [ F ]₀ h ]∘[ [ F ]₀ g ] ]∘[ [ F ]₀ f ]}) c 
                  ≅⟨ hrefl ⟩
                Category.id C {[ [ F ]₀ h ]₀ ([ [ F ]₀ g ]₀ ([ [ F ]₀ f ]₀ c))}
                  ≅⟨ hrefl ⟩
                nat-η (MonoidalCategory.α (Fun C) ([ F ]₀ h) ([ F ]₀ g) ([ F ]₀ f)) c ∎h

    abstract
      μ-natural₁ : {a b c : Cell₀ Mon₂}
                 → (f : Cell₁ Mon₂ a b)
                 → {x y : Cell₁ Mon₂ b c}
                 → {θ : Cell₂ Mon₂ x y} 
                 → ⟨ [ F ]₁ ((Mon₂ ∘ₕ θ) (id₂ Mon₂)) ⟩∘ᵥ⟨ μ x f ⟩
                 ≡ ⟨ μ y f ⟩∘ᵥ⟨ ⟨ [ F ]₁ θ ⟩∘ₕ⟨ [ F ]₁ (id₂ Mon₂) ⟩ ⟩
      μ-natural₁ {tt} {tt} {tt} f {x} {.x} {refl} = begin
        ⟨ [ F ]₁ refl ⟩∘ᵥ⟨ μ x f ⟩
          ≡⟨ cong (λ X → ⟨ X ⟩∘ᵥ⟨ μ x f ⟩) (Functor.id F) ⟩  
        ⟨ id₂ Cat' ⟩∘ᵥ⟨ μ x f ⟩
          ≡⟨ vertical-right-id Cat' ⟩  
        μ x f
          ≡⟨ sym (vertical-left-id Cat') ⟩  
        ⟨ μ x f ⟩∘ᵥ⟨ id₂ Cat' ⟩
          ≡⟨ cong (λ X → ⟨ μ x f ⟩∘ᵥ⟨ X ⟩) (sym $ id∘ₕid≡id Cat') ⟩  
        ⟨ μ x f ⟩∘ᵥ⟨ ⟨ id₂ Cat' ⟩∘ₕ⟨ id₂ Cat' ⟩ ⟩
          ≡⟨ cong₂ (λ X Y → ⟨ μ x f ⟩∘ᵥ⟨ ⟨ X ⟩∘ₕ⟨ Y ⟩ ⟩) (sym $ Functor.id F) (sym $ Functor.id F) ⟩  
        ⟨ μ x f ⟩∘ᵥ⟨ ⟨ [ F ]₁ refl ⟩∘ₕ⟨ [ F ]₁ refl ⟩ ⟩ ∎
    
    abstract
      μ-natural₂ : {a b c : Cell₀ Mon₂}
                 → (g : Cell₁ Mon₂ b c)
                 → {x y : Cell₁ Mon₂ a b}
                 → {θ : Cell₂ Mon₂ x y} 
                 → ⟨ [ F ]₁ ((Mon₂ ∘ₕ id₂ Mon₂) θ) ⟩∘ᵥ⟨ μ g x ⟩
                 ≡ ⟨ μ g y ⟩∘ᵥ⟨ ⟨ [ F ]₁ (id₂ Mon₂) ⟩∘ₕ⟨ [ F ]₁ θ ⟩ ⟩
      μ-natural₂ {tt} {tt} {tt} g {x} {.x} {refl} = begin
        ⟨ [ F ]₁ refl ⟩∘ᵥ⟨ μ g x ⟩
          ≡⟨ cong (λ X → ⟨ X ⟩∘ᵥ⟨ μ g x ⟩) (Functor.id F) ⟩ 
        ⟨ id₂ Cat' ⟩∘ᵥ⟨ μ g x ⟩
          ≡⟨ vertical-right-id Cat' ⟩ 
        μ g x
          ≡⟨ sym (vertical-left-id Cat') ⟩ 
        ⟨ μ g x ⟩∘ᵥ⟨ id₂ Cat' ⟩
          ≡⟨ cong (λ X → ⟨ μ g x ⟩∘ᵥ⟨ X ⟩) (sym (id∘ₕid≡id Cat')) ⟩ 
        ⟨ μ g x ⟩∘ᵥ⟨ ⟨ id₂ Cat' ⟩∘ₕ⟨ id₂ Cat' ⟩ ⟩
          ≡⟨ cong₂ (λ X Y → ⟨ μ g x ⟩∘ᵥ⟨ ⟨ X ⟩∘ₕ⟨ Y ⟩ ⟩) (sym (Functor.id F)) (sym (Functor.id F)) ⟩ 
        ⟨ μ g x ⟩∘ᵥ⟨ ⟨ [ F ]₁ refl ⟩∘ₕ⟨ [ F ]₁ refl ⟩ ⟩ ∎
