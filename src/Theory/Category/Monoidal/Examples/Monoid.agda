
open import Level
open import Function hiding ( id ) renaming ( _∘_ to _∘F_ )

open import Data.Unit
open import Data.Product

open import Relation.Binary.PropositionalEquality
open import Theory.Monoid
open import Theory.Category.Definition
open import Theory.Category.Monoidal
open import Theory.Category.Isomorphism
open import Theory.Category.Examples renaming ( setCategory to SetCat )
open import Theory.Functor.Definition
open import Theory.Natural.Transformation
open import Theory.Natural.Isomorphism

module Theory.Category.Monoidal.Examples.Monoid where

monoidMonoidalCategory : {ℓ : Level} {A : Set ℓ} → (mon : Monoid A) → MonoidalCategory (discreteCategory A)
monoidMonoidalCategory {ℓ} {A} mon = record
  { tensor = tensor
  ; unit = Monoid.ε mon
  ; associator = associator
  ; left-unitor = left-unitor
  ; right-unitor = right-unitor
  ; triangle-id = {!!} -- λ x y → refl
  ; pentagon-id = {!!} -- λ w x y z → refl
  } where
    open import Theory.Triple renaming ( _,_,_ to _,'_,'_ )
    open import Theory.Functor.Association
    open import Theory.Functor.Application
    open Theory.Triple.Triple renaming ( proj₁ to proj₁' ; proj₂ to proj₂' )
    open Theory.Functor.Association.Associator
    open Theory.Functor.Application.BiFunctor
    open Category hiding ( left-id ; right-id ; assoc )
    open Monoid mon

    Disc = discreteCategory A
    _∘D_ = _∘_ Disc
    
    tensor : Functor (Disc ×C Disc) Disc
    tensor = functor (λ x → proj₁ x ∙ proj₂ x) tensor₁ refl tensor-compose
      where
        tensor₁ : {a b : Obj (Disc ×C Disc)} → Hom (Disc ×C Disc) a b → Hom Disc (proj₁ a ∙ proj₂ a) (proj₁ b ∙ proj₂ b)
        tensor₁ (refl , refl) = refl

        abstract
          tensor-compose : {a b c : Obj (Disc ×C Disc)} {f : Hom (Disc ×C Disc) a b} {g : Hom (Disc ×C Disc) b c}
                         → tensor₁ (((Disc ×C Disc) ∘ g) f) ≡ (Disc ∘ tensor₁ g) (tensor₁ f)
          tensor-compose {a} {b} {c} {refl , refl} {refl , refl} = refl
    
    associator : NaturalIsomorphism (leftAssociator tensor) (rightAssociator tensor)
    associator = naturalIsomorphism (naturalTransformation (λ {x → sym assoc}) {!!})
                                    (λ x → isomorphism assoc (proof-irrelevance (sym assoc ∘D assoc) (id Disc)) (proof-irrelevance (assoc ∘D sym assoc) (id Disc)))
    -- (Disc ∘ (λ { x₁ → sym (Monoid.assoc mon) }) x) assoc ≡ id Disc
    left-unitor : NaturalIsomorphism ([ Monoid.ε mon ,-] tensor) Id[ discreteCategory A ]
    left-unitor = naturalIsomorphism (naturalTransformation (λ x → left-id ) {!!})
                                     (λ x → isomorphism (sym left-id) {!!} {!!})
    
    right-unitor : NaturalIsomorphism ([-, Monoid.ε mon ] tensor) Id[ discreteCategory A ]
    right-unitor = naturalIsomorphism (naturalTransformation (λ x → right-id) {!!})
                                                             (λ x → isomorphism (sym right-id) {!!} {!!})

