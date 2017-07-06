
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

open Functor hiding ( id )
open NaturalTransformation renaming ( η to nat-η )
open NaturalIsomorphism renaming ( η to iso-η )

monoidMonoidalCategory : {ℓ : Level} {A : Set ℓ} → (mon : Monoid A) → MonoidalCategory (discreteCategory A)
monoidMonoidalCategory {ℓ} {A} mon = record
  { tensor = tensor
  ; unit = Monoid.ε mon
  ; associator = associator
  ; left-unitor = left-unitor
  ; right-unitor = right-unitor
  ; triangle-id = λ x y → proof-irrelevance
                (F₁ tensor (iso-η right-unitor x , id Disc))
                (F₁ tensor (id Disc , iso-η left-unitor y) ∘D iso-η associator (x ,' ε ,' y))
  ; pentagon-id = λ w x y z → proof-irrelevance
                (F₁ tensor (id Disc , iso-η associator (x ,' y ,' z)) ∘D (iso-η associator (w ,' F₀ tensor (x , y) ,' z) ∘D F₁ tensor (iso-η associator (w ,' x ,' y) , id Disc)))
                (iso-η associator (w ,' x ,' F₀ tensor (y , z)) ∘D iso-η associator (F₀ tensor (w , x) ,' y ,' z))
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
    associator = naturalIsomorphism (naturalTransformation (λ {x → sym assoc})
                                      (λ {a b} {f} → proof-irrelevance ([ rightAssociator tensor ]₁ f ∘D sym (Monoid.assoc mon))
                                                                       (sym (Monoid.assoc mon) ∘D ([ leftAssociator tensor ]₁ f) )))
                                    (λ x → isomorphism assoc (proof-irrelevance (sym assoc ∘D assoc) (id Disc))
                                                             (proof-irrelevance (assoc ∘D sym assoc) (id Disc)))
    -- (Disc ∘ (λ { x₁ → sym (Monoid.assoc mon) }) x) assoc ≡ id Disc
    left-unitor : NaturalIsomorphism ([ Monoid.ε mon ,-] tensor) Id[ discreteCategory A ]
    left-unitor = naturalIsomorphism (naturalTransformation (λ x → left-id)
                                       (λ {a b} {f} → proof-irrelevance ([ Id[ discreteCategory A ] ]₁ f ∘D left-id) (left-id ∘D ([ [ ε ,-] tensor ]₁ f))))
                                     (λ x → isomorphism (sym left-id)
                                                        (proof-irrelevance (left-id ∘D sym left-id) (id Disc))
                                                        (proof-irrelevance (sym left-id ∘D left-id) (id Disc)))
    
    right-unitor : NaturalIsomorphism ([-, Monoid.ε mon ] tensor) Id[ discreteCategory A ]
    right-unitor = naturalIsomorphism (naturalTransformation (λ x → right-id)
                                        (λ {a b} {f} → proof-irrelevance ([ Id[ discreteCategory A ] ]₁ f ∘D right-id) (right-id ∘D ([ [-, ε ] tensor ]₁ f))))
                                      (λ x → isomorphism (sym right-id)
                                                         (proof-irrelevance (right-id ∘D sym right-id) (id Disc))
                                                         (proof-irrelevance (sym right-id ∘D right-id) (id Disc)))
