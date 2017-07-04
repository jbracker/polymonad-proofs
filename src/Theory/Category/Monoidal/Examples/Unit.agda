
open import Level
open import Function hiding ( id ) renaming ( _∘_ to _∘F_ )

open import Data.Unit
open import Data.Product

open import Relation.Binary.PropositionalEquality

open import Theory.Category.Definition
open import Theory.Category.Monoidal
open import Theory.Category.Isomorphism
open import Theory.Category.Examples renaming ( setCategory to SetCat )
open import Theory.Functor.Definition
open import Theory.Natural.Transformation
open import Theory.Natural.Isomorphism

module Theory.Category.Monoidal.Examples.Unit where

unitMonoidalCategory : MonoidalCategory ⊤-Cat
unitMonoidalCategory = monoidalCategory comp tt assoc lunitor runitor triangle pentagon
  where    
    open import Theory.Functor.Association
    open Theory.Functor.Association.Associator
    open import Theory.Functor.Application
    open Theory.Functor.Application.BiFunctor
    open import Theory.Triple renaming ( _,_,_ to _,'_,'_ )
    open Theory.Triple.Triple renaming ( proj₁ to proj₁' ; proj₂ to proj₂' )
    
    open Category hiding ( assoc )
    open Functor hiding ( id )
    open NaturalIsomorphism renaming ( η to iso-η )

    _∘⊤_ = _∘_ ⊤-Cat
    
    comp : Functor (⊤-Cat ×C ⊤-Cat) ⊤-Cat
    comp = functor (λ _ → tt) (λ {_} {_} _ → tt) (λ {_} → refl) (λ {_} {_} {_} {_} {_} → refl)
    
    assoc : NaturalIsomorphism (leftAssociator comp) (rightAssociator comp)
    assoc = naturalIsomorphism (naturalTransformation (λ _ → tt) (λ {_} {_} {_} → refl)) (λ _ → isomorphism tt refl refl)
    
    lunitor : NaturalIsomorphism ([ tt ,-] comp) Id[ ⊤-Cat ]
    lunitor = naturalIsomorphism (naturalTransformation (λ _ → tt) (λ {_} {_} {_} → refl)) (λ _ → isomorphism tt refl refl)
    
    runitor : NaturalIsomorphism ([-, tt ] comp) Id[ ⊤-Cat ]
    runitor = naturalIsomorphism (naturalTransformation (λ _ → tt) (λ {_} {_} {_} → refl)) (λ _ → isomorphism tt refl refl)
    
    abstract
      triangle : (x y : Obj ⊤-Cat) 
               → F₁ comp (iso-η runitor x , Category.id ⊤-Cat) 
               ≡ F₁ comp (id ⊤-Cat , iso-η lunitor y) ∘⊤ iso-η assoc (x ,' tt ,' y)
      triangle _ _ = refl
    
    abstract
      pentagon : (w x y z : Obj ⊤-Cat)
               → F₁ comp (id ⊤-Cat , iso-η assoc (x ,' y ,' z)) ∘⊤ (iso-η assoc (w ,' F₀ comp (x , y) ,' z) ∘⊤ F₁ comp (iso-η assoc (w ,' x ,' y) , id ⊤-Cat))
               ≡ iso-η assoc (w ,' x ,' F₀ comp (y , z)) ∘⊤ iso-η assoc (F₀ comp (w , x) ,' y ,' z)
      pentagon _ _ _ _ = refl
    
⊤-MonCat = unitMonoidalCategory
