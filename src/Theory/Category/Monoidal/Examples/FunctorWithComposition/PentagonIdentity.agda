
open import Level
open import Function hiding ( id ; _∘_ )

open import Data.Product

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Theory.Triple renaming ( _,_,_ to _,'_,'_ )
open import Theory.Category.Definition
open import Theory.Category.Monoidal
open import Theory.Category.Isomorphism
open import Theory.Category.Examples renaming ( functorCategory to Fun )
open import Theory.Functor.Definition
open import Theory.Functor.Composition
open import Theory.Functor.Association
open import Theory.Functor.Application
open import Theory.Functor.Examples.CompositionFunctor renaming ( compositionFunctor to CompF )
open import Theory.Natural.Transformation
open import Theory.Natural.Transformation.Properties
open import Theory.Natural.Isomorphism
open import Theory.Natural.Isomorphism.Examples.FunctorCompositionAssociator renaming ( functorCompositionAssociatorIso to fcaIso )

open import Extensionality

module Theory.Category.Monoidal.Examples.FunctorWithComposition.PentagonIdentity where

open Category
open Functor renaming ( id to functor-id )
open NaturalTransformation renaming ( η to nat-η )
open NaturalIsomorphism renaming ( η to iso-η )

abstract
  pentagon-id 
    : {ℓC₀ ℓC₁ : Level} (C : Category {ℓC₀} {ℓC₁}) 
    → (F G H I : Obj (Fun C C)) 
    → (Fun C C ∘ F₁ (CompF C C C) (id (Fun C C) {F} , iso-η (fcaIso C) (G ,' H ,' I))) ((Fun C C ∘ iso-η (fcaIso C) (F ,' F₀ (CompF C C C) (G , H) ,' I)) (F₁ (CompF C C C) (iso-η (fcaIso C) (F ,' G ,' H) , id (Fun C C) {I})))
    ≡ (Fun C C ∘ iso-η (fcaIso C) (F ,' G ,' F₀ (CompF C C C) (H , I))) (iso-η (fcaIso C) (F₀ (CompF C C C) (F , G) ,' H ,' I))
  pentagon-id C F G H I = natural-transformation-eq $ fun-ext $ λ (c : Obj C) → begin
    nat-η ⟨ ⟨ id (Fun C C) {F} ⟩∘ₕ⟨ iso-η (fcaIso C) (G ,' H ,' I) ⟩ ⟩∘ᵥ⟨ ⟨ iso-η (fcaIso C) (F ,' F₀ (CompF C C C) (G , H) ,' I) ⟩∘ᵥ⟨ ⟨ iso-η (fcaIso C) (F ,' G ,' H) ⟩∘ₕ⟨ id (Fun C C) {I} ⟩ ⟩ ⟩ c
      ≡⟨⟩ 
    nat-η ⟨ id (Fun C C) {F} ⟩∘ₕ⟨ iso-η (fcaIso C) (G ,' H ,' I) ⟩ c ∘C (id C ∘C nat-η ⟨ iso-η (fcaIso C) (F ,' G ,' H) ⟩∘ₕ⟨ id (Fun C C) {I} ⟩ c)
      ≡⟨ cong (λ X → nat-η ⟨ id (Fun C C) {F} ⟩∘ₕ⟨ iso-η (fcaIso C) (G ,' H ,' I) ⟩ c ∘C X) (right-id C) ⟩ 
    nat-η ⟨ id (Fun C C) {F} ⟩∘ₕ⟨ iso-η (fcaIso C) (G ,' H ,' I) ⟩ c ∘C nat-η ⟨ iso-η (fcaIso C) (F ,' G ,' H) ⟩∘ₕ⟨ id (Fun C C) {I} ⟩ c
      ≡⟨⟩ 
    (id C ∘C [ F ]₁ (id C)) ∘C (nat-η ⟨ iso-η (fcaIso C) (F ,' G ,' H) ⟩∘ₕ⟨ id (Fun C C) {I} ⟩ c)
      ≡⟨ cong (λ X → X ∘C (nat-η ⟨ iso-η (fcaIso C) (F ,' G ,' H) ⟩∘ₕ⟨ id (Fun C C) {I} ⟩ c)) (right-id C) ⟩ 
    [ F ]₁ (id C) ∘C (nat-η ⟨ iso-η (fcaIso C) (F ,' G ,' H) ⟩∘ₕ⟨ id (Fun C C) {I} ⟩ c)
      ≡⟨ cong (λ X → X ∘C (nat-η ⟨ iso-η (fcaIso C) (F ,' G ,' H) ⟩∘ₕ⟨ id (Fun C C) {I} ⟩ c)) (functor-id F)⟩ 
    id C ∘C (nat-η ⟨ iso-η (fcaIso C) (F ,' G ,' H) ⟩∘ₕ⟨ id (Fun C C) {I} ⟩ c)
      ≡⟨ right-id C ⟩ 
    nat-η ⟨ iso-η (fcaIso C) (F ,' G ,' H) ⟩∘ₕ⟨ id (Fun C C) {I} ⟩ c
      ≡⟨⟩ 
    id C ∘C [ [ F ]∘[ [ G ]∘[ H ] ] ]₁ (id C)
      ≡⟨ right-id C ⟩ 
    [ [ F ]∘[ [ G ]∘[ H ] ] ]₁ (id C)
      ≡⟨ functor-id [ F ]∘[ [ G ]∘[ H ] ] ⟩ 
    id C
      ≡⟨ sym (left-id C) ⟩ 
    id C ∘C id C
      ≡⟨⟩ 
    nat-η ⟨ iso-η (fcaIso C) (F ,' G ,' F₀ (CompF C C C) (H , I)) ⟩∘ᵥ⟨ iso-η (fcaIso C) (F₀ (CompF C C C) (F , G) ,' H ,' I) ⟩ c ∎
    where _∘C_ = _∘_ C

