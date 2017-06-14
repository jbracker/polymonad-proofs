
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
open import Theory.Natural.Isomorphism.Examples.FunctorCompositionLeftUnitor renaming ( functorCompositionLeftUnitorIso to fclIso )
open import Theory.Natural.Isomorphism.Examples.FunctorCompositionRightUnitor renaming ( functorCompositionRightUnitorIso to fcrIso )

open import Extensionality

module Theory.Category.Monoidal.Examples.FunctorWithComposition.TriangleIdentity where

open Category
open Functor renaming ( id to functor-id )
open NaturalTransformation renaming ( η to nat-η )
open NaturalIsomorphism renaming ( η to iso-η )

open Theory.Functor.Association.Associator
open Theory.Functor.Application.BiFunctor

triangle-id 
  : {ℓC₀ ℓC₁ : Level} (C : Category {ℓC₀} {ℓC₁}) 
  → (F G : Obj (Fun C C)) 
  → F₁ (CompF C C C) (iso-η (fcrIso C) F , id (Fun C C) {G})
  ≡ (Fun C C ∘ F₁ (CompF C C C) (id (Fun C C) {F}, iso-η (fclIso C) G)) (iso-η (fcaIso C) (F ,' Id[ C ] ,' G))
triangle-id C F G = natural-transformation-eq $ fun-ext $ λ (x : Obj C) → begin
   nat-η ⟨ iso-η (fcrIso C) F ⟩∘ₕ⟨ Id⟨ G ⟩ ⟩ x
     ≡⟨⟩
   nat-η (iso-η (fcrIso C) F) ([ G ]₀ x) ∘C [ F ]₁ (nat-η Id⟨ G ⟩ x)
     ≡⟨ cong (λ X → nat-η (iso-η (fcrIso C) F) ([ G ]₀ x) ∘C X) (functor-id F) ⟩
   nat-η (iso-η (fcrIso C) F) ([ G ]₀ x) ∘C id C
     ≡⟨ left-id C ⟩
   nat-η (iso-η (fcrIso C) F) ([ G ]₀ x)
     ≡⟨ sym (functor-id F) ⟩
   [ F ]₁ (id C)
     ≡⟨⟩
   [ F ]₁ (nat-η (iso-η (fclIso C) G) x)
     ≡⟨ sym (right-id C) ⟩
   id C ∘C [ F ]₁ (nat-η (iso-η (fclIso C) G) x)
     ≡⟨⟩
   nat-η Id⟨ F ⟩ ([ G ]₀ x) ∘C [ F ]₁ (nat-η (iso-η (fclIso C) G) x)
     ≡⟨⟩
   nat-η ⟨ Id⟨ F ⟩ ⟩∘ₕ⟨ iso-η (fclIso C) G ⟩ x
     ≡⟨ sym (left-id C) ⟩
   nat-η ⟨ Id⟨ F ⟩ ⟩∘ₕ⟨ iso-η (fclIso C) G ⟩ x ∘C id C -- nat-η (iso-η (fcaIso C) (F ,' Id[ C ] ,' G)) x
     ≡⟨⟩
   nat-η ⟨ ⟨ Id⟨ F ⟩ ⟩∘ₕ⟨ iso-η (fclIso C) G ⟩ ⟩∘ᵥ⟨ (iso-η (fcaIso C) (F ,' Id[ C ] ,' G)) ⟩ x ∎
   where _∘C_ = _∘_ C

