
open import Level
open import Function renaming ( id to idF ; _∘_ to _∘F_ )

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Extensionality

open import Theory.Category.Definition
open import Theory.Category.Isomorphism
open import Theory.Category.Examples renaming ( setCategory to SetCat' ; functorCategory to FunctorCat )

open import Theory.Functor.Definition
open import Theory.Natural.Transformation

module Theory.Yoneda.Embedding {ℓ₀ ℓ₁ : Level} {C : Category {ℓ₀} {ℓ₁}} where

open Category
open Functor hiding ( id )

import Theory.Yoneda.HomFunctor
open Theory.Yoneda.HomFunctor {ℓ₀} {ℓ₁} {C}

import Theory.Yoneda.Bijection
open Theory.Yoneda.Bijection {ℓ₀} {ℓ₁} {C}

private
  SetCat = SetCat' {ℓ₀ ⊔ ℓ₁}
  _∘C_ = _∘_ C
  _∘Cop_ = _∘_ (C op)
  _∘Func_ = _∘_ (FunctorCat C SetCat)

YonedaEmbedding : Functor (C op) (FunctorCat C SetCat)
YonedaEmbedding = functor EmbF₀ EmbF₁ id-Emb compose-Emb
  where
    EmbF₀ : Obj (C op) → Obj (FunctorCat C SetCat)
    EmbF₀ A = Hom[ A ,-]
    
    EmbF₁ : {a b : Obj C} → Hom (C op) a b → Hom (FunctorCat C SetCat) Hom[ a ,-] Hom[ b ,-]
    EmbF₁ {a} {b} f = yoneda← Hom[ b ,-] a (lift f)
    
    id-Emb : {a : Obj (C op)} → EmbF₁ {a} {a} (id (C op)) ≡ id (FunctorCat C SetCat)
    id-Emb {A} = natural-transformation-eq $ fun-ext $ λ X → fun-ext $ λ f → begin
      NaturalTransformation.η (yoneda← Hom[ A ,-] A (lift $ id (C op))) X f 
        ≡⟨ refl ⟩
      (F₁ Hom[ A ,-] (lower f)) (lift $ id (C op) {A}) 
        ≡⟨ refl ⟩
      lift (lower f ∘C id (C op))
        ≡⟨ cong lift (left-id C) ⟩
      f
        ≡⟨⟩
      id SetCat f ∎
    
    compose-Emb : {a b c : Obj (C op)} {f : Hom (C op) a b} {g : Hom (C op) b c}
                → EmbF₁ (g ∘Cop f) ≡ (EmbF₁ g) ∘Func (EmbF₁ f)
    compose-Emb {a} {b} {c} {f} {g} = natural-transformation-eq $ fun-ext $ λ X → fun-ext $ λ h → begin
      NaturalTransformation.η (EmbF₁ (g ∘Cop f)) X h
        ≡⟨⟩
      (F₁ Hom[ c ,-] (lower h)) (lift $ g ∘Cop f) 
        ≡⟨⟩
      lift ((g ∘Cop f) ∘Cop (lower h)) 
        ≡⟨ cong lift (sym (assoc (C op))) ⟩
      lift (g ∘Cop (f ∘Cop lower h))
        ≡⟨⟩
      (F₁ Hom[ c ,-] (lower ((F₁ Hom[ b ,-] (lower h)) (lift f)))) (lift g)
        ≡⟨⟩
      NaturalTransformation.η (EmbF₁ g) X (NaturalTransformation.η (EmbF₁ f) X h)
        ≡⟨⟩
      NaturalTransformation.η (EmbF₁ g ∘Func EmbF₁ f) X h ∎
