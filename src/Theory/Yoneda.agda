
open import Level
open import Function hiding ( id ) renaming ( _∘_ to _∘F_)

open import Data.Product

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Extensionality

open import Theory.Category
open import Theory.Category.Isomorphism
open import Theory.Category.Examples renaming ( functorCategory to FunctorCat )

open import Theory.Functor

open import Theory.Natural.Transformation
open import Theory.Natural.Isomorphism


module Theory.Yoneda {ℓ₀ ℓ₁ : Level} {C : Category {ℓ₀} {ℓ₁}} where

open Category
open Functor hiding ( id )

private
  SetCat = setCategory {ℓ₁}
  _∘C_ = _∘_ C
  _∘Cop_ = _∘_ (C op)
  _∘Set_ = _∘_ SetCat
  _∘Func_ = _∘_ (FunctorCat C SetCat)
  _∘CSet×C_ = _∘_ $ FunctorCat C SetCat ×C C

-- Definition of the Hom-Functor Hom[A,-] from C to Set.
Hom[_,-] : (a : Obj C) → Functor C SetCat
Hom[_,-] a = functor HomF₀ HomF₁ id-HomF compose-HomF
  where
    HomF₀ : Obj C → Obj SetCat
    HomF₀ x = Hom C a x
    
    HomF₁ : {x y : Obj C} → Hom C x y → Hom SetCat (HomF₀ x) (HomF₀ y)
    HomF₁ f = λ g → f ∘C g
    
    id-HomF : {a : Obj C} → HomF₁ (id C {a}) ≡ id SetCat
    id-HomF {a} = begin
      HomF₁ (id C) 
        ≡⟨ refl ⟩
      ( λ g → id C ∘C g )
        ≡⟨ fun-ext (λ g → right-id C {f = g}) ⟩
      ( λ g → g )
        ≡⟨ refl ⟩
      id SetCat ∎
    
    compose-HomF : {a b c : Obj C} {f : Hom C a b} {g : Hom C b c} 
                 → HomF₁ (g ∘C f) ≡ (HomF₁ g) ∘Set (HomF₁ f)
    compose-HomF {f = f} {g} = begin
      HomF₁ (g ∘C f) 
        ≡⟨ refl ⟩
      ( λ h → (g ∘C f) ∘C h )
        ≡⟨ fun-ext (λ h → sym (assoc C {f = h} {f} {g})) ⟩ 
      ( λ h → g ∘C (f ∘C h) )
        ≡⟨ refl ⟩ 
      (HomF₁ g) ∘Set (HomF₁ f) ∎

yoneda→ : (F : Functor C SetCat) → (A : Obj C) → NaturalTransformation Hom[ A ,-] F → F₀ F A
yoneda→ F A (naturalTransformation η natural) = η A (id C {A})

yoneda← : (F : Functor C SetCat) → (A : Obj C) → F₀ F A → NaturalTransformation Hom[ A ,-] F
yoneda← F A FA = naturalTransformation η natural-η
  where
    η : (x : Obj C) → Hom SetCat ([ Hom[ A ,-] ]₀ x) ([ F ]₀ x)
    η x f = (F₁ F f) FA
    
    -- h A f = λ g → f ∘C g
    natural-η : {a b : Obj C} {f : Hom C a b} → ([ F ]₁ f) ∘Set (η a) ≡ (η b) ∘Set ([ Hom[ A ,-] ]₁ f)
    natural-η {a} {b} {f} = begin
      ([ F ]₁ f) ∘Set (η a) 
        ≡⟨ refl ⟩
      ( λ g → ([ F ]₁ f) (([ F ]₁ g) FA) )
        ≡⟨ fun-ext (λ g → cong (λ P → P FA) (sym $ compose F)) ⟩
      ( λ g → ([ F ]₁ (f ∘C g)) FA )
        ≡⟨ refl ⟩
      (η b) ∘Set ([ Hom[ A ,-] ]₁ f) ∎

yoneda-left-id : (F : Functor C SetCat) → (A : Obj C) → yoneda→ F A ∘F yoneda← F A ≡ (λ x → x)
yoneda-left-id F A = fun-ext p
  where
    p : (FA : F₀ F A) → (yoneda→ F A ∘F yoneda← F A) FA ≡ FA
    p FA with yoneda← F A FA 
    p FA | naturalTransformation η natural = begin
      F₁ F (id C) FA 
        ≡⟨ cong (λ P → P FA) (Functor.id F) ⟩
      FA ∎

yoneda-right-id : (F : Functor C SetCat) → (A : Obj C) → yoneda← F A ∘F yoneda→ F A ≡ (λ x → x)
yoneda-right-id F A = fun-ext $ λ NatTrans → natural-transformation-eq (p NatTrans)
  where
    p : (NatTrans : NaturalTransformation Hom[ A ,-] F) → NaturalTransformation.η (yoneda← F A (yoneda→ F A NatTrans)) ≡ NaturalTransformation.η NatTrans
    p (naturalTransformation η natural) = fun-ext $ λ x → fun-ext $ λ f → begin
      NaturalTransformation.η (yoneda← F A (yoneda→ F A (naturalTransformation η natural))) x f
        ≡⟨ refl ⟩
      ([ F ]₁ f ∘Set η A) (id C {A})
        ≡⟨ cong (λ P → P (id C {A})) (natural {A} {x} {f}) ⟩
      (η x ∘Set ([ Hom[ A ,-] ]₁ f)) (id C {A})
        ≡⟨ refl ⟩
      η x (f ∘C (id C {A}))
        ≡⟨ cong (η x) (left-id C) ⟩
      η x f ∎

{-
Obj→Functor : (F : Functor C SetCat) → (A : Obj C) → Functor (FunctorCat C SetCat ×C C ) SetCat
Obj→Functor F A = functor ObjF₀ ObjF₁ refl refl
  where
    ObjF₀ : Obj (FunctorCat C SetCat ×C C) → Obj SetCat
    ObjF₀ (G , x) = F₀ F A
    
    ObjF₁ : {x y : Obj (FunctorCat C SetCat ×C C)}
          → Hom (FunctorCat C SetCat ×C C) x y → Hom SetCat (ObjF₀ x) (ObjF₀ y)
    ObjF₁ {G , x} {H , y} (NatTrans , f) = id SetCat {F₀ F A}

NatTrans→Functor : (F : Functor C SetCat) → (A : Obj C) → NaturalTransformation Hom[ A ,-] F → Functor (FunctorCat C SetCat ×C C ) SetCat
NatTrans→Functor F A (naturalTransformation η natural) = functor NatTransF₀ NatTransF₁ {!!} {!!}
  where
    NatTransF₀ : Obj (FunctorCat C SetCat ×C C) → Obj SetCat
    NatTransF₀ (G , x) = F₀ G A
    -- yoneda→ F A (naturalTransformation η natural) = η A (id C {A})
    NatTransF₁ : {x y : Obj (FunctorCat C SetCat ×C C)}
               → Hom (FunctorCat C SetCat ×C C) x y → Hom SetCat (NatTransF₀ x) (NatTransF₀ y)
    NatTransF₁ {G , x} {H , y} (NatTrans , f) = {!!}
-}

YonedaEmbedding : Functor (C op) (FunctorCat C SetCat)
YonedaEmbedding = functor EmbF₀ EmbF₁ id-Emb compose-Emb
  where
    EmbF₀ : Obj (C op) → Obj (FunctorCat C SetCat)
    EmbF₀ A = Hom[ A ,-]
    
    EmbF₁ : {a b : Obj C} → Hom (C op) a b → Hom (FunctorCat C SetCat) Hom[ a ,-] Hom[ b ,-]
    EmbF₁ {a} {b} f = yoneda← Hom[ b ,-] a f
    
    id-Emb : {a : Obj (C op)} → EmbF₁ {a} {a} (id (C op)) ≡ id (FunctorCat C SetCat)
    id-Emb {A} = natural-transformation-eq $ fun-ext $ λ X → fun-ext $ λ f → begin
      NaturalTransformation.η (yoneda← Hom[ A ,-] A (id (C op))) X f 
        ≡⟨ refl ⟩
      (F₁ Hom[ A ,-] f) (id (C op) {A})
        ≡⟨ refl ⟩
      f ∘C id (C op)
        ≡⟨ left-id C ⟩
      f
        ≡⟨ refl ⟩
      id SetCat f ∎
    
    compose-Emb : {a b c : Obj (C op)} {f : Hom (C op) a b} {g : Hom (C op) b c}
                → EmbF₁ (g ∘Cop f) ≡ (EmbF₁ g) ∘Func (EmbF₁ f)
    compose-Emb {a} {b} {c} {f} {g} = natural-transformation-eq $ fun-ext $ λ X → fun-ext $ λ h → begin
      NaturalTransformation.η (EmbF₁ (g ∘Cop f)) X h
        ≡⟨ refl ⟩
      (F₁ Hom[ c ,-] h) (g ∘Cop f)
        ≡⟨ refl ⟩
      (g ∘Cop f) ∘Cop h
        ≡⟨ sym (assoc (C op)) ⟩
      g ∘Cop (f ∘Cop h) 
        ≡⟨ refl ⟩
      (F₁ Hom[ c ,-] ((F₁ Hom[ b ,-] h) f)) g
        ≡⟨ refl ⟩
      NaturalTransformation.η (EmbF₁ g) X (NaturalTransformation.η (EmbF₁ f) X h)
        ≡⟨ refl ⟩
      NaturalTransformation.η (EmbF₁ g ∘Func EmbF₁ f) X h ∎
