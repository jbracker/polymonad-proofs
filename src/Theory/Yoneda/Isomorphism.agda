
open import Level
open import Function hiding ( id ) renaming ( _∘_ to _∘F_)

open import Data.Product

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Extensionality

open import Theory.Category
open import Theory.Category.Isomorphism
open import Theory.Category.Examples renaming ( setCategory to SetCat' ; functorCategory to FunctorCat )

open import Theory.Functor

open import Theory.Natural.Transformation
open import Theory.Natural.Isomorphism

module Theory.Yoneda.Isomorphism {ℓ₀ ℓ₁ : Level} {C : Category {ℓ₀} {ℓ₁}} where

open Category
open Functor hiding ( id )

import Theory.Yoneda.HomFunctor
open Theory.Yoneda.HomFunctor {ℓ₀} {ℓ₁} {C}

import Theory.Yoneda.Bijection
open Theory.Yoneda.Bijection {ℓ₀} {ℓ₁} {C}

import Theory.Yoneda.Embedding
open Theory.Yoneda.Embedding {ℓ₀} {ℓ₁} {C}

private
  SetCat = SetCat' {ℓ₁}
  _∘C_ = _∘_ C
  _∘Cop_ = _∘_ (C op)
  _∘Set_ = _∘_ SetCat
  _∘Set'_ = _∘_ (SetCat' {suc ℓ₁ ⊔ ℓ₀})
  _∘Func_ = _∘_ (FunctorCat C SetCat)
  _∘CSet×C_ = _∘_ $ FunctorCat C SetCat ×C C

yonedaObjFunctor : Functor (FunctorCat C SetCat ×C C ) (SetCat' {suc ℓ₁ ⊔ ℓ₀})
yonedaObjFunctor = functor ObjF₀ ObjF₁ (λ {a} → id-ObjF {a}) (λ {a} {b} {c} {f} {g} → compose-ObjF {a} {b} {c} {f} {g})
  where
    open NaturalTransformation
    
    ObjF₀ : Obj (FunctorCat C SetCat ×C C) → Obj (SetCat' {suc ℓ₁ ⊔ ℓ₀})
    ObjF₀ (F , a) = Lift ([ F ]₀ a)
    
    ObjF₁ : {x y : Obj (FunctorCat C SetCat ×C C)}
          → Hom (FunctorCat C SetCat ×C C) x y → Hom (SetCat' {suc ℓ₁ ⊔ ℓ₀}) (ObjF₀ x) (ObjF₀ y)
    ObjF₁ {F , a} {G , b} (Φ , f) = lift ∘F ([ G ]₁ f ∘F η Φ a) ∘F lower -- same as 'η Φ b ∘ [ F ]₁ f' due to naturality 
    
    id-ObjF : {a : Obj (FunctorCat C SetCat ×C C)} → ObjF₁ {a} {a} (id (FunctorCat C SetCat ×C C)) ≡ id (SetCat' {suc ℓ₁ ⊔ ℓ₀})
    id-ObjF {F , a} = cong (λ P → lift ∘F P ∘F lower) $ begin
      [ F ]₁ (id C {a}) ∘F η Id⟨ F ⟩ a
        ≡⟨ refl ⟩
      [ F ]₁ (id C {a}) ∘F id SetCat {[ F ]₀ a}
        ≡⟨ left-id SetCat ⟩
      [ F ]₁ (id C {a})
        ≡⟨ Functor.id F ⟩
      id SetCat ∎
    
    compose-ObjF : {a b c : Obj (FunctorCat C SetCat ×C C)}
                 → {f : Hom (FunctorCat C SetCat ×C C) a b} {g : Hom (FunctorCat C SetCat ×C C) b c}
                 → ObjF₁ (g ∘CSet×C f) ≡ ObjF₁ g ∘Set' ObjF₁ f
    compose-ObjF {F , a} {G , b} {H , c} {Φ , f} {Ψ , g} = cong (λ P → lift ∘F P ∘F lower) $ begin
      [ H ]₁ (g ∘C f) ∘F η ⟨ Ψ ⟩∘ᵥ⟨ Φ ⟩ a
        ≡⟨ cong (λ P → P ∘F η ⟨ Ψ ⟩∘ᵥ⟨ Φ ⟩ a) (compose H) ⟩
      ([ H ]₁ g ∘F [ H ]₁ f) ∘F η ⟨ Ψ ⟩∘ᵥ⟨ Φ ⟩ a
        ≡⟨ sym (assoc SetCat {f = η ⟨ Ψ ⟩∘ᵥ⟨ Φ ⟩ a} {[ H ]₁ f} {[ H ]₁ g}) ⟩
      [ H ]₁ g ∘F ([ H ]₁ f ∘F η ⟨ Ψ ⟩∘ᵥ⟨ Φ ⟩ a)
        ≡⟨ cong (λ P → [ H ]₁ g ∘F P) (natural ⟨ Ψ ⟩∘ᵥ⟨ Φ ⟩) ⟩
      [ H ]₁ g ∘F (η ⟨ Ψ ⟩∘ᵥ⟨ Φ ⟩ b ∘F [ F ]₁ f)
        ≡⟨ refl ⟩
      [ H ]₁ g ∘F (η Ψ b ∘F (η Φ b ∘F [ F ]₁ f))
        ≡⟨ cong (λ P → [ H ]₁ g ∘F (η Ψ b ∘F P)) (sym (natural Φ)) ⟩
      [ H ]₁ g ∘F (η Ψ b ∘F ([ G ]₁ f ∘F η Φ a))
        ≡⟨ assoc SetCat {f = [ G ]₁ f ∘F η Φ a} {η Ψ b} {[ H ]₁ g} ⟩
      ([ H ]₁ g ∘F η Ψ b) ∘F ([ G ]₁ f ∘F η Φ a) ∎

yonedaNatTransFunctor : Functor (FunctorCat C SetCat ×C C ) (SetCat' {suc ℓ₁ ⊔ ℓ₀})
yonedaNatTransFunctor = functor NatTransF₀ NatTransF₁ id-NatTransF (λ {a} {b} {c} {f} {g} → compose-NatTransF {a} {b} {c} {f} {g})
  where
    NatTransF₀ : Obj (FunctorCat C SetCat ×C C) → Obj (SetCat' {ℓ₀ ⊔ suc ℓ₁})
    NatTransF₀ (F , a) = NaturalTransformation Hom[ a ,-] F
    
    NatTransF₁ : {x y : Obj (FunctorCat C SetCat ×C C)}
               → Hom (FunctorCat C SetCat ×C C) x y → Hom (SetCat' {ℓ₀ ⊔ suc ℓ₁}) (NatTransF₀ x) (NatTransF₀ y)
    NatTransF₁ {F , a} {G , b} (Φ , f) Ψ = Φ ∘Func (Ψ ∘Func [ YonedaEmbedding ]₁ f)

    id-NatTransF : {a : Obj (FunctorCat C SetCat ×C C)} → NatTransF₁ {a} {a} (id (FunctorCat C SetCat ×C C)) ≡ id SetCat'
    id-NatTransF {F , a} = begin
      NatTransF₁ (id (FunctorCat C SetCat ×C C))
        ≡⟨⟩
      (λ Ψ → Id⟨ F ⟩ ∘Func (Ψ ∘Func [ YonedaEmbedding ]₁ (id C {a})))
        ≡⟨ fun-ext (λ Ψ → right-id (FunctorCat C SetCat)) ⟩
      (λ Ψ → Ψ ∘Func [ YonedaEmbedding ]₁ (id C {a}))
        ≡⟨ fun-ext (λ Ψ → cong (λ P → Ψ ∘Func P) (Functor.id YonedaEmbedding)) ⟩
      (λ Ψ → Ψ ∘Func id (FunctorCat C SetCat))
        ≡⟨ fun-ext (λ Ψ → left-id (FunctorCat C SetCat)) ⟩
      (λ Ψ → Ψ)
        ≡⟨⟩
      id SetCat' ∎ 
    
    compose-NatTransF : {a b c : Obj (FunctorCat C SetCat ×C C)}
                      → {f : Hom (FunctorCat C SetCat ×C C) a b} {g : Hom (FunctorCat C SetCat ×C C) b c}
                      → NatTransF₁ (g ∘CSet×C f) ≡ NatTransF₁ g ∘Set' NatTransF₁ f
    compose-NatTransF {F , a} {G , b} {H , c} {Φ , f} {Ψ , g} = begin
      NatTransF₁ ((Ψ , g) ∘CSet×C (Φ , f)) 
        ≡⟨⟩
      (λ Θ → (Ψ ∘Func Φ) ∘Func (Θ ∘Func [ YonedaEmbedding ]₁ (g ∘C f)) )
        ≡⟨ fun-ext (λ Θ → cong (λ P → (Ψ ∘Func Φ) ∘Func (Θ ∘Func P)) (compose YonedaEmbedding)) ⟩
      (λ Θ → (Ψ ∘Func Φ) ∘Func (Θ ∘Func ([ YonedaEmbedding ]₁ f ∘Func [ YonedaEmbedding ]₁ g)))
        ≡⟨ fun-ext (λ Θ → cong (λ P → (Ψ ∘Func Φ) ∘Func P) (assoc (FunctorCat C SetCat) {f = [ YonedaEmbedding ]₁ g} {[ YonedaEmbedding ]₁ f} {Θ})) ⟩
      (λ Θ → (Ψ ∘Func Φ) ∘Func ((Θ ∘Func [ YonedaEmbedding ]₁ f) ∘Func [ YonedaEmbedding ]₁ g))
        ≡⟨ fun-ext (λ Θ → assoc (FunctorCat C SetCat) {f = [ YonedaEmbedding ]₁ g} {Θ ∘Func [ YonedaEmbedding ]₁ f} {Ψ ∘Func Φ}) ⟩
      (λ Θ → ((Ψ ∘Func Φ) ∘Func (Θ ∘Func [ YonedaEmbedding ]₁ f)) ∘Func [ YonedaEmbedding ]₁ g)
        ≡⟨ fun-ext (λ Θ → cong (λ P → P ∘Func [ YonedaEmbedding ]₁ g) (sym (assoc (FunctorCat C SetCat) {f = Θ ∘Func [ YonedaEmbedding ]₁ f} {Φ} {Ψ}))) ⟩
      (λ Θ → (Ψ ∘Func (Φ ∘Func (Θ ∘Func [ YonedaEmbedding ]₁ f))) ∘Func [ YonedaEmbedding ]₁ g)
        ≡⟨ fun-ext (λ Θ → sym (assoc (FunctorCat C SetCat) {f = [ YonedaEmbedding ]₁ g} {Φ ∘Func (Θ ∘Func [ YonedaEmbedding ]₁ f)} {Ψ})) ⟩
      (λ Θ → Ψ ∘Func ((Φ ∘Func (Θ ∘Func [ YonedaEmbedding ]₁ f)) ∘Func [ YonedaEmbedding ]₁ g))
        ≡⟨⟩
      (λ Θ → Ψ ∘Func (Θ ∘Func [ YonedaEmbedding ]₁ g)) ∘F (λ Θ → Φ ∘Func (Θ ∘Func [ YonedaEmbedding ]₁ f))
        ≡⟨⟩
      NatTransF₁ (Ψ , g) ∘Set' NatTransF₁ (Φ , f) ∎

yoneda-isomorphism : NaturalIsomorphism yonedaObjFunctor yonedaNatTransFunctor
yoneda-isomorphism = naturalIsomorphism (naturalTransformation η (λ {a} {b} {f} → natural {a} {b} {f})) iso
  where
    η : (F×a : Obj (FunctorCat C SetCat ×C C)) → Lift ([ proj₁ F×a ]₀ (proj₂ F×a)) → NaturalTransformation Hom[ proj₂ F×a ,-] (proj₁ F×a)
    η (F , a) (lift Fa) = naturalTransformation η' natural'
      where
        η' : (x : Obj C) → [ Hom[ a ,-] ]₀ x → [ F ]₀ x
        η' x f = [ F ]₁ f Fa

        natural' : {x y : Obj C} {f : Hom C x y} → [ F ]₁ f ∘Set η' x ≡ η' y ∘Set [ Hom[ a ,-] ]₁ f
        natural' {x} {y} {f} = begin
          [ F ]₁ f ∘Set η' x 
            ≡⟨⟩
          [ F ]₁ f ∘F (λ g → [ F ]₁ g Fa) 
            ≡⟨⟩
          (λ g → [ F ]₁ f ([ F ]₁ g Fa))
            ≡⟨ fun-ext (λ g → sym (cong (λ P → P Fa) (compose F))) ⟩
          (λ g → [ F ]₁ (f ∘C g) Fa)
            ≡⟨⟩
          (λ g → [ F ]₁ g Fa) ∘F (λ g → f ∘C g)
            ≡⟨⟩
          η' y ∘Set [ Hom[ a ,-] ]₁ f ∎
    
    natural : {a b : Obj (FunctorCat C SetCat ×C C)} {f : Hom (FunctorCat C SetCat ×C C) a b} 
            → ([ yonedaNatTransFunctor ]₁ f) ∘Set' (η a) ≡ (η b) ∘Set' ([ yonedaObjFunctor ]₁ f)
    natural {F , a} {G , b} {Φ , f} = fun-ext $ λ Fa → begin
      ([ yonedaNatTransFunctor ]₁ (Φ , f) ∘Set' η (F , a)) Fa
        ≡⟨⟩
      Φ ∘Func (η (F , a) Fa ∘Func yoneda← Hom[ a ,-] b f)
        ≡⟨ natural-transformation-eq (fun-ext $ p Fa) ⟩
      η (G , b) ((lift ∘F [ G ]₁ f ∘F NaturalTransformation.η Φ a ∘F lower) Fa)
        ≡⟨⟩
      (η (G , b) ∘Set' [ yonedaObjFunctor ]₁ (Φ , f)) Fa ∎
      where
        p : (Fa : Lift ([ F ]₀ a)) → (x : Obj C) 
          → NaturalTransformation.η (Φ ∘Func (η (F , a) Fa ∘Func yoneda← Hom[ a ,-] b f)) x 
          ≡ NaturalTransformation.η (η (G , b) ((lift ∘F [ G ]₁ f ∘F NaturalTransformation.η Φ a ∘F lower) Fa)) x
        p (lift Fa) x = fun-ext $ λ g → begin
          NaturalTransformation.η (Φ ∘Func (η (F , a) (lift Fa) ∘Func yoneda← Hom[ a ,-] b f)) x g
            ≡⟨⟩
          NaturalTransformation.η Φ x (NaturalTransformation.η (η (F , a) (lift Fa)) x (NaturalTransformation.η (yoneda← Hom[ a ,-] b f) x g))
            ≡⟨ cong (NaturalTransformation.η Φ x) (cong (λ P → P Fa) (compose F)) ⟩
          NaturalTransformation.η Φ x ([ F ]₁ g ([ F ]₁ f Fa))
            ≡⟨ cong (λ P → P ([ F ]₁ f Fa)) (sym $ NaturalTransformation.natural Φ) ⟩
          [ G ]₁ g (NaturalTransformation.η Φ b ([ F ]₁ f Fa))
            ≡⟨ cong ([ G ]₁ g) (cong (λ P → P Fa) (sym $ NaturalTransformation.natural Φ)) ⟩
          [ G ]₁ g ([ G ]₁ f (NaturalTransformation.η Φ a Fa))
            ≡⟨⟩
          NaturalTransformation.η (η (G , b) ((lift ∘F [ G ]₁ f ∘F NaturalTransformation.η Φ a) Fa)) x g ∎
    
    iso : (x : Obj (FunctorCat C SetCat ×C C)) → Isomorphism SetCat' (η x)
    iso {F , a} = isomorphism (lift ∘F inv) iso-left-id (fun-ext iso-right-id)
      where
        inv : NaturalTransformation Hom[ a ,-] F -> [ F ]₀ a
        inv (naturalTransformation η natural) = η a (id C)
        
        iso-left-id : η (F , a) ∘Set' (lift ∘F inv) ≡ id SetCat'
        iso-left-id = fun-ext $ λ Φ → natural-transformation-eq $ fun-ext $ λ x → fun-ext $ λ f → begin
          [ F ]₁ f (inv Φ)
            ≡⟨⟩
          ([ F ]₁ f ∘F NaturalTransformation.η Φ a) (id C {a})
            ≡⟨ cong (λ P → P (id C {a})) (NaturalTransformation.natural Φ) ⟩
          (NaturalTransformation.η Φ x ∘F [ Hom[ a ,-] ]₁ f) (id C {a})
            ≡⟨⟩
          NaturalTransformation.η Φ x ([ Hom[ a ,-] ]₁ f (id C {a}))
            ≡⟨⟩
          NaturalTransformation.η Φ x (f ∘C (id C {a}))
            ≡⟨ cong (NaturalTransformation.η Φ x) (left-id C) ⟩
          NaturalTransformation.η Φ x f ∎
        
        iso-right-id : (Fa : Lift ([ F ]₀ a)) → ((lift ∘F inv) ∘Set' η (F , a)) Fa ≡ (id SetCat') Fa
        iso-right-id (lift Fa) = begin
          ((lift ∘F inv) ∘Set' η (F , a)) (lift Fa) 
            ≡⟨⟩ 
          lift ( inv (η (F , a) (lift Fa)) )
            ≡⟨⟩ 
          lift ( NaturalTransformation.η (η (F , a) (lift Fa)) a (id C) )
            ≡⟨⟩ 
          lift ( [ F ]₁ (id C) Fa )
            ≡⟨ cong (λ P → lift (P Fa)) (Functor.id F) ⟩ 
          lift Fa
            ≡⟨⟩ 
          (id SetCat') (lift Fa) ∎
