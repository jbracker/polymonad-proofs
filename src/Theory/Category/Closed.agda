
open import Level renaming ( zero to lzero ; suc to lsuc )
open import Function using ( _$_ )

open import Data.Unit
open import Data.Product renaming ( _,_ to _,'_ )

open import Relation.Binary.PropositionalEquality

open import Theory.Category hiding ( category )
open import Theory.Functor
open import Theory.Functor.Application
import Theory.Functor.Composition
open import Theory.Natural.Isomorphism
open import Theory.Natural.Transformation
open import Theory.Natural.DinaturalTransformation
open import Theory.Natural.ExtranaturalTransformation

module Theory.Category.Closed where

-------------------------------------------------------------------------------
-- Definition of Closed Categories
-------------------------------------------------------------------------------
record ClosedCategory {ℓC₀ ℓC₁ : Level} (C : Category {ℓC₀} {ℓC₁}) : Set (lsuc (ℓC₀ ⊔ ℓC₁)) where
  constructor closedCategory

  category = C
  open Category
  private
    _∘C_ = _∘_ C
    _∘Cop_ = _∘_ (C op)
  
  field
    InternalHom : Functor (C op ×C C) C
    
    I : Obj C
  
  [_,_]₀ : Obj (C op) → Obj C → Obj C
  [_,_]₀ c' c = Functor.F₀ InternalHom (c' ,' c)
  
  [_,_]₁ : {a b : Obj (C op)} {c d : Obj C}
         → Hom (C op) a b → Hom C c d
         → Hom C [ a , c ]₀ [ b , d ]₀
  [_,_]₁ f' f = Functor.F₁ InternalHom (f' ,' f) 
  
  open Theory.Functor.Application.BiFunctor
  
  field
    i : NaturalIsomorphism Id[ C ] ([ I ,-] InternalHom)

    j : (a : Obj C) → Hom C I [ a , a ]₀
    
    L : (a b c : Obj C) → Hom C [ b , c ]₀ [ [ a , b ]₀ , [ a , c ]₀ ]₀

    j-extranatural-a : {a a' : Obj C} (f : Hom C a a') 
                     → [ f , id C ]₁ ∘C (j a') ≡ [ id (C op) , f ]₁ ∘C (j a)
    
    L-natural-c : (a : Obj C) → (b : Obj (C op)) → {c c' : Obj C} {f : Hom C c c'}
                → ([ [ id C {a} , id C {b} ]₁ , [ id C {a} , f ]₁ ]₁) ∘C (L a b c) ≡ (L a b c') ∘C ([ id C {b} , f ]₁)
    
    L-natural-b : (a c : Obj C) → {b b' : Obj C} {f : Hom C b b'}
                → ([ [ id C {a} , f ]₁ , [ id C {a} , id C {c} ]₁ ]₁) ∘C (L a b' c) ≡ (L a b c) ∘C ([ f , id C {c} ]₁)
    
    L-extranatural-a : (b : Obj (C op)) → (c : Obj C) → {a a' : Obj C} (f : Hom C a a') 
                     → [ id C , [ f , id C {c} ]₁ ]₁ ∘C (L a' b c) ≡ [ [ f , id (C op) {b} ]₁ , id C ]₁ ∘C (L a b c)
  
  open Theory.Functor.Composition.BiFunctor
  
  -- [b,-] → [[a,b],[a,-]] is a natural transformation
  L-natural-transformation : (a b : Obj (C op))
                           → NaturalTransformation
                             ([ b ,-] InternalHom)
                             ([⊤, [ [ [ a , b ] InternalHom ]op , [ a ,-] InternalHom ]∘[ InternalHom ] ])
  L-natural-transformation a b = naturalTransformation (λ x → L a b x) (L-natural-c a b)

  -- [-,c] → [[a,-],[a,c]] is a natural transformation
  L-natural-transformation-op : (a : Obj (C op)) → (c : Obj C)
                              → NaturalTransformation
                                ([-, c ] InternalHom)
                                ([ [ [ [ a ,-] InternalHom ]op , [ a , c ] InternalHom ]∘[ InternalHom ] ,⊤])
  L-natural-transformation-op a c = naturalTransformation (λ x → L a x c) (L-natural-b a c)
  
  open import Theory.Triple
  open ≡-Reasoning
  private
    _∘⊤⊤⊤_ = _∘_ (⊤-Cat ×C ⊤-Cat op ×C ⊤-Cat)
    
  
  LeftExtraFunctor-j : Functor (⊤-Cat ×C (⊤-Cat op) ×C ⊤-Cat) C
  LeftExtraFunctor-j = functor (λ _ → I) (λ _ → id C {I}) refl (sym $ left-id C)
  
  RightExtraFunctor-j : Functor (⊤-Cat ×C (C op) ×C C) C
  RightExtraFunctor-j = functor rightObj rightHom (Functor.id InternalHom) (Functor.compose InternalHom)
    where
      rightObj : Obj (⊤-Cat ×C C op ×C C) → Obj C
      rightObj (tt , a⁻ , a⁺) = [ a⁻ , a⁺ ]₀
      
      rightHom : {a b : Obj (⊤-Cat ×C C op ×C C)} 
               → Hom (⊤-Cat ×C C op ×C C) a b → Hom C (rightObj a) (rightObj b)
      rightHom (tt , f⁻ , f⁺) = [ f⁻ , f⁺ ]₁
  
  j-extranatural-transformation : ExtranaturalTransformation LeftExtraFunctor-j RightExtraFunctor-j
  j-extranatural-transformation = record
    { η = λ _ _ a → j a
    ; η-natural = λ _ c {_} {_} {_} → j-natural c
    ; extranatural = λ _ _ {a} {a'} f → j-extranatural-a {a} {a'} f
    ; extranatural-op = λ _ _ {_} {_} _ → refl
    } where
      j-natural : (c : Obj C) → [ id (C op) {c} , id C {c} ]₁ ∘C j c ≡ j c ∘C id C {I}
      j-natural c = begin
        [ id (C op) {c} , id C {c} ]₁ ∘C j c 
          ≡⟨ cong (λ X → X ∘C j c) (Functor.id InternalHom) ⟩
        id C ∘C j c 
          ≡⟨ right-id C ⟩
        j c 
          ≡⟨ sym $ left-id C ⟩
        j c ∘C id C {I} ∎
  
  LeftExtraFunctor-L : Obj (C op) → Obj C → Functor (⊤-Cat ×C (⊤-Cat op) ×C ⊤-Cat) C
  LeftExtraFunctor-L b c = functor leftObj leftHom (Functor.id InternalHom) compose
    where
      leftObj : Obj (⊤-Cat ×C ⊤-Cat op ×C ⊤-Cat) → Obj C
      leftObj (tt , tt , tt) = [ b , c ]₀
      
      leftHom : {x y : Obj (⊤-Cat ×C ⊤-Cat op ×C ⊤-Cat)} 
              → Hom (⊤-Cat ×C ⊤-Cat op ×C ⊤-Cat) x y →  Hom C (leftObj x) (leftObj y)
      leftHom (tt , tt , tt) = [ id (C op) {b} , id C {c} ]₁
      
      compose : {x y z : Obj (⊤-Cat ×C ⊤-Cat op ×C ⊤-Cat)}
              → {f : Hom (⊤-Cat ×C ⊤-Cat op ×C ⊤-Cat) x y} {g : Hom (⊤-Cat ×C ⊤-Cat op ×C ⊤-Cat) y z}
              → leftHom (g ∘⊤⊤⊤ f) ≡ leftHom g ∘C leftHom f
      compose {tt , tt , tt} {tt , tt , tt} {tt , tt , tt} {tt , tt , tt} {tt , tt , tt} = begin
        leftHom ((tt , tt , tt) ∘⊤⊤⊤ (tt , tt , tt))
          ≡⟨⟩
        [ id (C op) {b} , id C {c} ]₁
          ≡⟨ cong₂ [_,_]₁ (sym $ left-id (C op)) (sym $ left-id C) ⟩
        [ id (C op) {b} ∘Cop id (C op) {b} , id C {c} ∘C id C {c} ]₁
          ≡⟨ Functor.compose InternalHom ⟩
        [ id (C op) {b} , id C {c} ]₁ ∘C [ id (C op) {b} , id C {c} ]₁
          ≡⟨⟩
        leftHom (tt , tt , tt) ∘C leftHom (tt , tt , tt) ∎

  RightExtraFunctor-L : Obj (C op) → Obj C → Functor (⊤-Cat ×C (C op) ×C C) C
  RightExtraFunctor-L b c 
    = functor rightObj rightHom (trans (cong₂ [_,_]₁ (Functor.id InternalHom) (Functor.id InternalHom)) (Functor.id InternalHom)) compose 
    where
      _∘⊤CC_ = _∘_ (⊤-Cat ×C C op ×C C)
      
      rightObj : Obj (⊤-Cat ×C C op ×C C) → Obj C
      rightObj (tt , a⁻ , a⁺) = [ [ a⁺ , b ]₀ , [ a⁻ , c ]₀ ]₀

      rightHom : {x y : Obj (⊤-Cat ×C C op ×C C)} 
               → Hom (⊤-Cat ×C C op ×C C) x y → Hom C (rightObj x) (rightObj y)
      rightHom (tt , f⁻ , f⁺) = [ [ f⁺ , id (C op) {b} ]₁ , [ f⁻ , id C {c} ]₁ ]₁
      
      compose : {x y z : Obj (⊤-Cat ×C C op ×C C)}
              → {f : Hom (⊤-Cat ×C C op ×C C) x y} {g : Hom (⊤-Cat ×C C op ×C C) y z}
              → rightHom (g ∘⊤CC f) ≡ rightHom g ∘C rightHom f
      compose {x} {y} {z} {tt , f⁻ , f⁺} {tt , g⁻ , g⁺} = begin
        rightHom (tt , (f⁻ ∘C g⁻) , (g⁺ ∘C f⁺))
          ≡⟨⟩
        [ [ (g⁺ ∘C f⁺) , id (C op) {b} ]₁ , [ (g⁻ ∘Cop f⁻) , id C {c} ]₁ ]₁
          ≡⟨ cong₂ (λ X Y → [ [ (g⁺ ∘C f⁺) , X ]₁ , [ (g⁻ ∘Cop f⁻) , Y ]₁ ]₁) (sym $ left-id (C op)) (sym $ left-id C) ⟩
        [ [ (g⁺ ∘C f⁺) , id (C op) {b} ∘Cop id (C op) {b} ]₁ , [ (g⁻ ∘Cop f⁻) , id C {c} ∘C id C {c} ]₁ ]₁
          ≡⟨ cong₂ [_,_]₁ (Functor.compose InternalHom) (Functor.compose InternalHom) ⟩
        [ [ f⁺ , id (C op) {b} ]₁ ∘C [ g⁺ , id (C op) {b} ]₁ , [ g⁻ , id C {c} ]₁ ∘C [ f⁻ , id C {c} ]₁ ]₁
          ≡⟨ Functor.compose InternalHom ⟩
        [ [ g⁺ , id (C op) {b} ]₁ , [ g⁻ , id C {c} ]₁ ]₁ ∘C [ [ f⁺ , id (C op) {b} ]₁ , [ f⁻ , id C {c} ]₁ ]₁
          ≡⟨⟩
        rightHom (tt , g⁻ , g⁺) ∘C rightHom (tt , f⁻ , f⁺) ∎
  
  L-extranatural-transformation : (b : Obj (C op)) → (c : Obj C)
                                → ExtranaturalTransformation (LeftExtraFunctor-L b c) (RightExtraFunctor-L b c)
  L-extranatural-transformation b c = record
    { η = η
    ; η-natural = λ b' c' {x} {y} {f} → L-natural-c c' b {c} {c} {id C {c}}
    ; extranatural = λ _ _ → extranatural
    ; extranatural-op = λ _ a {_} {_} f → refl
    } where
      η : (x y : ⊤) (z : Obj C) → Hom C ([ LeftExtraFunctor-L b c ]₀ (x , y , y)) ([ RightExtraFunctor-L b c ]₀ (x , z , z))
      η tt tt a = L a b c
      
      extranatural : {z z' : Obj C} (f : Hom C z z') 
                   → [ [ id C , id (C op) {b} ]₁ , [ f , id C {c} ]₁ ]₁ ∘C (L z' b c)
                   ≡ [ [ f , id (C op) {b} ]₁ , [ id (C op) , id C {c} ]₁ ]₁ ∘C (L z b c)
      extranatural {z} {z'} f = begin
        [ [ id C , id (C op) {b} ]₁ , [ f , id C {c} ]₁ ]₁ ∘C (L z' b c)
          ≡⟨ cong (λ X → [ X , [ f , id C {c} ]₁ ]₁ ∘C (L z' b c)) (Functor.id InternalHom) ⟩
        [ id C , [ f , id C {c} ]₁ ]₁ ∘C (L z' b c)
          ≡⟨ L-extranatural-a b c {z} {z'} f ⟩
        [ [ f , id (C op) {b} ]₁ , id C ]₁ ∘C (L z b c)
          ≡⟨ cong (λ X → [ [ f , id (C op) {b} ]₁ , X ]₁ ∘C L z b c) (sym $ Functor.id InternalHom) ⟩
        [ [ f , id (C op) {b} ]₁ , [ id (C op) , id C {c} ]₁ ]₁ ∘C (L z b c) ∎
  
  LeftExtraFunctor : Functor ((C op ×C C) ×C ⊤-Cat op ×C ⊤-Cat) C
  LeftExtraFunctor = functor LeftObj LeftHom (Functor.id InternalHom) (Functor.compose InternalHom)
    where
      LeftObj : Obj (((C op) ×C C) ×C ⊤-Cat op ×C ⊤-Cat) → Obj C
      LeftObj ((b ,' c) , tt , tt) = [ b , c ]₀
      
      LeftHom : {a b : Obj (((C op) ×C C) ×C ⊤-Cat op ×C ⊤-Cat)}
              → Hom (((C op) ×C C) ×C ⊤-Cat op ×C ⊤-Cat) a b → Hom C (LeftObj a) (LeftObj b)
      LeftHom ((fb ,' fc) , tt , tt) = [ fb , fc ]₁
  
  RightExtraFunctor : Functor ((C op ×C C) ×C C op ×C C) C
  RightExtraFunctor = functor RightObj RightHom 
                              (trans (cong₂ [_,_]₁ (Functor.id InternalHom) (Functor.id InternalHom)) (Functor.id InternalHom)) 
                              (trans (cong₂ [_,_]₁ (Functor.compose InternalHom) (Functor.compose InternalHom)) (Functor.compose InternalHom))
    where
      _∘CCCC_ = _∘_ ((C op ×C C) ×C C op ×C C)
      
      RightObj : Obj (((C op) ×C C) ×C C op ×C C) → Obj C
      RightObj ((b ,' c) , a⁻ , a⁺) = [ [ a⁺ , b ]₀ , [ a⁻ , c ]₀ ]₀
      
      RightHom : {a b : Obj (((C op) ×C C) ×C C op ×C C)}
              → Hom (((C op) ×C C) ×C C op ×C C) a b → Hom C (RightObj a) (RightObj b)
      RightHom ((fb ,' fc) , fa⁻ , fa⁺) = [ [ fa⁺ , fb ]₁ , [ fa⁻ , fc ]₁ ]₁
  
  private
    InternalHom-compose-eq : {b b' : Obj C} {c c' : Obj (C op)} {f : Hom C b b'} {g : Hom (C op) c c'} 
                           → [ g , id C ]₁ ∘C [ id (C op) , f ]₁ ≡ [ g , f ]₁
    InternalHom-compose-eq = trans (sym $ Functor.compose InternalHom) (cong₂ [_,_]₁ (right-id C) (left-id (C op)))
  
  L-natural-bc : (a : Obj C) 
               → {b b' : Obj (C op)} {c c' : Obj C}
               → {f : Hom (C op) b b'} {g : Hom C c c'}
               → [ [ id C {a} , f ]₁ , [ id C {a} , g ]₁ ]₁ ∘C L a b c 
               ≡ L a b' c' ∘C [ f , g ]₁
  L-natural-bc a {b} {b'} {c} {c'} {f} {g} = begin
    [ [ id C {a} , f ]₁ , [ id C {a} , g ]₁ ]₁ ∘C L a b c
      ≡⟨ cong (λ X → X ∘C L a b c) (sym $ InternalHom-compose-eq) ⟩
    ([ [ id C {a} , f ]₁ , id C ]₁ ∘C [ id (C op) , [ id C {a} , g ]₁ ]₁) ∘C L a b c
      ≡⟨ sym (assoc C) ⟩
    [ [ id C {a} , f ]₁ , id C ]₁ ∘C ([ id (C op) , [ id C {a} , g ]₁ ]₁ ∘C L a b c)
      ≡⟨ cong₂ (λ X Y → [ [ id C {a} , f ]₁ , X ]₁ ∘C ([ Y , [ id C {a} , g ]₁ ]₁ ∘C L a b c)) (sym $ Functor.id InternalHom) (sym $ Functor.id InternalHom) ⟩
    [ [ id C {a} , f ]₁ , [ id C , id C ]₁ ]₁ ∘C ([ [ id (C op) , id (C op) ]₁ , [ id C {a} , g ]₁ ]₁ ∘C L a b c)
      ≡⟨ cong (λ X → [ [ id C {a} , f ]₁ , [ id C , id C ]₁ ]₁ ∘C X) (L-natural-c a b {c} {c'} {g}) ⟩
    [ [ id C {a} , f ]₁ , [ id C , id C ]₁ ]₁ ∘C (L a b c' ∘C [ id C {b} , g ]₁)
      ≡⟨ assoc C ⟩
    ([ [ id C {a} , f ]₁ , [ id C , id C ]₁ ]₁ ∘C L a b c') ∘C [ id C {b} , g ]₁
      ≡⟨ cong (λ X → X ∘C [ id C {b} , g ]₁) (L-natural-b a c' {b'} {b} {f}) ⟩
    (L a b' c' ∘C [ f , id C {c'} ]₁) ∘C [ id C {b} , g ]₁
      ≡⟨ sym (assoc C) ⟩
    L a b' c' ∘C ([ f , id C {c'} ]₁ ∘C [ id C {b} , g ]₁)
      ≡⟨ cong (λ X → L a b' c' ∘C X) InternalHom-compose-eq ⟩
    L a b' c' ∘C [ f , g ]₁ ∎
  
  extranatural-transformation : ExtranaturalTransformation LeftExtraFunctor RightExtraFunctor
  extranatural-transformation = record
    { η = η
    ; η-natural = λ _ a {x} {y} {f} → L-natural-bc a {proj₁ x} {proj₁ y} {proj₂ x} {proj₂ y} {proj₁ f} {proj₂ f}
    ; extranatural = extranatural
    ; extranatural-op = λ a c f → refl
    } where
      η : (a : Obj (C op ×C C)) (b : ⊤) (c : Obj C) → Hom C ([ LeftExtraFunctor ]₀ (a , b , b)) ([ RightExtraFunctor ]₀ (a , c , c))
      η (b ,' c) tt a = L a b c
      
      extranatural : (a : Σ (Obj (C op)) (λ x → Obj C)) (b : ⊤) {c c' : Obj C}
                   → (f : Hom C c c')
                   → [ [ id C , id C ]₁ , [ f , id C ]₁ ]₁ ∘C η a b c'
                   ≡ [ [ f , id C ]₁ , [ id C , id C ]₁ ]₁ ∘C η a b c
      extranatural (a ,' a') tt {c} {c'} f = begin
        [ [ id C , id C ]₁ , [ f , id C ]₁ ]₁ ∘C L c' a a'
          ≡⟨ cong (λ X → [ X , [ f , id C ]₁ ]₁ ∘C L c' a a') (Functor.id InternalHom) ⟩
        [ id C , [ f , id C ]₁ ]₁ ∘C L c' a a'
          ≡⟨ L-extranatural-a a a' f ⟩
        [ [ f , id C ]₁ , id C ]₁ ∘C L c a a'
          ≡⟨ cong (λ X → [ [ f , id C ]₁ , X ]₁ ∘C L c a a') (sym $ Functor.id InternalHom) ⟩
        [ [ f , id C ]₁ , [ id C , id C ]₁ ]₁ ∘C L c a a' ∎
      
  open Category C public

-------------------------------------------------------------------------------
-- Equality of Closed Categories
-------------------------------------------------------------------------------

private
  module Equality {ℓC₀ ℓC₁ : Level} {C : Category {ℓC₀} {ℓC₁}} where
    open import Data.Product

    open import Relation.Binary.HeterogeneousEquality using ( _≅_ ; refl )
    
    open import Congruence
    open import Extensionality
    open Category
    open Functor hiding ( id )
    open Theory.Functor.Application.BiFunctor
    
    private
      _∘C_ = _∘_ C

    closed-category-eq : {InternalHom₀ : Functor (C op ×C C) C}
                       → {InternalHom₁ : Functor (C op ×C C) C}
                       → {I₀ : Obj C} {I₁ : Obj C}
                       → {i₀ : NaturalIsomorphism Id[ C ] ([ I₀ ,-] InternalHom₀)}
                       → {i₁ : NaturalIsomorphism Id[ C ] ([ I₁ ,-] InternalHom₁)}
                       → {j₀ : (a : Obj C) → Hom C I₀ (F₀ InternalHom₀ (a , a))}
                       → {j₁ : (a : Obj C) → Hom C I₁ (F₀ InternalHom₁ (a , a))}
                       → {L₀ : (a b c : Obj C) → Hom C (F₀ InternalHom₀ (b , c)) (F₀ InternalHom₀ (F₀ InternalHom₀ (a , b) , F₀ InternalHom₀ (a , c)))}
                       → {L₁ : (a b c : Obj C) → Hom C (F₀ InternalHom₁ (b , c)) (F₀ InternalHom₁ (F₀ InternalHom₁ (a , b) , F₀ InternalHom₁ (a , c)))}
                       → {j-extranatural-a₀ : {a a' : Obj C} (f : Hom C a a') → (F₁ InternalHom₀ (f , id C)) ∘C (j₀ a') ≡ F₁ InternalHom₀ (id (C op) , f) ∘C (j₀ a)}
                       → {j-extranatural-a₁ : {a a' : Obj C} (f : Hom C a a') → (F₁ InternalHom₁ (f , id C)) ∘C (j₁ a') ≡ F₁ InternalHom₁ (id (C op) , f) ∘C (j₁ a)}
                       → {L-natural-c₀ : (a : Obj C) → (b : Obj (C op)) → {c c' : Obj C} {f : Hom C c c'}
                                       → F₁ InternalHom₀ (F₁ InternalHom₀ (id C {a} , id C {b}) , F₁ InternalHom₀ (id C {a} , f)) ∘C L₀ a b c ≡ L₀ a b c' ∘C F₁ InternalHom₀ (id C {b} , f)}
                       → {L-natural-c₁ : (a : Obj C) → (b : Obj (C op)) → {c c' : Obj C} {f : Hom C c c'}
                                       → F₁ InternalHom₁ (F₁ InternalHom₁ (id C {a} , id C {b}) , F₁ InternalHom₁ (id C {a} , f)) ∘C L₁ a b c ≡ L₁ a b c' ∘C F₁ InternalHom₁ (id C {b} , f)}
                       → {L-natural-b₀ : (a c : Obj C) → {b b' : Obj C} {f : Hom C b b'}
                                       → F₁ InternalHom₀ (F₁ InternalHom₀ (id C {a} , f) , F₁ InternalHom₀ (id C {a} , id C {c})) ∘C L₀ a b' c ≡ L₀ a b c ∘C F₁ InternalHom₀ (f , id C {c})}
                       → {L-natural-b₁ : (a c : Obj C) → {b b' : Obj C} {f : Hom C b b'}
                                       → F₁ InternalHom₁ (F₁ InternalHom₁ (id C {a} , f) , F₁ InternalHom₁ (id C {a} , id C {c})) ∘C L₁ a b' c ≡ L₁ a b c ∘C F₁ InternalHom₁ (f , id C {c})}
                       → {L-extranatural-a₀ : (b : Obj (C op)) → (c : Obj C) → {a a' : Obj C} (f : Hom C a a') 
                                            → F₁ InternalHom₀ (id C , F₁ InternalHom₀ (f , id C {c})) ∘C L₀ a' b c ≡ F₁ InternalHom₀ (F₁ InternalHom₀ (f , id (C op) {b}) , id C) ∘C L₀ a b c}
                       → {L-extranatural-a₁ : (b : Obj (C op)) → (c : Obj C) → {a a' : Obj C} (f : Hom C a a') 
                                            → F₁ InternalHom₁ (id C , F₁ InternalHom₁ (f , id C {c})) ∘C L₁ a' b c ≡ F₁ InternalHom₁ (F₁ InternalHom₁ (f , id (C op) {b}) , id C) ∘C L₁ a b c}
                       → InternalHom₀ ≡ InternalHom₁ → I₀ ≡ I₁ → i₀ ≅ i₁ → j₀ ≅ j₁ → L₀ ≅ L₁
                       → closedCategory InternalHom₀ I₀ i₀ j₀ L₀ j-extranatural-a₀ L-natural-c₀ L-natural-b₀ L-extranatural-a₀
                       ≡ closedCategory InternalHom₁ I₁ i₁ j₁ L₁ j-extranatural-a₁ L-natural-c₁ L-natural-b₁ L-extranatural-a₁
    closed-category-eq {InternalHom₀ = InternalHom} {._} {I} {._} {i} {._} {j} {._} {L} {._} 
                       {j-extranatural-a₀} {j-extranatural-a₁} {L-natural-c₀} {L-natural-c₁} {L-natural-b₀} {L-natural-b₁} {L-extranatural-a₀} {L-extranatural-a₁}
                       refl refl refl refl refl 
      = cong₄ (closedCategory InternalHom I i j L) 
              (implicit-fun-ext $ λ a → implicit-fun-ext $ λ a' → fun-ext $ λ f → proof-irrelevance (j-extranatural-a₀ {a} {a'} f) (j-extranatural-a₁ {a} {a'} f)) 
              (fun-ext $ λ a → fun-ext $ λ b → implicit-fun-ext $ λ c → implicit-fun-ext $ λ c' → implicit-fun-ext $ λ f → proof-irrelevance (L-natural-c₀ a b {c} {c'} {f}) (L-natural-c₁ a b {c} {c'} {f}))
              (fun-ext $ λ a → fun-ext $ λ c → implicit-fun-ext $ λ b → implicit-fun-ext $ λ b' → implicit-fun-ext $ λ f → proof-irrelevance (L-natural-b₀ a c {b} {b'} {f}) (L-natural-b₁ a c {b} {b'} {f}))
              (fun-ext $ λ b → fun-ext $ λ c → implicit-fun-ext $ λ a → implicit-fun-ext $ λ a' → fun-ext $ λ f → proof-irrelevance (L-extranatural-a₀ b c {a} {a'} f) (L-extranatural-a₁ b c {a} {a'} f))

open Equality public

