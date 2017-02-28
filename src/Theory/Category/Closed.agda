
open import Level renaming ( zero to lzero ; suc to lsuc )
open import Function using ( _$_ )

open import Data.Unit
open import Data.Product renaming ( _,_ to _,'_ )

open import Relation.Binary.PropositionalEquality

open import Theory.Category hiding ( category )
open import Theory.Functor
import Theory.Functor.Application
import Theory.Functor.Composition
open import Theory.Natural.Isomorphism
open import Theory.Natural.Transformation
open import Theory.Natural.DinaturalTransformation
open import Theory.Natural.ExtranaturalTransformation

module Theory.Category.Closed where

invert : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}}
       → Functor C D → Functor (C op) (D op)
invert (functor F₀ F₁ id compose) = functor F₀ F₁ id compose

invert' : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}}
        → Functor (C op) (D op) → Functor C D
invert' (functor F₀ F₁ id compose) = functor F₀ F₁ id compose


leftId : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}}
       → Functor (⊤-Cat ×C C) D → Functor C D
leftId (functor F₀ F₁ id compose)
  = functor (λ x → F₀ (tt ,' x)) (λ f → F₁ (tt ,' f)) id compose

rightId : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}}
        → Functor (C ×C ⊤-Cat) D → Functor C D
rightId (functor F₀ F₁ id compose)
  = functor (λ x → F₀ (x ,' tt)) (λ f → F₁ (f ,' tt)) id compose

constToAny : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} (C : Category {ℓC₀} {ℓC₁}) {D : Category {ℓD₀} {ℓD₁}}
           → Functor ⊤-Cat D → Functor C D
constToAny C (functor F₀ F₁ id compose) = functor (λ _ → F₀ tt) (λ _ → F₁ tt) id compose


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

    j-extranatural-a : {a a' : Obj C} (f : Hom C a a') 
                   → [ f , id C ]₁ ∘C (j a') ≡ [ id (C op) , f ]₁ ∘C (j a)
    
    L : (a b c : Obj C) → Hom C [ b , c ]₀ [ [ a , b ]₀ , [ a , c ]₀ ]₀
    
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
                             (leftId ([ invert ([ a , b ] InternalHom) , [ a ,-] InternalHom ]∘[ InternalHom ]))
  L-natural-transformation a b = naturalTransformation (λ x → L a b x) (L-natural-c a b)

  -- [-,c] → [[a,-],[a,c]] is a natural transformation
  L-natural-transformation-op : (a : Obj (C op)) → (c : Obj C)
                              → NaturalTransformation
                                ([-, c ] InternalHom)
                                (rightId [ invert ([ a ,-] InternalHom) , [ a , c ] InternalHom ]∘[ InternalHom ])
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
