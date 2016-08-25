
module Theory.AtkeyParameterizedMonad where

-- Stdlib
open import Level renaming ( suc to lsuc ; zero to lzero )
open import Function renaming ( id to idF ; _∘_ to _∘F_ )
open import Data.Product renaming ( _,_ to _,'_ ; _×_ to _×'_ )
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning 

open import Theory.Triple
open import Theory.Category
open import Theory.Functor
open import Theory.NaturalTransformation
open import Theory.DinaturalTransformation

open Category hiding (assoc ; idL ; idR )

-------------------------------------------------------------------------------
-- Helper functors to model the dinatural transformations of a parameterized monad
-------------------------------------------------------------------------------

diNatAtkeyFunctorConst : {ℓS₀ ℓS₁ ℓD₀ ℓD₁ : Level} 
                       → (D : Category {ℓD₀} {ℓD₁})
                       → (S : Category {ℓS₀} {ℓS₁})
                       → Obj D
                       → Functor (S op ×C S) D
diNatAtkeyFunctorConst D S x = record
  { F₀ = F₀
  ; F₁ = F₁ 
  ; id = refl
  ; dist = sym $ Category.idL D
  } where
    F₀ : Obj (S op ×C S) → Obj D
    F₀ (s ,' s') = x
    
    F₁ : {a b : Obj (S op ×C S)} 
       → Hom (S op ×C S) a b → Hom D (F₀ a) (F₀ b)
    F₁ (sf ,' sf') = id D {x}


diNatAtkeyFunctorConst' : {ℓS₀ ℓS₁ ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} 
                       → {C : Category {ℓC₀} {ℓC₁}}
                       → {D : Category {ℓD₀} {ℓD₁}}
                       → {S : Category {ℓS₀} {ℓS₁}}
                       → Obj (S op) → Obj S → Obj C
                       → Functor (S op ×C S ×C C) D
                       → Functor (S op ×C S) D
diNatAtkeyFunctorConst' {C = C} {D} {S} s₁ s₃ x F = record
  { F₀ = F₀
  ; F₁ = F₁ 
  ; id = Functor.id F
  ; dist = λ {a} {b} {c} {f} {g} → dist {a} {b} {c} {f} {g}
  } where
    _∘D_ = _∘_ D ; _∘C_ = _∘_ C ; _∘SS_ = _∘_ (S op ×C S) ; _∘S_ = _∘_ S ; _∘Sop_ = _∘_ (S op)
    
    F₀ : Obj (S op ×C S) → Obj D
    F₀ (s ,' s') = [ F ]₀ (s₁ , s₃ , x)
    
    F₁ : {a b : Obj (S op ×C S)} 
       → Hom (S op ×C S) a b → Hom D (F₀ a) (F₀ b)
    F₁ (sf ,' sf') = [ F ]₁ (id (S op) {s₁} , id S {s₃} , id C {x})
    
    dist : {a b c : Obj ((S op) ×C S)} 
         → {f : Hom ((S op) ×C S) a b} {g : Hom ((S op) ×C S) b c}
         → F₁ (g ∘SS f) ≡ F₁ g ∘D F₁ f
    dist {f = sf ,' sf'} {g = sg ,' sg'} = begin
      F₁ ((sg ,' sg') ∘SS (sf ,' sf')) 
        ≡⟨ refl ⟩
      [ F ]₁ (id (S op) {s₁} , id S {s₃} , id C {x})
        ≡⟨ Functor.id F ⟩
      id D
        ≡⟨ sym $ Category.idL D ⟩
      id D ∘D id D
        ≡⟨ cong₂ _∘D_ (sym $ Functor.id F) (sym $ Functor.id F) ⟩
      [ F ]₁ (id (S op) {s₁} , id S {s₃} , id C {x}) ∘D [ F ]₁ (id (S op) {s₁} , id S {s₃} , id C {x})
        ≡⟨ refl ⟩
      F₁ (sg ,' sg') ∘D F₁ (sf ,' sf') ∎

diNatAtkeyFunctor : {ℓS₀ ℓS₁ ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} 
                  → {S : Category {ℓS₀} {ℓS₁}} {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}}
                  → Obj C
                  → Functor (S op ×C S ×C C) D 
                  → Functor (S op ×C S) D
diNatAtkeyFunctor {S = S} {C} {D} x F = record
  { F₀ = F₀
  ; F₁ = F₁  
  ; id = Functor.id F
  ; dist = dist
  } where
    F₀ : Obj ((S op) ×C S) → Obj D
    F₀ (s ,' s') = [ F ]₀ (s , s' , x)

    F₁ : {a b : Obj (S op ×C S)} → Hom (S op ×C S) a b → Hom D (F₀ a) (F₀ b)
    F₁ (sf ,' sf') = [ F ]₁ (sf , sf' , id C {x})
    
    _∘SS_ = _∘_ (S op ×C S)
    _∘S_ = _∘_ S
    _∘Sop_ = _∘_ (S op)
    _∘D_ = _∘_ D
    _∘C_ = _∘_ C
    
    dist : {a b c : Obj ((S op) ×C S)}
         → {f : Hom (S op ×C S) a b} {g : Hom (S op ×C S) b c} 
         → F₁ (g ∘SS f) ≡ (F₁ g) ∘D (F₁ f)
    dist {f = f ,' f'} {g = g ,' g'} = begin
      F₁ ((g ,' g') ∘SS (f ,' f')) 
        ≡⟨ refl ⟩
      [ F ]₁ ((g ∘Sop f) , (g' ∘S f') , id C {x}) 
        ≡⟨ cong (λ X → [ F ]₁ ((g ∘Sop f) , (g' ∘S f') , X)) (sym $ Category.idL C) ⟩
      [ F ]₁ ((g ∘Sop f) , (g' ∘S f') , (id C {x} ∘C id C {x})) 
        ≡⟨ Functor.dist F ⟩
      [ F ]₁ (g , g' , id C {x}) ∘D [ F ]₁ (f , f' , id C {x})
        ≡⟨ refl ⟩
      (F₁ (g ,' g')) ∘D (F₁ (f ,' f')) ∎

diNatAtkeyFunctorComp : {ℓS₀ ℓS₁ ℓC₀ ℓC₁ : Level} 
                  → {S : Category {ℓS₀} {ℓS₁}} {C : Category {ℓC₀} {ℓC₁}}
                  → Obj (S op) → Obj S → Obj C
                  → Functor (S op ×C S ×C C) C 
                  → Functor (S op ×C S ×C C) C 
                  → Functor (S op ×C S) C
diNatAtkeyFunctorComp {S = S} {C} s₁ s₃ x F G = record
  { F₀ = F₀
  ; F₁ = F₁  
  ; id = idFunc
  ; dist = dist
  } where
    _∘SS_ = _∘_ (S op ×C S) ; _∘C_ = _∘_ C
    _∘S_ = _∘_ S ; _∘Sop_ = _∘_ (S op)

    F₀ : Obj ((S op) ×C S) → Obj C
    F₀ (s₂ ,' s₂') = [ G ]₀ (s₁ , s₂' , [ F ]₀ (s₂ , s₃ , x))

    F₁ : {a b : Obj (S op ×C S)} → Hom (S op ×C S) a b → Hom C (F₀ a) (F₀ b)
    F₁ (s₂f ,' s₂f') = [ G ]₁ (id (S op) {s₁} , s₂f' , [ F ]₁ (s₂f , id S {s₃} , id C {x}))
    
    idFunc : {a : Obj (S op ×C S)} → F₁ (id (S op ×C S) {a})  ≡ id C
    idFunc {s₂ ,' s₂'} = begin
      F₁ (id (S op ×C S) {s₂ ,' s₂'}) 
        ≡⟨ refl ⟩
      [ G ]₁ (id (S op) {s₁} , id S {s₂'} , [ F ]₁ (id (S op) {s₂} , id S {s₃} , id C {x}))
        ≡⟨ cong (λ X → [ G ]₁ (id (S op) {s₁} , id S {s₂'} , X)) (Functor.id F) ⟩
      [ G ]₁ (id (S op) {s₁} , id S {s₂'} , id C)
        ≡⟨ Functor.id G ⟩
      id C ∎

    dist : {a b c : Obj ((S op) ×C S)} 
         → {f : Hom ((S op) ×C S) a b} {g : Hom ((S op) ×C S) b c}
         → F₁ (g ∘SS f) ≡ F₁ g ∘C F₁ f
    dist {f = sf ,' sf'} {g = sg ,' sg'} = begin
      F₁ ((sg ,' sg') ∘SS (sf ,' sf')) 
        ≡⟨ refl ⟩
      [ G ]₁ (id (S op) {s₁} , (sg' ∘S sf') , [ F ]₁ ((sg ∘Sop sf) , id S {s₃} , id C {x}))
        ≡⟨ cong₂ (λ X Y → [ G ]₁ (id (S op) {s₁} , (sg' ∘S sf') , [ F ]₁ ((sg ∘Sop sf) , X , Y))) (sym $ Category.idL S) (sym $ Category.idL C) ⟩
      [ G ]₁ (id (S op) {s₁} , (sg' ∘S sf') , [ F ]₁ ((sg ∘Sop sf) , (id S {s₃} ∘S id S {s₃}) , (id C {x} ∘C id C {x})))
        ≡⟨ cong (λ X → [ G ]₁ (id (S op) {s₁} , (sg' ∘S sf') , X)) (Functor.dist F) ⟩
      [ G ]₁ (id (S op) {s₁} , (sg' ∘S sf') , ([ F ]₁ (sg , id S {s₃} , id C {x}) ∘C [ F ]₁ (sf , id S {s₃} , id C {x})) )
        ≡⟨ cong (λ X → [ G ]₁ (X , (sg' ∘S sf') , ([ F ]₁ (sg , id S {s₃} , id C {x}) ∘C [ F ]₁ (sf , id S {s₃} , id C {x})) )) (sym $ Category.idL (S op)) ⟩
      [ G ]₁ ((id (S op) {s₁} ∘Sop id (S op) {s₁}) , (sg' ∘S sf') , ([ F ]₁ (sg , id S {s₃} , id C {x}) ∘C [ F ]₁ (sf , id S {s₃} , id C {x})) )
        ≡⟨ Functor.dist G ⟩
      ([ G ]₁ (id (S op) {s₁} , sg' , [ F ]₁ (sg , id S {s₃} , id C {x}))) ∘C ([ G ]₁ (id (S op) {s₁} , sf' , [ F ]₁ (sf , id S {s₃} , id C {x})))
        ≡⟨ refl ⟩
      F₁ (sg ,' sg') ∘C F₁ (sf ,' sf') ∎

-------------------------------------------------------------------------------
-- Helper functors to model the natural transformations of a parameterized monad
-------------------------------------------------------------------------------

natTransAtkeyFunctor : {ℓS₀ ℓS₁ ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} 
                     → {S : Category {ℓS₀} {ℓS₁}} {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}}
                     → Obj (S op) → Obj S
                     → Functor (S op ×C S ×C C) D 
                     → Functor C D
natTransAtkeyFunctor {S = S} {C} {D} s s' F = record 
  { F₀ = F₀
  ; F₁ = F₁  
  ; id = Functor.id F
  ; dist = dist
  } where
    _∘C_ = _∘_ C ; _∘D_ = _∘_ D ; _∘S_ = _∘_ S
    
    F₀ : Obj C → Obj D
    F₀ x = [ F ]₀ (s , s' , x)

    F₁ : {a b : Obj C} → Hom C a b → Hom D (F₀ a) (F₀ b)
    F₁ f = [ F ]₁ (id S {s} , id S {s'} , f)
    
    dist : {a b c : Obj C} 
         → {f : Hom C a b} {g : Hom C b c}
         → F₁ (g ∘C f) ≡ (F₁ g) ∘D (F₁ f)
    dist {a} {b} {c} {f} {g} = begin
      -- F₁ (g ∘C f)
      [ F ]₁ (id S {s} , id S {s'} , (g ∘C f))
        ≡⟨ cong₂ (λ X Y → [ F ]₁ (X , Y , (g ∘C f))) (sym $ Category.idL S) (sym $ Category.idL S) ⟩
      [ F ]₁ ((id S {s} ∘S id S {s}) , (id S {s'} ∘S id S {s'}) , (g ∘C f))
        ≡⟨ Functor.dist F ⟩
      [ F ]₁ (id S {s} , id S {s'} , g) ∘D [ F ]₁ (id S {s} , id S {s'} , f) ∎

natTransAtkeyFunctorFst : {ℓS₀ ℓS₁ ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} 
                        → {S : Category {ℓS₀} {ℓS₁}} {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}}
                        → Obj S → Obj C
                        → Functor (S op ×C S ×C C) D 
                        → Functor (S op) D
natTransAtkeyFunctorFst {S = S} {C} {D} s' x F = record 
  { F₀ = F₀
  ; F₁ = F₁  
  ; id = Functor.id F
  ; dist = dist
  } where
    _∘C_ = _∘_ C ; _∘D_ = _∘_ D ; _∘S_ = _∘_ S ; _∘Sop_ = _∘_ (S op)
    
    F₀ : Obj (S op) → Obj D
    F₀ s = [ F ]₀ (s , s' , x)

    F₁ : {a b : Obj (S op)} → Hom (S op) a b → Hom D (F₀ a) (F₀ b)
    F₁ sf = [ F ]₁ (sf , id S {s'} , id C {x})
    
    dist : {a b c : Obj (S op)} 
         → {sf : Hom (S op) a b} {sg : Hom (S op) b c}
         → F₁ (sg ∘Sop sf) ≡ (F₁ sg) ∘D (F₁ sf)
    dist {a} {b} {c} {sf} {sg} = begin
      [ F ]₁ ((sg ∘Sop sf) , id S {s'} , id C {x})
        ≡⟨ cong₂ (λ X Y → [ F ]₁ ((sg ∘Sop sf) , X , Y)) (sym $ Category.idL S) (sym $ Category.idL C) ⟩
      [ F ]₁ ((sg ∘Sop sf) , (id S {s'} ∘S id S {s'}) , (id C {x} ∘C id C {x}))
        ≡⟨ Functor.dist F ⟩
      [ F ]₁ (sg , id S {s'} , id C {x}) ∘D [ F ]₁ (sf , id S {s'} , id C {x}) ∎


natTransAtkeyFunctorSnd : {ℓS₀ ℓS₁ ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} 
                        → {S : Category {ℓS₀} {ℓS₁}} {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}}
                        → Obj (S op) → Obj C
                        → Functor (S op ×C S ×C C) D 
                        → Functor S D
natTransAtkeyFunctorSnd {S = S} {C} {D} s x F = record 
  { F₀ = F₀
  ; F₁ = F₁  
  ; id = Functor.id F
  ; dist = dist
  } where
    _∘C_ = _∘_ C ; _∘D_ = _∘_ D ; _∘S_ = _∘_ S ; _∘Sop_ = _∘_ (S op)
    
    F₀ : Obj S → Obj D
    F₀ s' = [ F ]₀ (s , s' , x)

    F₁ : {a b : Obj S} → Hom S a b → Hom D (F₀ a) (F₀ b)
    F₁ sf' = [ F ]₁ (id (S op) {s} , sf' , id C {x})
    
    dist : {a b c : Obj S} 
         → {sf' : Hom S a b} {sg' : Hom S b c}
         → F₁ (sg' ∘S sf') ≡ (F₁ sg') ∘D (F₁ sf')
    dist {a} {b} {c} {sf'} {sg'} = begin
      [ F ]₁ (id (S op) {s} , (sg' ∘S sf') , id C {x})
        ≡⟨ cong₂ (λ X Y → [ F ]₁ (X , (sg' ∘S sf') , Y)) (sym $ Category.idL (S op)) (sym $ Category.idL C) ⟩
      [ F ]₁ ((id (S op) {s} ∘Sop id (S op) {s}) , (sg' ∘S sf') , (id C {x} ∘C id C {x}))
        ≡⟨ Functor.dist F ⟩
      [ F ]₁ (id (S op) {s} , sg' , id C {x}) ∘D [ F ]₁ (id (S op) {s} , sf' , id C {x}) ∎

natTransAtkeyFunctorComp : {ℓS₀ ℓS₁ ℓC₀ ℓC₁ : Level} 
                         → {S : Category {ℓS₀} {ℓS₁}} {C : Category {ℓC₀} {ℓC₁}}
                         → Obj S
                         → Functor (S op ×C S ×C C) C
                         → Functor (S op ×C S ×C C) C
                         → Functor (S op ×C S ×C C) C
natTransAtkeyFunctorComp {S = S} {C} s₂ F G = record 
  { F₀ = F₀
  ; F₁ = F₁  
  ; id = idFunc
  ; dist = dist
  } where
    _∘C_ = _∘_ C ; _∘S_ = _∘_ S ; _∘Sop_ = _∘_ (S op)
    _∘SSC_ = _∘_ (S op ×C S ×C C)
    
    F₀ : Obj (S op ×C S ×C C) → Obj C
    F₀ (s₁ , s₃ , x) = [ G ]₀ (s₁ , s₂ , [ F ]₀ (s₂ , s₃ , x))

    F₁ : {a b : Obj (S op ×C S ×C C)} → Hom (S op ×C S ×C C) a b → Hom C (F₀ a) (F₀ b)
    F₁ (s₁ , s₃ , f) = [ G ]₁ (s₁ , id S {s₂} , [ F ]₁ (id S {s₂} , s₃ , f))
    
    idFunc : {a : Obj ((S op) ×C S ×C C)}
           → F₁ (id ((S op) ×C S ×C C) {a}) ≡ id C
    idFunc {s₁ , s₃ , x} = begin
      F₁ (id ((S op) ×C S ×C C) {s₁ , s₃ , x})
        ≡⟨ refl ⟩
      [ G ]₁ (id (S op) {s₁} , id S {s₂} , [ F ]₁ (id S {s₂} , id S {s₃} , id C {x}))
        ≡⟨ cong (λ X → [ G ]₁ (id (S op) {s₁} , id S {s₂} , X)) (Functor.id F) ⟩
      [ G ]₁ (id (S op) {s₁} , id S {s₂} , id C)
        ≡⟨ Functor.id G ⟩
      id C ∎
    
    dist : {a b c : Obj ((S op) ×C S ×C C)}
         → {f : Hom ((S op) ×C S ×C C) a b} {g : Hom ((S op) ×C S ×C C) b c}
         → F₁ (g ∘SSC f) ≡ F₁ g ∘C F₁ f
    dist {f = sf , sf' , f} {g = sg , sg' , g} = begin
      F₁ ((sg , sg' , g) ∘SSC (sf , sf' , f)) 
        ≡⟨ refl ⟩
      [ G ]₁ ((sg ∘Sop sf) , id S {s₂} , [ F ]₁ (id (S op) {s₂} , (sg' ∘S sf') , (g ∘C f)))
        ≡⟨ cong (λ X → [ G ]₁ ((sg ∘Sop sf) , id S {s₂} , [ F ]₁ (X , (sg' ∘S sf') , (g ∘C f)))) (sym $ Category.idL (S op)) ⟩
      [ G ]₁ ((sg ∘Sop sf) , id S {s₂} , [ F ]₁ ((id (S op) {s₂} ∘Sop id (S op) {s₂})  , (sg' ∘S sf') , (g ∘C f)))
        ≡⟨ cong (λ X → [ G ]₁ ((sg ∘Sop sf) , id S {s₂} , X)) (Functor.dist F) ⟩
      [ G ]₁ ((sg ∘Sop sf) , id S {s₂} , ([ F ]₁ (id (S op) {s₂} , sg' , g) ∘C [ F ]₁ (id (S op) {s₂}  , sf' , f)))
        ≡⟨ cong (λ X → [ G ]₁ ((sg ∘Sop sf) , X , ([ F ]₁ (id (S op) {s₂} , sg' , g) ∘C [ F ]₁ (id (S op) {s₂}  , sf' , f)))) (sym $ Category.idL S) ⟩
      [ G ]₁ ((sg ∘Sop sf) , (id S {s₂} ∘S id S {s₂}) , ([ F ]₁ (id (S op) {s₂} , sg' , g) ∘C [ F ]₁ (id (S op) {s₂}  , sf' , f)))
        ≡⟨ Functor.dist G ⟩
      [ G ]₁ (sg , id S {s₂} , [ F ]₁ (id (S op) {s₂} , sg' , g)) ∘C [ G ]₁ (sf , id S {s₂} , [ F ]₁ (id (S op) {s₂}  , sf' , f)) 
        ≡⟨ refl ⟩
      F₁ (sg , sg' , g) ∘C F₁ (sf , sf' , f) ∎

-------------------------------------------------------------------------------
-- Definition of parameterized monads as given by Atkey
-------------------------------------------------------------------------------

-- The definition and names choosen closly follow the definition given in 
-- Atkeys paper "Parameterized notions of computation" (page 339).
-- This is definition does not contain a strength conditions.
record AtkeyParameterizedMonad {ℓC₀ ℓC₁ ℓS₀ ℓS₁ : Level} (C : Category {ℓC₀} {ℓC₁}) (S : Category {ℓS₀} {ℓS₁}) (T : Functor (S op ×C S ×C C) C) : Set (ℓC₀ ⊔ ℓC₁ ⊔ ℓS₀ ⊔ ℓS₁) where
  private
    _∘C_ = _∘_ C
  field
    η : {a : Obj C} {s : Obj S} → Hom C a ([ T ]₀ (s , s , a))
    
    μ : {a : Obj C} {s₁ s₂ s₃ : Obj S} → Hom C ([ T ]₀ (s₁ , s₂ , ([ T ]₀ (s₂ , s₃ , a)))) ([ T ]₀ (s₁ , s₃ , a))
    

    naturalη : {s : Obj S}
             → {a b : Obj C} {f : Hom C a b} 
             → [ T ]₁ (id (S op) {s} , id S {s} , f) ∘C η {a} {s}
             ≡ η {b} {s} ∘C f
    
    dinaturalη : {x : Obj C} 
               → {a b : Obj S} {f : Hom S a b} 
               → [ T ]₁ (id S {a} , f , id C {x}) ∘C η {x} {a}
               ≡ [ T ]₁ (f , id S {b} , id C {x}) ∘C η {x} {b}

    naturalμ : {s₁ s₂ s₃ : Obj S}
             → {a b : Obj C} → {f : Hom C a b} 
             → [ T ]₁ (id (S op) {s₁} , id S {s₃} , f) ∘C μ {a} {s₁} {s₂} {s₃}
             ≡ μ {b} {s₁} {s₂} {s₃} ∘C [ T ]₁ (id (S op) {s₁} , id S {s₂} , ([ T ]₁ (id (S op) {s₂} , id S {s₃} , f))) 
    
    naturalμ₁ : {s₂ s₃ : Obj S} {x : Obj C} 
              → {a b : Obj (S op)} {f : Hom (S op) a b} 
              → [ T ]₁ (f , id S {s₃} , id C {x}) ∘C μ {x} {a} {s₂} {s₃}
              ≡ μ {x} {b} {s₂} {s₃} ∘C [ T ]₁ (f , id S {s₂} , [ T ]₁ (id S {s₂} ,  id S {s₃} , id C {x}))

    naturalμ₂ : {s₁ s₂ : Obj S} {x : Obj C} 
              → {a b : Obj S} {f : Hom S a b}
              → [ T ]₁ (id (S op) {s₁} , f , id C {x}) ∘C μ {x} {s₁} {s₂} {a}
              ≡ μ {x} {s₁} {s₂} {b} ∘C [ T ]₁ (id (S op) {s₁} , id S {s₂} , [ T ]₁ (id S {s₂} , f , id C {x}))

    dinaturalμ : {s₁ s₃ : Obj S} {x : Obj C}
               → {a b : Obj S} {f : Hom S a b}
               → μ {x} {s₁} {a} {s₃} ∘C [ T ]₁ (id (S op) {s₁} , id S {a} , [ T ]₁ (f , id S {s₃} , id C {x}))
               ≡ μ {x} {s₁} {b} {s₃} ∘C [ T ]₁ (id (S op) {s₁} , f , [ T ]₁ (id S {b} , id S {s₃} , id C {x}))
    
    assoc : ∀ {x : Obj C} {a b c d : Obj S} {s₁ : Hom S d d} {s₂ : Hom S a a}
           → μ {x} {d} {a} {c} ∘C [ T ]₁ (s₁ , s₂ , μ {x} {a} {b} {c}) 
           ≡ μ {x} {d} {b} {c} ∘C μ {[ T ]₀ (b , c , x)} {d} {a} {b}

    idL : {x : Obj C} {a b : Obj S}
        → μ {x} {a} {a} {b} ∘C η {[ T ]₀ (a , b , x)} {a} ≡ id C
    
    idR : {x : Obj C} {a b : Obj S} {s₁ : Hom S a a} {s₂ : Hom S b b}
        → [ T ]₁ (s₁ , s₂ , η {x} {b}) ∘C μ {x} {a} {b} {b} ≡ id C
  
  NatTrans-η : (s : Obj S) → NaturalTransformation Id[ C ] (natTransAtkeyFunctor s s T)
  NatTrans-η s = naturalTransformation (λ x → η {x} {s}) (naturalη {s})
  
  DiNatTrans-η : (x : Obj C) → DinaturalTransformation (diNatAtkeyFunctorConst C S x) (diNatAtkeyFunctor x T)
  DiNatTrans-η x = dinaturalTransformation (λ s → η {x} {s}) $ λ {a b : Obj S} {f : Hom S a b} → begin
    [ T ]₁ (id S {a} , f , id C {x}) ∘C (η {x} {a} ∘C id C {x})
      ≡⟨ cong (λ X → [ T ]₁ (id S {a} , f , id C {x}) ∘C X) (Category.idL C) ⟩
    [ T ]₁ (id S {a} , f , id C {x}) ∘C η {x} {a}
      ≡⟨ dinaturalη {x} ⟩
    [ T ]₁ (f , id S {b} , id C {x}) ∘C η {x} {b}
      ≡⟨ cong (λ X → [ T ]₁ (f , id S {b} , id C {x}) ∘C X) (sym $ Category.idL C) ⟩
    [ T ]₁ (f , id S {b} , id C {x}) ∘C (η {x} {b} ∘C id C {x}) ∎

  NatTrans-μ : (s₁ s₂ s₃ : Obj S) → NaturalTransformation [ natTransAtkeyFunctor s₁ s₂ T ]∘[ natTransAtkeyFunctor s₂ s₃ T ] (natTransAtkeyFunctor s₁ s₃ T)
  NatTrans-μ s₁ s₂ s₃ = naturalTransformation (λ x → μ {x} {s₁} {s₂} {s₃}) (naturalμ {s₁} {s₂} {s₃})

  NatTrans-μ₁ : (s₂ s₃ : Obj S) (x : Obj C) → NaturalTransformation (natTransAtkeyFunctorFst s₃ x (natTransAtkeyFunctorComp s₂ T T)) (natTransAtkeyFunctorFst s₃ x T)
  NatTrans-μ₁ s₂ s₃ x = naturalTransformation (λ s₁ → μ {x} {s₁} {s₂} {s₃}) (naturalμ₁ {s₂} {s₃} {x})

  NatTrans-μ₂ : (s₁ s₂ : Obj S) (x : Obj C) → NaturalTransformation (natTransAtkeyFunctorSnd s₁ x (natTransAtkeyFunctorComp s₂ T T)) (natTransAtkeyFunctorSnd s₁ x T)
  NatTrans-μ₂ s₁ s₂ x = naturalTransformation (λ s₃ → μ {x} {s₁} {s₂} {s₃}) (naturalμ₂ {s₁} {s₂} {x})
  
  DiNatTrans-μ : (s₁ s₃ : Obj S) (x : Obj C) → DinaturalTransformation (diNatAtkeyFunctorComp s₁ s₃ x T T) (diNatAtkeyFunctorConst' s₁ s₃ x T)
  DiNatTrans-μ s₁ s₃ x = dinaturalTransformation (λ s₂ → μ {x} {s₁} {s₂} {s₃}) $ λ {a b : Obj S} {f : Hom S a b} → begin
    [ T ]₁ (id (S op) {s₁} , id S {s₃} , id C {x}) ∘C (μ {x} {s₁} {a} {s₃} ∘C [ T ]₁ (id (S op) {s₁} , id S {a} , [ T ]₁ (f , id S {s₃} , id C {x})))
      ≡⟨ cong (λ X → X ∘C (μ {x} {s₁} {a} {s₃} ∘C [ T ]₁ (id (S op) {s₁} , id S {a} , [ T ]₁ (f , id S {s₃} , id C {x})))) (Functor.id T) ⟩ 
    id C ∘C (μ {x} {s₁} {a} {s₃} ∘C [ T ]₁ (id (S op) {s₁} , id S {a} , [ T ]₁ (f , id S {s₃} , id C {x})))
      ≡⟨ Category.idR C ⟩ 
    μ {x} {s₁} {a} {s₃} ∘C [ T ]₁ (id (S op) {s₁} , id S {a} , [ T ]₁ (f , id S {s₃} , id C {x}))
      ≡⟨ dinaturalμ {s₁} {s₃} {x} ⟩ 
    μ {x} {s₁} {b} {s₃} ∘C [ T ]₁ (id (S op) {s₁} , f , [ T ]₁ (id S {b} , id S {s₃} , id C {x}))
      ≡⟨ sym $ Category.idR C ⟩ 
    id C ∘C (μ {x} {s₁} {b} {s₃} ∘C [ T ]₁ (id (S op) {s₁} , f , [ T ]₁ (id S {b} , id S {s₃} , id C {x})))
      ≡⟨ cong (λ X → X ∘C (μ {x} {s₁} {b} {s₃} ∘C [ T ]₁ (id (S op) {s₁} , f , [ T ]₁ (id S {b} , id S {s₃} , id C {x})))) (sym $ Functor.id T) ⟩ 
    [ T ]₁ (id (S op) {s₁} , id S {s₃} , id C {x}) ∘C (μ {x} {s₁} {b} {s₃} ∘C [ T ]₁ (id (S op) {s₁} , f , [ T ]₁ (id S {b} , id S {s₃} , id C {x}))) ∎ --(dinaturalμ {s₁} {s₃} {x})
