
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

diNatFunctor : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} 
             → {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}}
             → Functor C D 
             → Functor (C op ×C C) D
diNatFunctor {C = C} {D} F = record
  { F₀ = F₀
  ; F₁ = F₁ 
  ; id = Functor.id F
  ; dist = Functor.dist F
  } where
    F₀ : Obj (C op ×C C) → Obj D
    F₀ (c' ,' c) = [ F ]₀ c
    
    F₁ : {a b : Obj ((C op) ×C C)} → Hom ((C op) ×C C) a b → Hom D (F₀ a) (F₀ b)
    F₁ (f' ,' f) = [ F ]₁ f

DiNat[_] = diNatFunctor

IdDiNat[_] : {ℓC₀ ℓC₁ : Level} → (C : Category {ℓC₀} {ℓC₁}) → Functor (C op ×C C) C
IdDiNat[_] C = DiNat[ Id[ C ] ]

diNatAtkeyConstFunctor : {ℓS₀ ℓS₁ ℓD₀ ℓD₁ : Level} 
                       → (D : Category {ℓD₀} {ℓD₁})
                       → (S : Category {ℓS₀} {ℓS₁})
                       → Obj D
                       → Functor (S op ×C S) D
diNatAtkeyConstFunctor D S x = record
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
    F₀ c = [ F ]₀ (s , s' , c)

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

-- This is not the strong definition presented in Atkeys paper.
record AtkeyParameterizedMonad {ℓC₀ ℓC₁ ℓS₀ ℓS₁ : Level} (C : Category {ℓC₀} {ℓC₁}) (S : Category {ℓS₀} {ℓS₁}) (T : Functor (S op ×C S ×C C) C) : Set (ℓC₀ ⊔ ℓC₁ ⊔ ℓS₀ ⊔ ℓS₁) where
  private
    _∘C_ = _∘_ C
  field
    η : {a : Obj C} {s : Obj S} → Hom C a ([ T ]₀ (s , s , a))
    
    μ : {a : Obj C} {s₁ s₂ s₃ : Obj S} → Hom C ([ T ]₀ (s₁ , s₂ , ([ T ]₀ (s₂ , s₃ , a)))) ([ T ]₀ (s₁ , s₃ , a))
    

    naturalη : {a b : Obj C} {f : Hom C a b} {x : Obj S} {s₁ : Hom S x x} {s₂ : Hom S x x}
             → ([ T ]₁ (s₁ , s₂ , f)) ∘C (η {a} {x}) ≡ (η {b} {x}) ∘C ([ Id[ C ] ]₁ f)
    
    dinaturalη : {c : Obj C} {s s' : Obj S} {f : Hom S s s'}
               → [ T ]₁ (id S {s} , f , id C {c}) ∘C (η {c} {s} ∘C [ Id[ C ] ]₁ (id C {c})) ≡ [ T ]₁ (f , id S {s'} , id C {c}) ∘C (η {c} {s'} ∘C [ Id[ C ] ]₁ (id C {c}))

    naturalμ : {s t u : Obj S} {s₁ : Hom S s s} {s₂ : Hom S t t} {s₃ : Hom S u u} {a b : Obj C} 
             → {f : Hom C a b} 
             → [ T ]₁ (s₁ , s₃ , f) ∘C μ {a} {s} {t} {u}
             ≡ μ {b} {s} {t} {u} ∘C [ T ]₁ (s₁ , s₂ , ([ T ]₁ (s₂ , s₃ , f))) 

    
    assoc : ∀ {x : Obj C} {a b c d : Obj S} {s₁ : Hom S d d} {s₂ : Hom S a a}
           → μ {x} {d} {a} {c} ∘C [ T ]₁ (s₁ , s₂ , μ {x} {a} {b} {c}) ≡ μ {x} {d} {b} {c} ∘C μ {[ T ]₀ (b , c , x)} {d} {a} {b}

    idL : {x : Obj C} {a b : Obj S}
        → μ {x} {a} {a} {b} ∘C η {[ T ]₀ (a , b , x)} {a} ≡ id C
    
    idR : {x : Obj C} {a b : Obj S} {s₁ : Hom S a a} {s₂ : Hom S b b}
        → [ T ]₁ (s₁ , s₂ , η {x} {b}) ∘C μ {x} {a} {b} {b} ≡ id C
  
  NatTrans-η : (s : Obj S) → NaturalTransformation Id[ C ] (natTransAtkeyFunctor s s T)
  NatTrans-η s = naturalTransformation (λ x → η {x} {s}) naturalη
  
  DiNatTrans-η : (x : Obj C) → DinaturalTransformation (diNatAtkeyConstFunctor C S x) (diNatAtkeyFunctor x T)
  DiNatTrans-η x = dinaturalTransformation (λ s → η {x} {s}) dinaturalη

  NatTrans-μ : (s₁ s₂ s₃ : Obj S) → NaturalTransformation [ natTransAtkeyFunctor s₁ s₂ T ]∘[ natTransAtkeyFunctor s₂ s₃ T ] (natTransAtkeyFunctor s₁ s₃ T)
  NatTrans-μ s₁ s₂ s₃ = naturalTransformation (λ x → μ {x} {s₁} {s₂} {s₃}) naturalμ
  
