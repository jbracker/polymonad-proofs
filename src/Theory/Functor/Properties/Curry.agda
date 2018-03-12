

-- Stdlib
open import Level renaming ( suc to lsuc ; zero to lzero )
open import Function hiding ( _∘_ ; id )

open import Data.Product

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning hiding ( _≅⟨_⟩_ )
open import Relation.Binary.HeterogeneousEquality renaming ( refl to hrefl ; sym to hsym ; trans to htrans ; cong to hcong ; cong₂ to hcong₂ )
open ≅-Reasoning renaming ( begin_ to hbegin_ ; _∎ to _∎h ) hiding ( _≡⟨_⟩_ )

-- Local
open import Extensionality
open import Bijection renaming ( refl to brefl ; sym to bsym ; trans to btrans )
open import Theory.Category.Definition
open import Theory.Category.Examples.Functor renaming ( functorCategory to Fun )
open import Theory.Functor.Definition
open import Theory.Natural.Transformation

module Theory.Functor.Properties.Curry
  {ℓC₀ ℓC₁ ℓD₀ ℓD₁ ℓE₀ ℓE₁ : Level} 
  {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}} {E : Category {ℓE₀} {ℓE₁}} where

open Category

private
  _∘C_ = _∘_ C
  _∘D_ = _∘_ D
  _∘E_ = _∘_ E
  _∘C×D_ = _∘_ (C ×C D)
  _∘Fun_ = _∘_ (Fun D E)

curryFunctor : Functor (C ×C D) E → Functor C (Fun D E)
curryFunctor (functor F₀ F₁ F-id F-compose) = functor G₀ G₁ G-id (λ {a b c} {f} {g} → G-compose {a} {b} {c} {f} {g})
  where
    G₀ : Obj C → Obj (Fun D E)
    G₀ c = functor G₀₀ G₀₁ F-id G₀-compose
      where
        G₀₀ : Obj D → Obj E
        G₀₀ d = F₀ (c , d)
        
        G₀₁ : {a b : Obj D} → Hom D a b → Hom E (G₀₀ a) (G₀₀ b)
        G₀₁ {a} {b} f = F₁ (id C {c} , f)
        
        abstract
          G₀-compose : {a b c : Obj D} {f : Hom D a b} {g : Hom D b c} → G₀₁ (g ∘D f) ≡ (G₀₁ g) ∘E (G₀₁ f)
          G₀-compose {x} {y} {z} {f} {g} = begin
            G₀₁ (g ∘D f) 
              ≡⟨ refl ⟩
            F₁ (id C {c} , g ∘D f) 
              ≡⟨ cong (λ X → F₁ (X , g ∘D f)) (sym $ left-id C) ⟩
            F₁ (id C {c} ∘C id C {c} , g ∘D f) 
              ≡⟨ F-compose ⟩
            F₁ (id C {c} , g) ∘E F₁ (id C {c} , f)
              ≡⟨ refl ⟩
            G₀₁ g ∘E G₀₁ f ∎
  
    G₁ : {a b : Obj C} → Hom C a b → Hom (Fun D E) (G₀ a) (G₀ b)
    G₁ {a} {b} f = naturalTransformation G₁-η G₁-natural
      where
        G₁-η : (x : Obj D) → Hom E ([ G₀ a ]₀ x) ([ G₀ b ]₀ x)
        G₁-η x = F₁ (f , id D {x})
        
        abstract
          G₁-natural : {x y : Obj D} {g : Hom D x y} 
                     → [ G₀ b ]₁ g ∘E G₁-η x ≡ G₁-η y ∘E [ G₀ a ]₁ g
          G₁-natural {x} {y} {g} = begin
            [ G₀ b ]₁ g ∘E G₁-η x 
              ≡⟨ refl ⟩
            F₁ (id C {b} , g) ∘E F₁ (f , id D {x})
              ≡⟨ sym $ F-compose ⟩
            F₁ (id C {b} ∘C f , g ∘D id D {x})
              ≡⟨ cong₂ (λ X Y → F₁ (X , Y)) (right-id C) (left-id D) ⟩
            F₁ (f , g)
              ≡⟨ cong₂ (λ X Y → F₁ (X , Y)) (sym $ left-id C) (sym $ right-id D) ⟩
            F₁ (f ∘C id C {a}, id D {y} ∘D g)
              ≡⟨ F-compose ⟩
            F₁ (f , id D {y}) ∘E F₁ (id C {a} , g)
              ≡⟨ refl ⟩
            G₁-η y ∘E [ G₀ a ]₁ g ∎
    
    abstract
      G-id : {a : Obj C} → G₁ {a} {a} (id C) ≡ id (Fun D E)
      G-id {a} = natural-transformation-eq $ fun-ext $ λ x → F-id {a , x}
    
    open NaturalTransformation renaming ( η to nat-η )
    
    abstract
      G-compose : {a b c : Obj C} {f : Hom C a b} {g : Hom C b c} 
                → G₁ (g ∘C f) ≡ G₁ g ∘Fun G₁ f
      G-compose {a} {b} {c} {f} {g} = natural-transformation-eq $ fun-ext $ λ x → begin
        nat-η (G₁ (g ∘C f)) x 
          ≡⟨ refl ⟩
        F₁ (g ∘C f , id D {x})
          ≡⟨ cong (λ X → F₁ (g ∘C f , X)) (sym $ left-id D) ⟩
        F₁ (g ∘C f , id D {x} ∘D id D {x})
          ≡⟨ F-compose ⟩
        F₁ (g , id D {x}) ∘E F₁ (f , id D {x})
          ≡⟨ refl ⟩
        nat-η (G₁ g) x ∘E nat-η (G₁ f) x ∎

uncurryFunctor : Functor C (Fun D E) → Functor (C ×C D) E
uncurryFunctor (functor F₀ F₁ F-id F-compose) = functor G₀ G₁ G-id G-compose
  where
    open NaturalTransformation renaming ( η to nat-η )
    
    G₀ : Obj (C ×C D) → Obj E
    G₀ (c , d) = [ F₀ c ]₀ d
    
    G₁ : {a b : Obj (C ×C D)} → Hom (C ×C D) a b → Hom E (G₀ a) (G₀ b)
    G₁ {c , d} {c' , d'} (f , g) = [ F₀ c' ]₁ g ∘E nat-η (F₁ {c} {c'} f) d
    
    abstract
      G-id : {a : Obj (C ×C D)} → G₁ {a} {a} (id (C ×C D)) ≡ id E
      G-id {c , d} = begin
        G₁ (id (C ×C D)) 
          ≡⟨ refl ⟩
        [ F₀ c ]₁ (id D {d}) ∘E nat-η (F₁ {c} {c} (id C {c})) d
          ≡⟨ cong (λ X → [ F₀ c ]₁ (id D {d}) ∘E nat-η X d) F-id ⟩
        [ F₀ c ]₁ (id D {d}) ∘E nat-η (id (Fun D E) {F₀ c}) d
          ≡⟨ refl ⟩
        [ F₀ c ]₁ (id D {d}) ∘E id E {[ F₀ c ]₀ d}
          ≡⟨ left-id E ⟩
        [ F₀ c ]₁ (id D {d})
          ≡⟨ Functor.id (F₀ c) ⟩
        id E ∎
    
    abstract
      G-compose : {a b c : Obj (C ×C D)} {f : Hom (C ×C D) a b} {g : Hom (C ×C D) b c}
                → G₁ (g ∘C×D f) ≡ G₁ g ∘E G₁ f
      G-compose {c , d} {c' , d'} {c'' , d''} {f , g} {f' , g'} = begin
        G₁ ((f' , g') ∘C×D (f , g)) 
          ≡⟨ refl ⟩
        [ F₀ c'' ]₁ (g' ∘D g) ∘E nat-η (F₁ {c} {c''} (f' ∘C f)) d
          ≡⟨ cong₂ _∘E_ (Functor.compose (F₀ c'')) (cong (λ X → nat-η X d) F-compose) ⟩
        ([ F₀ c'' ]₁ g' ∘E [ F₀ c'' ]₁ g) ∘E (nat-η (F₁ {c'} {c''} f') d ∘E nat-η (F₁ {c} {c'} f) d)
          ≡⟨ sym $ assoc E ⟩
        [ F₀ c'' ]₁ g' ∘E ([ F₀ c'' ]₁ g ∘E (nat-η (F₁ {c'} {c''} f') d ∘E nat-η (F₁ {c} {c'} f) d))
          ≡⟨ cong (λ X → [ F₀ c'' ]₁ g' ∘E X) (assoc E) ⟩
        [ F₀ c'' ]₁ g' ∘E (([ F₀ c'' ]₁ g ∘E nat-η (F₁ {c'} {c''} f') d) ∘E nat-η (F₁ {c} {c'} f) d)
          ≡⟨ cong (λ X → [ F₀ c'' ]₁ g' ∘E (X ∘E nat-η (F₁ {c} {c'} f) d)) (natural $ F₁ {c'} {c''} f') ⟩
        [ F₀ c'' ]₁ g' ∘E ((nat-η (F₁ {c'} {c''} f') d' ∘E [ F₀ c' ]₁ g) ∘E nat-η (F₁ {c} {c'} f) d)
          ≡⟨ cong (λ X → [ F₀ c'' ]₁ g' ∘E X) (sym $ assoc E) ⟩
        [ F₀ c'' ]₁ g' ∘E (nat-η (F₁ {c'} {c''} f') d' ∘E ([ F₀ c' ]₁ g ∘E nat-η (F₁ {c} {c'} f) d))
          ≡⟨ assoc E ⟩
        ([ F₀ c'' ]₁ g' ∘E nat-η (F₁ {c'} {c''} f') d') ∘E ([ F₀ c' ]₁ g ∘E nat-η (F₁ {c} {c'} f) d)
          ≡⟨ refl ⟩
        G₁ (f' , g') ∘E G₁ (f , g) ∎


curry-uncurry-bij : Functor (C ×C D) E ↔ Functor C (Fun D E)
curry-uncurry-bij = bijection curryFunctor uncurryFunctor uncurry-curry curry-uncurry
  where
    open NaturalTransformation renaming ( η to nat-η )
    
    abstract
      uncurry-curry : (F : Functor C (Fun D E)) → curryFunctor (uncurryFunctor F) ≡ F
      uncurry-curry F = functor-eq F₀-eq $ het-implicit-fun-ext (hcong (λ X → (λ z → {b : Obj C} → Hom C z b → NaturalTransformation (X z) (X b))) (≡-to-≅ F₀-eq)) 
                      $ λ (c : Obj C) → het-implicit-fun-ext (hcong (λ X → (λ z → Hom C c z → NaturalTransformation (X c) (X z))) (≡-to-≅ F₀-eq)) 
                      $ λ (c' : Obj C) → het-fun-ext (hcong (λ X → (λ (f : Hom C c c') → NaturalTransformation (X c) (X c'))) (≡-to-≅ F₀-eq)) 
                      $ λ (f : Hom C c c') → het-natural-transformation-eq (cong (λ X → X c) F₀-eq) (cong (λ X → X c') F₀-eq) $ het-fun-ext hrefl 
                      $ λ (d : Obj D) → F-nat-eq c c' f d
        where
          abstract
            F-nat-eq : (c c' : Obj C) → (f : Hom C c c') → (d : Obj D) 
                     → nat-η (Functor.F₁ (curryFunctor (uncurryFunctor F)) f) d ≅ nat-η (Functor.F₁ F f) d
            F-nat-eq c c' f d = hbegin
              nat-η (Functor.F₁ (curryFunctor (uncurryFunctor F)) f) d 
                ≅⟨ hrefl ⟩
              [ Functor.F₀ F c' ]₁ (id D {d}) ∘E nat-η (Functor.F₁ F {c} {c'} f) d
                ≅⟨ hcong (λ X → X ∘E nat-η (Functor.F₁ F {c} {c'} f) d) (≡-to-≅ (Functor.id (Functor.F₀ F c'))) ⟩
              id E ∘E nat-η (Functor.F₁ F {c} {c'} f) d
                ≅⟨ ≡-to-≅ (right-id E) ⟩
              nat-η (Functor.F₁ F f) d ∎h
          
          abstract
            F₀₁-eq : (c : Obj C) → (d d' : Obj D) → (f : Hom D d d') 
                   → Functor.F₁ (Functor.F₀ (curryFunctor (uncurryFunctor F)) c) f ≡ Functor.F₁ (Functor.F₀ F c) f
            F₀₁-eq c d d' f = begin
              Functor.F₁ (Functor.F₀ (curryFunctor (uncurryFunctor F)) c) f
                ≡⟨ refl ⟩
              [ Functor.F₀ F c ]₁ f ∘E nat-η (Functor.F₁ F (id C {c})) d
                ≡⟨ cong (λ X → [ Functor.F₀ F c ]₁ f ∘E nat-η X d) (Functor.id F) ⟩
              [ Functor.F₀ F c ]₁ f ∘E nat-η (id (Fun D E) {Functor.F₀ F c}) d
                ≡⟨ refl ⟩
              [ Functor.F₀ F c ]₁ f ∘E id E
                ≡⟨ left-id E ⟩
              Functor.F₁ (Functor.F₀ F c) f ∎
          
          abstract
            F₀-eq : Functor.F₀ (curryFunctor (uncurryFunctor F)) ≡ Functor.F₀ F
            F₀-eq = fun-ext 
                  $ λ (c : Obj C) → functor-eq refl $ het-implicit-fun-ext hrefl 
                  $ λ (d : Obj D) → het-implicit-fun-ext hrefl 
                  $ λ (d' : Obj D) → het-fun-ext hrefl 
                  $ λ (f : Hom D d d') → ≡-to-≅ $ F₀₁-eq c d d' f
    
    abstract
      curry-uncurry : (F : Functor (C ×C D) E) → uncurryFunctor (curryFunctor F) ≡ F
      curry-uncurry F = functor-eq refl $ ≡-to-≅ $ implicit-fun-ext 
                      $ λ (cd : Obj (C ×C D)) → implicit-fun-ext 
                      $ λ (cd' : Obj (C ×C D)) → fun-ext 
                      $ λ (fg : Hom (C ×C D) cd cd') → F₁-eq cd cd' fg
        where
          F₁-eq : (cd cd' : Obj (C ×C D)) → (fg : Hom (C ×C D) cd cd') 
                → Functor.F₁ (uncurryFunctor (curryFunctor F)) fg ≡ Functor.F₁ F fg
          F₁-eq (c , d) (c' , d') (f , g) = begin
            Functor.F₁ (uncurryFunctor (curryFunctor F)) (f , g) 
              ≡⟨ refl ⟩
            Functor.F₁ F (id C {c'} , g) ∘E Functor.F₁ F (f , id D {d})
              ≡⟨ sym $ Functor.compose F ⟩
            Functor.F₁ F (id C {c'} ∘C f , g ∘D id D {d})
              ≡⟨ cong₂ (λ X Y → Functor.F₁ F (X , Y)) (right-id C) (left-id D) ⟩
            Functor.F₁ F (f , g) ∎

