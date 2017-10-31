
open import Level
open import Function hiding ( id ) renaming ( _∘_ to _∘F_ )
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( proof-irrelevance to het-proof-irrelevance )

open import Extensionality
open import Congruence

open import Theory.Category.Definition
open import Theory.Functor.Definition

open import Theory.Haskell.Parameterized.Relative.Monad

module Theory.Haskell.Parameterized.Relative.Monad.Equality 
  {ℓC₀ ℓC₁ ℓD₀ ℓD₁ ℓI₀ ℓI₁ : Level} 
  {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}} {I : Category {ℓI₀} {ℓI₁}}  where 

open Category renaming ( id to cat-id )

private
  _∘I_ = _∘_ I
  _∘C_ = _∘_ C
  _∘D_ = _∘_ D

abstract
  parameterized-relative-monad-eq 
    : {T : {i j : Obj I} → Hom I i j → Obj C → Obj D}
    → {J : Functor C D}
    → {η₀ : (i : Obj I) → {a : Obj C} → Hom D ([ J ]₀ a) (T (cat-id I {i}) a)}
    → {η₁ : (i : Obj I) → {a : Obj C} → Hom D ([ J ]₀ a) (T (cat-id I {i}) a)}
    → {kext₀ : {i j k : Obj I} → (f : Hom I i j) (g : Hom I j k) 
             → {a b : Obj C} → Hom D ([ J ]₀ a) (T g b) → Hom D (T f a) (T (g ∘I f) b)}
    → {kext₁ : {i j k : Obj I} → (f : Hom I i j) (g : Hom I j k) 
             → {a b : Obj C} → Hom D ([ J ]₀ a) (T g b) → Hom D (T f a) (T (g ∘I f) b)}
    → {right-id₀ : {i j : Obj I} → (f : Hom I i j) 
                 → {a b : Obj C} {k : Hom D ([ J ]₀ a) (T f b)} 
                 → kext₀ (cat-id I) f k ∘D η₀ i ≅ k}
    → {right-id₁ : {i j : Obj I} → (f : Hom I i j) 
                 → {a b : Obj C} {k : Hom D ([ J ]₀ a) (T f b)} 
                 → kext₁ (cat-id I) f k ∘D η₁ i ≅ k}
    → {left-id₀ : {i j : Obj I} → (f : Hom I i j) 
                → {a : Obj C}
                → kext₀ f (cat-id I) (η₀ j {a}) ≅ cat-id D {a = T f a}}
    → {left-id₁ : {i j : Obj I} → (f : Hom I i j) 
                → {a : Obj C}
                → kext₁ f (cat-id I) (η₁ j {a}) ≅ cat-id D {a = T f a}}
    → {coher₀ : {i j v w : Obj I} → (f : Hom I i j) → (g : Hom I j v) → (h : Hom I v w) 
              → {a b c : Obj C} {k : Hom D ([ J ]₀ a) (T g b)} {l : Hom D ([ J ]₀ b) (T h c)} 
              → kext₀ f (h ∘I g) ( (kext₀ g h l) ∘D k ) ≅ kext₀ (g ∘I f) h l ∘D kext₀ f g k}
    → {coher₁ : {i j v w : Obj I} → (f : Hom I i j) → (g : Hom I j v) → (h : Hom I v w) 
              → {a b c : Obj C} {k : Hom D ([ J ]₀ a) (T g b)} {l : Hom D ([ J ]₀ b) (T h c)} 
              → kext₁ f (h ∘I g) ( (kext₁ g h l) ∘D k ) ≅ kext₁ (g ∘I f) h l ∘D kext₁ f g k}
    → (η₀ ≡ η₁)
    → ((λ {i j k} → kext₀ {i} {j} {k}) ≡ kext₁)
    → parameterizedRelativeMonad {C = C} {D} {I} {T} {J} η₀ kext₀ right-id₀ left-id₀ coher₀ 
    ≡ parameterizedRelativeMonad {C = C} {D} {I} {T} {J} η₁ kext₁ right-id₁ left-id₁ coher₁
  parameterized-relative-monad-eq {T} {J} {η} {.η} {kext} {.kext} {rid₀} {rid₁} {lid₀} {lid₁} {coher₀} {coher₁} refl refl 
    = cong₃ (parameterizedRelativeMonad {C = C} {D} {I} {T} {J} η kext) eq1 eq2 eq3
    where
      abstract
        eq1 : (λ {i j} fI {a b} {f} → rid₀ {i} {j} fI {a} {b} {f}) ≡ rid₁
        eq1 = implicit-fun-ext 
            $ λ i → implicit-fun-ext 
            $ λ j → fun-ext 
            $ λ fI → implicit-fun-ext 
            $ λ a → implicit-fun-ext 
            $ λ b → implicit-fun-ext 
            $ λ f → het-proof-irrelevance (rid₀ fI) (rid₁ fI)
      
      abstract
        eq2 : (λ {i j} fI {a} → lid₀ {i} {j} fI {a}) ≡ lid₁
        eq2 = implicit-fun-ext 
            $ λ i → implicit-fun-ext 
            $ λ j → fun-ext 
            $ λ fI → implicit-fun-ext 
            $ λ a → het-proof-irrelevance (lid₀ fI) (lid₁ fI)
      
      abstract
        eq3 : (λ {i j v w} fI gI hI {a b c} {k} {l} → coher₀ {i} {j} {v} {w} fI gI hI {a} {b} {c} {k} {l}) ≡ coher₁
        eq3 = implicit-fun-ext 
            $ λ i → implicit-fun-ext 
            $ λ j → implicit-fun-ext 
            $ λ v → implicit-fun-ext 
            $ λ w → fun-ext 
            $ λ fI → fun-ext 
            $ λ gI → fun-ext 
            $ λ hI → implicit-fun-ext 
            $ λ a → implicit-fun-ext 
            $ λ b → implicit-fun-ext 
            $ λ c → implicit-fun-ext 
            $ λ k → implicit-fun-ext 
            $ λ l → het-proof-irrelevance (coher₀ fI gI hI) (coher₁ fI gI hI)
        
