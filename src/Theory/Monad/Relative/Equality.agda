
open import Level
open import Function hiding ( id ) renaming ( _∘_ to _∘F_ )
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning 

open import Congruence
open import Extensionality

open import Theory.Category.Definition
open import Theory.Functor.Definition

open import Theory.Monad.Relative

open Category hiding ( right-id ; left-id )

module Theory.Monad.Relative.Equality
  {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} 
  {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}}  where

private
  _∘D_ = _∘_ D
  _∘C_ = _∘_ C

abstract
  relative-monad-eq 
    : {T : Obj C → Obj D} 
    → {J : Functor C D}
    → {η₀ : {a : Obj C} → Hom D ([ J ]₀ a) (T a)}
    → {η₁ : {a : Obj C} → Hom D ([ J ]₀ a) (T a)}
    → {kext₀ : {a b : Obj C} → Hom D ([ J ]₀ a) (T b) → Hom D (T a) (T b)}
    → {kext₁ : {a b : Obj C} → Hom D ([ J ]₀ a) (T b) → Hom D (T a) (T b)}
    → {rid₀ : {a b : Obj C} {k : Hom D ([ J ]₀ a) (T b)} → kext₀ k ∘D η₀ ≡ k}
    → {rid₁ : {a b : Obj C} {k : Hom D ([ J ]₀ a) (T b)} → kext₁ k ∘D η₁ ≡ k}
    → {lid₀ : {a : Obj C} → kext₀ η₀ ≡ id D {a = T a}}
    → {lid₁ : {a : Obj C} → kext₁ η₁ ≡ id D {a = T a}}
    → {coher₀ : {a b c : Obj C} {k : Hom D ([ J ]₀ a) (T b)} {l : Hom D ([ J ]₀ b) (T c)} → kext₀ ( (kext₀ l) ∘D k ) ≡ kext₀ l ∘D kext₀ k}
    → {coher₁ : {a b c : Obj C} {k : Hom D ([ J ]₀ a) (T b)} {l : Hom D ([ J ]₀ b) (T c)} → kext₁ ( (kext₁ l) ∘D k ) ≡ kext₁ l ∘D kext₁ k}
    → ((λ {a} → η₀ {a}) ≡ η₁)
    → ((λ {a b} → kext₀ {a} {b}) ≡ kext₁)
    → relative-monad {T = T} {J} η₀ kext₀ rid₀ lid₀ coher₀ ≡ relative-monad {T = T} {J} η₁ kext₁ rid₁ lid₁ coher₁
  relative-monad-eq {T} {J} {η} {.η} {kext} {.kext} {rid₀} {rid₁} {lid₀} {lid₁} {coher₀} {coher₁} refl refl = 
    cong₃ (relative-monad {T = T} {J} η kext) eq1 eq2 eq3
    where
      eq1 : (λ {a b} {k} → rid₀ {a} {b} {k}) ≡ rid₁
      eq1 = implicit-fun-ext 
          $ λ a → implicit-fun-ext 
          $ λ b → implicit-fun-ext 
          $ λ k → proof-irrelevance rid₀ rid₁
      
      eq2 : (λ {a} → lid₀ {a}) ≡ lid₁
      eq2 = implicit-fun-ext 
          $ λ a → proof-irrelevance lid₀ lid₁
      
      eq3 : (λ {a b c} {k} {l} → coher₀ {a} {b} {c} {k} {l}) ≡ coher₁
      eq3 = implicit-fun-ext 
          $ λ a → implicit-fun-ext 
          $ λ b → implicit-fun-ext 
          $ λ c → implicit-fun-ext 
          $ λ k → implicit-fun-ext 
          $ λ l → proof-irrelevance coher₀ coher₁
