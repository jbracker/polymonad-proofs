 
module Substitution where

open import Level
open import Relation.Binary.HeterogeneousEquality renaming ( refl to hrefl ; trans to htrans ; cong to hcong ; subst to hsubst ; subst₂ to hsubst₂ ; sym to hsym ) -- ≅
open import Relation.Binary.PropositionalEquality using ( refl ; _≡_ ; subst ; subst₂ )

abstract
  subst₂-removable : ∀ {a b p} {A : Set a} {B : Set b} (P : A → B → Set p) 
                   → ∀ {x₁ x₂ y₁ y₂}
                   → (eqx : x₁ ≡ x₂ ) → (eqy : y₁ ≡ y₂) 
                   → (z : P x₁ y₁)
                   → subst₂ P eqx eqy z ≅ z
  subst₂-removable P refl refl z = hrefl


-- Substitution with three arguments.
subst₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} 
         (P : A → B → C → Set d) {x₁ x₂ y₁ y₂ z₁ z₂} 
       → x₁ ≡ x₂ → y₁ ≡ y₂ → z₁ ≡ z₂ → P x₁ y₁ z₁ → P x₂ y₂ z₂
subst₃ P refl refl refl p = p

-- Substitution with three arguments.
het-subst₃-dep : {a b c d : Level}
               → {A : Set a} {B : A → Set b} {C : (a : A) → B a → Set c} 
               → (P : (a : A) → (b : B a) → C a b → Set d)
               → {x₁ x₂ : A} {y₁ : B x₁} {y₂ : B x₂} {z₁ : C x₁ y₁} {z₂ : C x₂ y₂} 
               → x₁ ≡ x₂ → y₁ ≅ y₂ → z₁ ≅ z₂
               → P x₁ y₁ z₁ → P x₂ y₂ z₂
het-subst₃-dep P refl hrefl hrefl p = p

-- Substitution with four arguments.
subst₄ : ∀ {a b c d p} {A : Set a} {B : Set b} {C : Set c} {D : Set d} 
       → (P : A → B → C → D → Set p)
       → ∀ {x₁ x₂ y₁ y₂ z₁ z₂ w₁ w₂} 
       → x₁ ≡ x₂ → y₁ ≡ y₂ → z₁ ≡ z₂ → w₁ ≡ w₂ 
       → P x₁ y₁ z₁ w₁ → P x₂ y₂ z₂ w₂
subst₄ P refl refl refl refl p = p

-- Properly dependently typed substitution for two arguments.
subst₂dep : ∀ {a b c} 
          → {A : Set a} {B : A → Set b}
          → (P : (a : A) → B a → Set c) 
          → {x1 y1 : A} → (eq1 : x1 ≡ y1)
          → {x2 : B x1} → {y2 : B y1} → subst B eq1 x2 ≡ y2
          → P x1 x2 → P y1 y2
subst₂dep P refl refl p = p

-- Properly dependently typed substitution for three arguments.
subst₃dep : ∀ {a b c d} 
          → {A : Set a} {B : A → Set b} {C : (a : A) → B a → Set c}
          → (P : (a : A) → (b : B a) → C a b → Set d) 
          → {x1 y1 : A} → (eq1 : x1 ≡ y1)
          → {x2 : B x1} → {y2 : B y1} → (eq2 : subst B eq1 x2 ≡ y2)
          → {x3 : C x1 x2} → {y3 : C y1 y2} → (eq3 : subst₂dep C eq1 eq2 x3 ≡ y3)
          → P x1 x2 x3 → P y1 y2 y3
subst₃dep P refl refl refl p = p

-- Properly dependently typed substitution for four arguments.
subst₄dep : ∀ {a b c d e} 
          → {A : Set a} {B : A → Set b} {C : (a : A) → B a → Set c} 
            {D : (a : A) → (b : B a) → C a b → Set d}
          → (P : (a : A) → (b : B a) → (c : C a b) → D a b c → Set e) 
          → {x1 y1 : A} → (eq1 : x1 ≡ y1)
          → {x2 : B x1} → {y2 : B y1} → (eq2 : subst B eq1 x2 ≡ y2)
          → {x3 : C x1 x2} → {y3 : C y1 y2} → (eq3 : subst₂dep C eq1 eq2 x3 ≡ y3)
          → {x4 : D x1 x2 x3} → {y4 : D y1 y2 y3} → (eq4 : subst₃dep D eq1 eq2 eq3 x4 ≡ y4)
          → P x1 x2 x3 x4 → P y1 y2 y3 y4
subst₄dep P refl refl refl refl p = p

-- Properly dependently typed substitution for five arguments.
subst₅dep : ∀ {a b c d e f} 
          → {A : Set a} {B : A → Set b} {C : (a : A) → B a → Set c} 
            {D : (a : A) → (b : B a) → C a b → Set d} 
            {E : (a : A) → (b : B a) → (c : C a b) → D a b c → Set e}
          → (P : (a : A) → (b : B a) → (c : C a b) → (d : D a b c) → E a b c d → Set f) 
          → {x1 y1 : A} → (eq1 : x1 ≡ y1)
          → {x2 : B x1} → {y2 : B y1} → (eq2 : subst B eq1 x2 ≡ y2)
          → {x3 : C x1 x2} → {y3 : C y1 y2} → (eq3 : subst₂dep C eq1 eq2 x3 ≡ y3)
          → {x4 : D x1 x2 x3} → {y4 : D y1 y2 y3} → (eq4 : subst₃dep D eq1 eq2 eq3 x4 ≡ y4)
          → {x5 : E x1 x2 x3 x4} → {y5 : E y1 y2 y3 y4} → (eq5 : subst₄dep E eq1 eq2 eq3 eq4 x5 ≡ y5)
          → P x1 x2 x3 x4 x5 → P y1 y2 y3 y4 y5
subst₅dep P refl refl refl refl refl p = p

-- Properly dependently typed substitution for six arguments.
subst₆dep : ∀ {a b c d e f g} 
          → {A : Set a} {B : A → Set b} {C : (a : A) → B a → Set c} 
            {D : (a : A) → (b : B a) → C a b → Set d} 
            {E : (a : A) → (b : B a) → (c : C a b) → D a b c → Set e}
            {F : (a : A) → (b : B a) → (c : C a b) → (d : D a b c) → E a b c d → Set f}
          → (P : (a : A) → (b : B a) → (c : C a b) → (d : D a b c) → (e : E a b c d) → F a b c d e → Set g) 
          → {x1 y1 : A} → (eq1 : x1 ≡ y1)
          → {x2 : B x1} → {y2 : B y1} → (eq2 : subst B eq1 x2 ≡ y2)
          → {x3 : C x1 x2} → {y3 : C y1 y2} → (eq3 : subst₂dep C eq1 eq2 x3 ≡ y3)
          → {x4 : D x1 x2 x3} → {y4 : D y1 y2 y3} → (eq4 : subst₃dep D eq1 eq2 eq3 x4 ≡ y4)
          → {x5 : E x1 x2 x3 x4} → {y5 : E y1 y2 y3 y4} → (eq5 : subst₄dep E eq1 eq2 eq3 eq4 x5 ≡ y5)
          → {x6 : F x1 x2 x3 x4 x5} → {y6 : F y1 y2 y3 y4 y5} → (eq6 : subst₅dep F eq1 eq2 eq3 eq4 eq5 x6 ≡ y6)
          → P x1 x2 x3 x4 x5 x6 → P y1 y2 y3 y4 y5 y6
subst₆dep P refl refl refl refl refl refl p = p

-- Properly dependently typed substitution for seven arguments.
subst₇dep : ∀ {a b c d e f g h} 
          → {A : Set a} {B : A → Set b} {C : (a : A) → B a → Set c} 
            {D : (a : A) → (b : B a) → C a b → Set d} 
            {E : (a : A) → (b : B a) → (c : C a b) → D a b c → Set e}
            {F : (a : A) → (b : B a) → (c : C a b) → (d : D a b c) → E a b c d → Set f} 
            {G : (a : A) → (b : B a) → (c : C a b) → (d : D a b c) → (e : E a b c d) → F a b c d e → Set g}
          → (P : (a : A) → (b : B a) → (c : C a b) → (d : D a b c) → (e : E a b c d) → (f : F a b c d e) → G a b c d e f → Set h) 
          → {x1 : A}                   → {y1 : A}                   → (eq1 : x1 ≡ y1)
          → {x2 : B x1}                → {y2 : B y1}                → (eq2 : subst B eq1 x2 ≡ y2)
          → {x3 : C x1 x2}             → {y3 : C y1 y2}             → (eq3 : subst₂dep C eq1 eq2 x3 ≡ y3)
          → {x4 : D x1 x2 x3}          → {y4 : D y1 y2 y3}          → (eq4 : subst₃dep D eq1 eq2 eq3 x4 ≡ y4)
          → {x5 : E x1 x2 x3 x4}       → {y5 : E y1 y2 y3 y4}       → (eq5 : subst₄dep E eq1 eq2 eq3 eq4 x5 ≡ y5)
          → {x6 : F x1 x2 x3 x4 x5}    → {y6 : F y1 y2 y3 y4 y5}    → (eq6 : subst₅dep F eq1 eq2 eq3 eq4 eq5 x6 ≡ y6)
          → {x7 : G x1 x2 x3 x4 x5 x6} → {y7 : G y1 y2 y3 y4 y5 y6} → (eq7 : subst₆dep G eq1 eq2 eq3 eq4 eq5 eq6 x7 ≡ y7)
          → P x1 x2 x3 x4 x5 x6 x7 → P y1 y2 y3 y4 y5 y6 y7
subst₇dep P refl refl refl refl refl refl refl p = p

-- Properly dependently typed substitution for eight arguments.
subst₈dep : ∀ {a b c d e f g h i} 
          → {A : Set a} {B : A → Set b} {C : (a : A) → B a → Set c} 
            {D : (a : A) → (b : B a) → C a b → Set d} 
            {E : (a : A) → (b : B a) → (c : C a b) → D a b c → Set e}
            {F : (a : A) → (b : B a) → (c : C a b) → (d : D a b c) → E a b c d → Set f} 
            {G : (a : A) → (b : B a) → (c : C a b) → (d : D a b c) → (e : E a b c d) → F a b c d e → Set g}
            {H : (a : A) → (b : B a) → (c : C a b) → (d : D a b c) → (e : E a b c d) → (f : F a b c d e) → G a b c d e f → Set h}
          → (P : (a : A) → (b : B a) → (c : C a b) → (d : D a b c) → (e : E a b c d) → (f : F a b c d e) → (g : G a b c d e f) → H a b c d e f g → Set i) 
          → {x1 : A}                      → {y1 : A}                      → (eq1 : x1 ≡ y1)
          → {x2 : B x1}                   → {y2 : B y1}                   → (eq2 : subst B eq1 x2 ≡ y2)
          → {x3 : C x1 x2}                → {y3 : C y1 y2}                → (eq3 : subst₂dep C eq1 eq2 x3 ≡ y3)
          → {x4 : D x1 x2 x3}             → {y4 : D y1 y2 y3}             → (eq4 : subst₃dep D eq1 eq2 eq3 x4 ≡ y4)
          → {x5 : E x1 x2 x3 x4}          → {y5 : E y1 y2 y3 y4}          → (eq5 : subst₄dep E eq1 eq2 eq3 eq4 x5 ≡ y5)
          → {x6 : F x1 x2 x3 x4 x5}       → {y6 : F y1 y2 y3 y4 y5}       → (eq6 : subst₅dep F eq1 eq2 eq3 eq4 eq5 x6 ≡ y6)
          → {x7 : G x1 x2 x3 x4 x5 x6}    → {y7 : G y1 y2 y3 y4 y5 y6}    → (eq7 : subst₆dep G eq1 eq2 eq3 eq4 eq5 eq6 x7 ≡ y7)
          → {x8 : H x1 x2 x3 x4 x5 x6 x7} → {y8 : H y1 y2 y3 y4 y5 y6 y7} → (eq8 : subst₇dep H eq1 eq2 eq3 eq4 eq5 eq6 eq7 x8 ≡ y8)
          → P x1 x2 x3 x4 x5 x6 x7 x8 → P y1 y2 y3 y4 y5 y6 y7 y8
subst₈dep P refl refl refl refl refl refl refl refl p = p

-- Properly dependently typed substitution for eight arguments.
subst₉dep : ∀ {a b c d e f g h i j} 
          → {A : Set a} {B : A → Set b} {C : (a : A) → B a → Set c} 
            {D : (a : A) → (b : B a) → C a b → Set d} 
            {E : (a : A) → (b : B a) → (c : C a b) → D a b c → Set e}
            {F : (a : A) → (b : B a) → (c : C a b) → (d : D a b c) → E a b c d → Set f} 
            {G : (a : A) → (b : B a) → (c : C a b) → (d : D a b c) → (e : E a b c d) → F a b c d e → Set g}
            {H : (a : A) → (b : B a) → (c : C a b) → (d : D a b c) → (e : E a b c d) → (f : F a b c d e) → G a b c d e f → Set h}
            {I : (a : A) → (b : B a) → (c : C a b) → (d : D a b c) → (e : E a b c d) → (f : F a b c d e) → (g : G a b c d e f) → H a b c d e f g → Set i}
          → (P : (a : A) → (b : B a) → (c : C a b) → (d : D a b c) → (e : E a b c d) → (f : F a b c d e) → (g : G a b c d e f) → (h : H a b c d e f g) → I a b c d e f g h → Set j) 
          → {x1 : A}                         → {y1 : A}                         → (eq1 : x1 ≡ y1)
          → {x2 : B x1}                      → {y2 : B y1}                      → (eq2 : subst B eq1 x2 ≡ y2)
          → {x3 : C x1 x2}                   → {y3 : C y1 y2}                   → (eq3 : subst₂dep C eq1 eq2 x3 ≡ y3)
          → {x4 : D x1 x2 x3}                → {y4 : D y1 y2 y3}                → (eq4 : subst₃dep D eq1 eq2 eq3 x4 ≡ y4)
          → {x5 : E x1 x2 x3 x4}             → {y5 : E y1 y2 y3 y4}             → (eq5 : subst₄dep E eq1 eq2 eq3 eq4 x5 ≡ y5)
          → {x6 : F x1 x2 x3 x4 x5}          → {y6 : F y1 y2 y3 y4 y5}          → (eq6 : subst₅dep F eq1 eq2 eq3 eq4 eq5 x6 ≡ y6)
          → {x7 : G x1 x2 x3 x4 x5 x6}       → {y7 : G y1 y2 y3 y4 y5 y6}       → (eq7 : subst₆dep G eq1 eq2 eq3 eq4 eq5 eq6 x7 ≡ y7)
          → {x8 : H x1 x2 x3 x4 x5 x6 x7}    → {y8 : H y1 y2 y3 y4 y5 y6 y7}    → (eq8 : subst₇dep H eq1 eq2 eq3 eq4 eq5 eq6 eq7 x8 ≡ y8)
          → {x9 : I x1 x2 x3 x4 x5 x6 x7 x8} → {y9 : I y1 y2 y3 y4 y5 y6 y7 y8} → (eq9 : subst₈dep I eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8 x9 ≡ y9)
          → P x1 x2 x3 x4 x5 x6 x7 x8 x9 → P y1 y2 y3 y4 y5 y6 y7 y8 y9
subst₉dep P refl refl refl refl refl refl refl refl refl p = p


het-subst₂-dep : {a b p : Level} {A : Set a} {B : A → Set b}
               → (P : (a : A) → B a → Set p)
               → {x₁ x₂ : A} {y₁ : B x₁} {y₂ : B x₂}
               → x₁ ≡ x₂ → y₁ ≅ y₂
               → P x₁ y₁ → P x₂ y₂
het-subst₂-dep P refl hrefl p = p
