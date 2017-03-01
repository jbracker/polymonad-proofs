
module Congruence where

open import Level
open import Relation.Binary.HeterogeneousEquality renaming ( trans to htrans ; cong to hcong ; subst to hsubst ; subst₂ to hsubst₂ ; sym to hsym ) -- ≅
open import Relation.Binary.PropositionalEquality using ( refl ; _≡_ ; subst ; subst₂ ) 

open import Substitution


-- Congruence with three arguments.
cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
        (f : A → B → C → D) {x y u v r s} 
      → x ≡ y → u ≡ v → r ≡ s 
      → f x u r ≡ f y v s
cong₃ f refl refl refl = refl

-- Congruence with four arguments.
cong₄ : ∀ {a b c d e} {A : Set a} {B : Set b} {C : Set c} {D : Set d} {E : Set e}
        (f : A → B → C → D → E) {x1 y1 x2 y2 x3 y3 x4 y4} 
      → x1 ≡ y1 → x2 ≡ y2 → x3 ≡ y3 → x4 ≡ y4
      → f x1 x2 x3 x4 ≡ f y1 y2 y3 y4
cong₄ f refl refl refl refl = refl

-- Congruence with five arguments.
cong₅ : ∀ {a b c d e f} {A : Set a} {B : Set b} {C : Set c} {D : Set d} {E : Set e} {F : Set f}
        (f : A → B → C → D → E → F) {x1 y1 x2 y2 x3 y3 x4 y4 x5 y5} 
      → x1 ≡ y1 → x2 ≡ y2 → x3 ≡ y3 → x4 ≡ y4 → x5 ≡ y5
      → f x1 x2 x3 x4 x5 ≡ f y1 y2 y3 y4 y5
cong₅ f refl refl refl refl refl = refl

-- Congruence with six arguments.
cong₆ : ∀ {a b c d e f g} {A : Set a} {B : Set b} {C : Set c} {D : Set d} {E : Set e} {F : Set f} {G : Set g}
        (f : A → B → C → D → E → F → G) {x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6} 
      → x1 ≡ y1 → x2 ≡ y2 → x3 ≡ y3 → x4 ≡ y4 → x5 ≡ y5 → x6 ≡ y6
      → f x1 x2 x3 x4 x5 x6 ≡ f y1 y2 y3 y4 y5 y6
cong₆ f refl refl refl refl refl refl = refl

-- Congruence with seven arguments.
cong₇ : ∀ {a b c d e f g h} {A : Set a} {B : Set b} {C : Set c} {D : Set d} {E : Set e} {F : Set f} {G : Set g} {H : Set h}
        (f : A → B → C → D → E → F → G → H) {x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 x7 y7} 
      → x1 ≡ y1 → x2 ≡ y2 → x3 ≡ y3 → x4 ≡ y4 → x5 ≡ y5 → x6 ≡ y6 → x7 ≡ y7
      → f x1 x2 x3 x4 x5 x6 x7 ≡ f y1 y2 y3 y4 y5 y6 y7
cong₇ f refl refl refl refl refl refl refl = refl

-- Congruence with ten arguments.
cong10 : ∀ {a b c d e f g h i j k} {A : Set a} {B : Set b} {C : Set c} {D : Set d} {E : Set e} {F : Set f} {G : Set g} {H : Set h} {I : Set i} {J : Set j} {K : Set k}
        (f : A → B → C → D → E → F → G → H → I → J → K) {x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 x7 y7 x8 y8 x9 y9 x10 y10} 
      → x1 ≡ y1 → x2 ≡ y2 → x3 ≡ y3 → x4 ≡ y4 → x5 ≡ y5 → x6 ≡ y6 → x7 ≡ y7 → x8 ≡ y8 → x9 ≡ y9 → x10 ≡ y10
      → f x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ≡ f y1 y2 y3 y4 y5 y6 y7 y8 y9 y10
cong10 f refl refl refl refl refl refl refl refl refl refl = refl

-- Properly dependently typed congruence with two arguments.
cong₂dep : ∀ {a b c} 
         → {A : Set a} {B : A → Set b} {C : (a : A) → B a → Set c}
         → (f : (a : A) → (b : B a) → C a b) 
         → {x1 : A}    → {y1 : A}    → (eq1 : x1 ≡ y1) 
         → {x2 : B x1} → {y2 : B y1} → (eq2 : subst B eq1 x2 ≡ y2)
         → subst₂dep C eq1 eq2 (f x1 x2) ≡ f y1 y2
cong₂dep f refl refl = refl

-- Properly dependently typed congruence with three arguments.
cong₃dep : ∀ {a b c d} 
         → {A : Set a} {B : A → Set b} {C : (a : A) → B a → Set c}
           {D : (a : A) → (b : B a) → C a b → Set d}
         → (f : (a : A) → (b : B a) → (c : C a b) → D a b c) 
         → {x1 : A}       → {y1 : A}       → (eq1 : x1 ≡ y1) 
         → {x2 : B x1}    → {y2 : B y1}    → (eq2 : subst B eq1 x2 ≡ y2)
         → {x3 : C x1 x2} → {y3 : C y1 y2} → (eq3 : subst₂dep C eq1 eq2 x3 ≡ y3)
         → subst₃dep D eq1 eq2 eq3 (f x1 x2 x3) ≡ f y1 y2 y3
cong₃dep f refl refl refl = refl

-- Properly dependently typed congruence with four arguments.
cong₄dep : ∀ {a b c d e} 
         → {A : Set a} {B : A → Set b} {C : (a : A) → B a → Set c}
           {D : (a : A) → (b : B a) → C a b → Set d}
           {E : (a : A) → (b : B a) → (c : C a b) → D a b c → Set e}
         → (f : (a : A) → (b : B a) → (c : C a b) → (d : D a b c) → E a b c d) 
         → {x1 : A}          → {y1 : A}          → (eq1 : x1 ≡ y1) 
         → {x2 : B x1}       → {y2 : B y1}       → (eq2 : subst B eq1 x2 ≡ y2)
         → {x3 : C x1 x2}    → {y3 : C y1 y2}    → (eq3 : subst₂dep C eq1 eq2 x3 ≡ y3)
         → {x4 : D x1 x2 x3} → {y4 : D y1 y2 y3} → (eq4 : subst₃dep D eq1 eq2 eq3 x4 ≡ y4)
         → subst₄dep E eq1 eq2 eq3 eq4 (f x1 x2 x3 x4) ≡ f y1 y2 y3 y4
cong₄dep f refl refl refl refl = refl

-- Properly dependently typed congruence with five arguments.
cong₅dep : ∀ {a b c d e f} 
         → {A : Set a} {B : A → Set b} {C : (a : A) → B a → Set c}
           {D : (a : A) → (b : B a) → C a b → Set d}
           {E : (a : A) → (b : B a) → (c : C a b) → D a b c → Set e}
           {F : (a : A) → (b : B a) → (c : C a b) → (d : D a b c) → E a b c d → Set f}
         → (z : (a : A) → (b : B a) → (c : C a b) → (d : D a b c) → (e : E a b c d) → F a b c d e) 
         → {x1 : A}             → {y1 : A}             → (eq1 : x1 ≡ y1) 
         → {x2 : B x1}          → {y2 : B y1}          → (eq2 : subst B eq1 x2 ≡ y2)
         → {x3 : C x1 x2}       → {y3 : C y1 y2}       → (eq3 : subst₂dep C eq1 eq2 x3 ≡ y3)
         → {x4 : D x1 x2 x3}    → {y4 : D y1 y2 y3}    → (eq4 : subst₃dep D eq1 eq2 eq3 x4 ≡ y4)
         → {x5 : E x1 x2 x3 x4} → {y5 : E y1 y2 y3 y4} → (eq5 : subst₄dep E eq1 eq2 eq3 eq4 x5 ≡ y5)
         → subst₅dep F eq1 eq2 eq3 eq4 eq5 (z x1 x2 x3 x4 x5) ≡ z y1 y2 y3 y4 y5
cong₅dep z refl refl refl refl refl = refl

-- Properly dependently typed congruence with six arguments.
cong₆dep : ∀ {a b c d e f g} 
         → {A : Set a} {B : A → Set b} {C : (a : A) → B a → Set c}
           {D : (a : A) → (b : B a) → C a b → Set d}
           {E : (a : A) → (b : B a) → (c : C a b) → D a b c → Set e}
           {F : (a : A) → (b : B a) → (c : C a b) → (d : D a b c) → E a b c d → Set f}
           {G : (a : A) → (b : B a) → (c : C a b) → (d : D a b c) → (e : E a b c d) → F a b c d e → Set g}
         → (z : (a : A) → (b : B a) → (c : C a b) → (d : D a b c) → (e : E a b c d) → (f : F a b c d e) → G a b c d e f) 
         → {x1 : A}                → {y1 : A}                → (eq1 : x1 ≡ y1) 
         → {x2 : B x1}             → {y2 : B y1}             → (eq2 : subst B eq1 x2 ≡ y2)
         → {x3 : C x1 x2}          → {y3 : C y1 y2}          → (eq3 : subst₂dep C eq1 eq2 x3 ≡ y3)
         → {x4 : D x1 x2 x3}       → {y4 : D y1 y2 y3}       → (eq4 : subst₃dep D eq1 eq2 eq3 x4 ≡ y4)
         → {x5 : E x1 x2 x3 x4}    → {y5 : E y1 y2 y3 y4}    → (eq5 : subst₄dep E eq1 eq2 eq3 eq4 x5 ≡ y5)
         → {x6 : F x1 x2 x3 x4 x5} → {y6 : F y1 y2 y3 y4 y5} → (eq6 : subst₅dep F eq1 eq2 eq3 eq4 eq5 x6 ≡ y6)
         → subst₆dep G eq1 eq2 eq3 eq4 eq5 eq6 (z x1 x2 x3 x4 x5 x6) ≡ z y1 y2 y3 y4 y5 y6
cong₆dep z refl refl refl refl refl refl = refl

-- Properly dependently typed congruence with seven arguments.
cong₇dep : ∀ {a b c d e f g h} 
         → {A : Set a} {B : A → Set b} {C : (a : A) → B a → Set c}
           {D : (a : A) → (b : B a) → C a b → Set d}
           {E : (a : A) → (b : B a) → (c : C a b) → D a b c → Set e}
           {F : (a : A) → (b : B a) → (c : C a b) → (d : D a b c) → E a b c d → Set f}
           {G : (a : A) → (b : B a) → (c : C a b) → (d : D a b c) → (e : E a b c d) → F a b c d e → Set g}
           {H : (a : A) → (b : B a) → (c : C a b) → (d : D a b c) → (e : E a b c d) → (f : F a b c d e) → G a b c d e f → Set h}
         → (z : (a : A) → (b : B a) → (c : C a b) → (d : D a b c) → (e : E a b c d) → (f : F a b c d e) → (g : G a b c d e f) → H a b c d e f g) 
         → {x1 : A}                → {y1 : A}                → (eq1 : x1 ≡ y1) 
         → {x2 : B x1}             → {y2 : B y1}             → (eq2 : subst B eq1 x2 ≡ y2)
         → {x3 : C x1 x2}          → {y3 : C y1 y2}          → (eq3 : subst₂dep C eq1 eq2 x3 ≡ y3)
         → {x4 : D x1 x2 x3}       → {y4 : D y1 y2 y3}       → (eq4 : subst₃dep D eq1 eq2 eq3 x4 ≡ y4)
         → {x5 : E x1 x2 x3 x4}    → {y5 : E y1 y2 y3 y4}    → (eq5 : subst₄dep E eq1 eq2 eq3 eq4 x5 ≡ y5)
         → {x6 : F x1 x2 x3 x4 x5} → {y6 : F y1 y2 y3 y4 y5} → (eq6 : subst₅dep F eq1 eq2 eq3 eq4 eq5 x6 ≡ y6)
         → {x7 : G x1 x2 x3 x4 x5 x6} → {y7 : G y1 y2 y3 y4 y5 y6} → (eq7 : subst₆dep G eq1 eq2 eq3 eq4 eq5 eq6 x7 ≡ y7)
         → subst₇dep H eq1 eq2 eq3 eq4 eq5 eq6 eq7 (z x1 x2 x3 x4 x5 x6 x7) ≡ z y1 y2 y3 y4 y5 y6 y7
cong₇dep z refl refl refl refl refl refl refl = refl

-- Properly dependently typed congruence with eight arguments.
cong₈dep : ∀ {a b c d e f g h i} 
         → {A : Set a} {B : A → Set b} {C : (a : A) → B a → Set c}
           {D : (a : A) → (b : B a) → C a b → Set d}
           {E : (a : A) → (b : B a) → (c : C a b) → D a b c → Set e}
           {F : (a : A) → (b : B a) → (c : C a b) → (d : D a b c) → E a b c d → Set f}
           {G : (a : A) → (b : B a) → (c : C a b) → (d : D a b c) → (e : E a b c d) → F a b c d e → Set g}
           {H : (a : A) → (b : B a) → (c : C a b) → (d : D a b c) → (e : E a b c d) → (f : F a b c d e) → G a b c d e f → Set h}
           {I : (a : A) → (b : B a) → (c : C a b) → (d : D a b c) → (e : E a b c d) → (f : F a b c d e) → (g : G a b c d e f) → H a b c d e f g → Set i}
         → (z : (a : A) → (b : B a) → (c : C a b) → (d : D a b c) → (e : E a b c d) → (f : F a b c d e) → (g : G a b c d e f) → (h : H a b c d e f g) → I a b c d e f g h) 
         → {x1 : A}                → {y1 : A}                → (eq1 : x1 ≡ y1) 
         → {x2 : B x1}             → {y2 : B y1}             → (eq2 : subst B eq1 x2 ≡ y2)
         → {x3 : C x1 x2}          → {y3 : C y1 y2}          → (eq3 : subst₂dep C eq1 eq2 x3 ≡ y3)
         → {x4 : D x1 x2 x3}       → {y4 : D y1 y2 y3}       → (eq4 : subst₃dep D eq1 eq2 eq3 x4 ≡ y4)
         → {x5 : E x1 x2 x3 x4}    → {y5 : E y1 y2 y3 y4}    → (eq5 : subst₄dep E eq1 eq2 eq3 eq4 x5 ≡ y5)
         → {x6 : F x1 x2 x3 x4 x5} → {y6 : F y1 y2 y3 y4 y5} → (eq6 : subst₅dep F eq1 eq2 eq3 eq4 eq5 x6 ≡ y6)
         → {x7 : G x1 x2 x3 x4 x5 x6} → {y7 : G y1 y2 y3 y4 y5 y6} → (eq7 : subst₆dep G eq1 eq2 eq3 eq4 eq5 eq6 x7 ≡ y7)
         → {x8 : H x1 x2 x3 x4 x5 x6 x7} → {y8 : H y1 y2 y3 y4 y5 y6 y7} → (eq8 : subst₇dep H eq1 eq2 eq3 eq4 eq5 eq6 eq7 x8 ≡ y8)
         → subst₈dep I eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8 (z x1 x2 x3 x4 x5 x6 x7 x8) ≡ z y1 y2 y3 y4 y5 y6 y7 y8
cong₈dep z refl refl refl refl refl refl refl refl = refl

-- Properly dependently typed congruence with nine arguments.
cong₉dep : ∀ {a b c d e f g h i j} 
         → {A : Set a} {B : A → Set b} {C : (a : A) → B a → Set c}
           {D : (a : A) → (b : B a) → C a b → Set d}
           {E : (a : A) → (b : B a) → (c : C a b) → D a b c → Set e}
           {F : (a : A) → (b : B a) → (c : C a b) → (d : D a b c) → E a b c d → Set f}
           {G : (a : A) → (b : B a) → (c : C a b) → (d : D a b c) → (e : E a b c d) → F a b c d e → Set g}
           {H : (a : A) → (b : B a) → (c : C a b) → (d : D a b c) → (e : E a b c d) → (f : F a b c d e) → G a b c d e f → Set h}
           {I : (a : A) → (b : B a) → (c : C a b) → (d : D a b c) → (e : E a b c d) → (f : F a b c d e) → (g : G a b c d e f) → H a b c d e f g → Set i}
           {J : (a : A) → (b : B a) → (c : C a b) → (d : D a b c) → (e : E a b c d) → (f : F a b c d e) → (g : G a b c d e f) → (h : H a b c d e f g) → I a b c d e f g h → Set j}
         → (z : (a : A) → (b : B a) → (c : C a b) → (d : D a b c) → (e : E a b c d) → (f : F a b c d e) → (g : G a b c d e f) → (h : H a b c d e f g) → (i : I a b c d e f g h) → J a b c d e f g h i) 
         → {x1 : A}                → {y1 : A}                → (eq1 : x1 ≡ y1) 
         → {x2 : B x1}             → {y2 : B y1}             → (eq2 : subst B eq1 x2 ≡ y2)
         → {x3 : C x1 x2}          → {y3 : C y1 y2}          → (eq3 : subst₂dep C eq1 eq2 x3 ≡ y3)
         → {x4 : D x1 x2 x3}       → {y4 : D y1 y2 y3}       → (eq4 : subst₃dep D eq1 eq2 eq3 x4 ≡ y4)
         → {x5 : E x1 x2 x3 x4}    → {y5 : E y1 y2 y3 y4}    → (eq5 : subst₄dep E eq1 eq2 eq3 eq4 x5 ≡ y5)
         → {x6 : F x1 x2 x3 x4 x5} → {y6 : F y1 y2 y3 y4 y5} → (eq6 : subst₅dep F eq1 eq2 eq3 eq4 eq5 x6 ≡ y6)
         → {x7 : G x1 x2 x3 x4 x5 x6} → {y7 : G y1 y2 y3 y4 y5 y6} → (eq7 : subst₆dep G eq1 eq2 eq3 eq4 eq5 eq6 x7 ≡ y7)
         → {x8 : H x1 x2 x3 x4 x5 x6 x7} → {y8 : H y1 y2 y3 y4 y5 y6 y7} → (eq8 : subst₇dep H eq1 eq2 eq3 eq4 eq5 eq6 eq7 x8 ≡ y8)
         → {x9 : I x1 x2 x3 x4 x5 x6 x7 x8} → {y9 : I y1 y2 y3 y4 y5 y6 y7 y8} → (eq9 : subst₈dep I eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8 x9 ≡ y9)
         → subst₉dep J eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8 eq9 (z x1 x2 x3 x4 x5 x6 x7 x8 x9) ≡ z y1 y2 y3 y4 y5 y6 y7 y8 y9
cong₉dep z refl refl refl refl refl refl refl refl refl = refl
