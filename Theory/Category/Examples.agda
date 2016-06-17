
module Theory.Category.Examples where 

-- Stdlib
open import Level renaming ( suc to lsuc ; zero to lzero )
open import Function renaming ( id to idF ; _∘_ to _∘F_ )
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Utilities
open import Theory.Category
open import Theory.Functor

-- The unit category with exactly one element and one morphism.
unitCategory : {ℓ₀ ℓ₁ : Level} → Category {ℓ₀ = ℓ₀} {ℓ₁ = ℓ₁}
unitCategory = record
  { Obj = Lift ⊤
  ; Hom = λ _ _ → Lift ⊤
  ; _∘_ = λ _ _ → lift tt
  ; id = lift tt
  ; assoc = refl
  ; idL = refl
  ; idR = refl
  }

-- Category of sets and functions.
setCategory : {ℓ₀ : Level} → Category {ℓ₀ = lsuc ℓ₀}
setCategory {ℓ₀ = ℓ₀} = record
  { Obj = Set ℓ₀
  ; Hom = λ a b → (a → b)
  ; _∘_ = λ f g → f ∘F g
  ; id = idF
  ; assoc = refl
  ; idL = refl
  ; idR = refl
  }

subst₄ : ∀ {a b c d p} {A : Set a} {B : Set b} {C : Set c} {D : Set d} 
       → (P : A → B → C → D → Set p)
       → ∀ {x₁ x₂ y₁ y₂ z₁ z₂ w₁ w₂} 
       → x₁ ≡ x₂ → y₁ ≡ y₂ → z₁ ≡ z₂ → w₁ ≡ w₂ 
       → P x₁ y₁ z₁ w₁ → P x₂ y₂ z₂ w₂
subst₄ P refl refl refl refl p = p

cong₃' : ∀ {a b c d} {A : Set a} {B : A → Set b} {C : A → Set c}
        (f : (a : A) → B a → C a → Set d) {x y} {u} {v} {r} {s} 
      → (eqA : x ≡ y) → (eqB : u ≡ v) → r ≡ s
      → f x u r ≡ f y (subst B eqA v) (subst C eqA s)
cong₃' f refl refl refl = refl

open Category

congFunctor : {Cℓ₀ Cℓ₁ Dℓ₀ Dℓ₁ : Level} {C : Category {Cℓ₀} {Cℓ₁}} {D : Category {Dℓ₀} {Dℓ₁}} 
            → {F₀ G₀ : Obj C → Obj D}
            → {F₁ : (a b : Obj C) → Hom C a b → Hom D (F₀ a) (F₀ b)}
            → {G₁ : (a b : Obj C) → Hom C a b → Hom D (G₀ a) (G₀ b)}
            → {idF : {a : Obj C} → F₁ a a (id C) ≡ id D}
            → {idG : {a : Obj C} → G₁ a a (id C) ≡ id D}
            → {distF : ∀ {a b c} {f : Hom C a b} {g : Hom C b c} → F₁ a c (_∘_ C g f) ≡ _∘_ D (F₁ b c g) (F₁ a b f)}
            → {distG : ∀ {a b c} {f : Hom C a b} {g : Hom C b c} → G₁ a c (_∘_ C g f) ≡ _∘_ D (G₁ b c g) (G₁ a b f)}
            → (eq₀ : F₀ ≡ G₀)
            → (eq₁ : F₁ ≡ subst₂ (λ X Y → (a b : Obj C) → Hom C a b → Hom D (X a) (Y b)) (sym eq₀) (sym eq₀) G₁ )
            → functor {C = C} {D = D} F₀ (λ {a b} → F₁ a b) idF distF ≡ functor {C = C} {D = D} G₀ (λ {a b} → G₁ a b) idG distG
congFunctor {Cℓ₀} {Cℓ₁} {Dℓ₀} {Dℓ₁} {F₀ = F₀} {F₁ = F₁} {idF = idF} {idG} {distF} {distG} refl refl = cong₂ (functor F₀ (λ {a b} → F₁ a b)) {!proof-irrelevance {a = Dℓ₁} idF idG!} {!!} {- begin 
  functor F₀ F₁ idF distF 
    ≡⟨ {!cong₃' (λ X Y Z → functor {C = C} {D = D} F₀ (λ {a b} → X {a} {b}) (λ {a} → Y {a}) (λ {a b c} {f} {g} → Z {a} {b} {c} {f} {g}) ) ? ? ?!} ⟩ 
  functor F₀ G₁ idG distG ∎ -}

catCategory : {ℓ₀ ℓ₁ : Level} → Category {ℓ₀ = lsuc (ℓ₀ ⊔ ℓ₁)} {ℓ₁ = ℓ₀ ⊔ ℓ₁}
catCategory {ℓ₀} {ℓ₁} = record
  { Obj = Category {ℓ₀} {ℓ₁}
  ; Hom = λ C D → Functor C D
  ; _∘_ = [_]∘[_]
  ; id = λ {C} → Id[ C ]
  ; assoc = λ {a b c d} {f} {g} {h} → assoc' {a} {b} {c} {d} {f} {g} {h}
  ; idL = idL'
  ; idR = idR'
  } where
    assoc' : {a b c d : Category} {f : Functor a b} {g : Functor b c} {h : Functor c d} 
           → [ h ]∘[ [ g ]∘[ f ] ] ≡ [ [ h ]∘[ g ] ]∘[ f ]
    assoc' = {!!}
    
    idL' : {a b : Category} {f : Functor a b} → [ Id[ b ] ]∘[ f ] ≡ f
    idL' = {!!}

    idR' : {a b : Category} {f : Functor a b} → [ f ]∘[ Id[ a ] ] ≡ f
    idR' = refl
