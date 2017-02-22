
module Theory.Monad.Kleisli where

-- Stdlib
open import Level
open import Function hiding ( id ) renaming ( _∘_ to _∘F_ )
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning 

-- Local
open import Theory.Category
open import Theory.Functor
open import Theory.Natural.Transformation 
open import Theory.Monad

open Category using ( Obj ; Hom )

-- -----------------------------------------------------------------------------
-- Definition of a Kleisli monad/triple
-- -----------------------------------------------------------------------------
record KleisliTriple {ℓC₀ ℓC₁ : Level} {C : Category {ℓC₀} {ℓC₁}} (T : Obj C → Obj C) : Set (ℓC₀ ⊔ ℓC₁) where
  open Category C hiding ( Obj ; Hom ; left-id ; right-id )
  
  field
    η : {a : Obj C} → (Hom C a (T a))
    kext : {a b : Obj C} → (Hom C a (T b)) → (Hom C (T a) (T b))
  
  field
    right-id : {a b : Obj C} {k : Hom C a (T b)} 
            → kext k ∘ η ≡ k
    
    left-id : {a : Obj C} → kext η ≡ id {a = T a}
    
    coher : {a b c : Obj C} {k : Hom C a (T b)} {l : Hom C b (T c)} 
          → kext ( kext l ∘ k ) ≡ kext l ∘ kext k

-- -----------------------------------------------------------------------------
-- Every Kleisli triple gives rise to a functor
-- -----------------------------------------------------------------------------
KleisliTriple→Functor : {ℓC₀ ℓC₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {T : Obj C → Obj C} 
                     → KleisliTriple {C = C} T → Functor C C
KleisliTriple→Functor {C = C} {T = T} km = record 
  { F₀ = F₀
  ; F₁ = F₁
  ; id = idF
  ; compose = composeF
  } where
    open Category C hiding ( Obj ; Hom )
    kext = KleisliTriple.kext km
    η = KleisliTriple.η km
    F₀ = T
    
    F₁ : {a b : Obj C} → Hom C a b → Hom C (F₀ a) (F₀ b)
    F₁ f = kext (η ∘ f)
    
    idF : {a : Obj C} → F₁ {a = a} id ≡ id {T a}
    idF {a = a} = begin
      F₁ {a = a} id
        ≡⟨ refl ⟩ 
      kext (η ∘ id)
        ≡⟨ cong (λ X → kext X) (Category.left-id C) ⟩ 
      kext η
        ≡⟨ KleisliTriple.left-id km ⟩ 
      id ∎
    
    composeF : {a b c : Obj C} {f : Hom C a b} {g : Hom C b c} 
          → F₁ (g ∘ f) ≡ (F₁ g) ∘ (F₁ f)
    composeF {a = a} {b = b} {c = c} {f = f} {g = g} = begin
      F₁ (g ∘ f) 
        ≡⟨ refl ⟩
      kext ( η ∘ (g ∘ f) )
        ≡⟨ cong (λ X → kext X) assoc ⟩
      kext ( (η ∘ g) ∘ f )
        ≡⟨ cong (λ X → kext (X ∘ f)) (sym (KleisliTriple.right-id km)) ⟩
      kext ( (kext (η ∘ g) ∘ η) ∘ f )
        ≡⟨ cong (λ X → kext X) (sym assoc) ⟩
      kext ( kext (η ∘ g) ∘ (η ∘ f) )
        ≡⟨ KleisliTriple.coher km ⟩
      kext (η ∘ g) ∘ kext (η ∘ f)
        ≡⟨ refl ⟩
      (F₁ g) ∘ (F₁ f) ∎
  
-- -----------------------------------------------------------------------------
-- Every Kleisli triple is a monad
-- -----------------------------------------------------------------------------
KleisliTriple→Monad : {ℓC₀ ℓC₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {T : Obj C → Obj C}
                   → (km : KleisliTriple {C = C} T) → Monad (KleisliTriple→Functor km)
KleisliTriple→Monad {C = C} {T = T} km = record 
  { η = ηNatTrans 
  ; μ = μNatTrans 
  ; μ-coher = μCoher 
  ; η-left-coher = ηCoherL 
  ; η-right-coher = ηCoherR
  } where
    open Category C hiding ( Obj ; Hom )
    TF = KleisliTriple→Functor km
    IdC = Id[ C ]
    kext = KleisliTriple.kext km
    ηk = KleisliTriple.η km
    
    μ : (x : Obj C) → Hom C ([ [ TF ]∘[ TF ] ]₀ x) ([ TF ]₀ x)
    μ x = kext (id {a = T x})
    
    η : (x : Obj C) → Hom C ([ IdC ]₀ x) ([ TF ]₀ x)
    η x = KleisliTriple.η km {a = x}
    
    μNatural : {a b : Obj C} {f : Hom C a b} 
            → ([ TF ]₁ f) ∘ μ a ≡ μ b ∘ ([ [ TF ]∘[ TF ] ]₁ f)
    μNatural {a = a} {b = b} {f = f} = begin
      ([ TF ]₁ f) ∘ μ a 
        ≡⟨ refl ⟩
      kext (ηk ∘ f) ∘ kext id
        ≡⟨ sym (KleisliTriple.coher km) ⟩
      kext (kext (ηk ∘ f) ∘ id)
        ≡⟨ cong (λ X → kext X) (Category.left-id C) ⟩
      kext (kext (ηk ∘ f))
        ≡⟨ cong (λ X → kext X) (sym (Category.right-id C)) ⟩
      kext (id ∘ kext (ηk ∘ f))
        ≡⟨ cong (λ X → kext (X ∘ kext (ηk ∘ f))) (sym (KleisliTriple.right-id km)) ⟩
      kext ((kext id ∘ ηk) ∘ kext (ηk ∘ f))
        ≡⟨ cong (λ X → kext X) (sym assoc) ⟩
      kext (kext id ∘ (ηk ∘ kext (ηk ∘ f)))
        ≡⟨ KleisliTriple.coher km ⟩
      kext id ∘ kext (ηk ∘ kext (ηk ∘ f))
        ≡⟨ refl ⟩
      μ b ∘ ([ [ TF ]∘[ TF ] ]₁ f) ∎
    
    ηNatural : {a b : Obj C} {f : Hom C a b} 
            → ([ TF ]₁ f) ∘ η a ≡ η b ∘ ([ IdC ]₁ f)
    ηNatural {a = a} {b = b} {f = f} = begin
      ([ TF ]₁ f) ∘ η a 
        ≡⟨ refl ⟩ 
      kext (η b ∘ f) ∘ η a
        ≡⟨ KleisliTriple.right-id km ⟩ 
      η b ∘ f
        ≡⟨ refl ⟩ 
      η b ∘ ([ IdC ]₁ f) ∎
    
    μCoher : {x : Obj C} → μ x ∘ ([ TF ]₁ (μ x)) ≡ μ x ∘ μ ([ TF ]₀ x)
    μCoher {x = x} = begin
      μ x ∘ ([ TF ]₁ (μ x))
        ≡⟨ refl ⟩
      kext id ∘ kext (ηk ∘ kext id)
        ≡⟨ sym (KleisliTriple.coher km) ⟩ 
      kext (kext id ∘ (ηk ∘ kext id))
        ≡⟨ cong kext assoc ⟩ 
      kext ((kext id ∘ ηk) ∘ kext id)
        ≡⟨ cong (λ X → kext (X ∘ kext id)) (KleisliTriple.right-id km) ⟩ 
      kext (id ∘ kext id)
        ≡⟨ cong kext (Category.right-id C) ⟩ 
      kext (kext id)
        ≡⟨ cong kext (sym (Category.left-id C)) ⟩ 
      kext (kext id ∘ id)
        ≡⟨ KleisliTriple.coher km ⟩ 
      kext id ∘ kext id
        ≡⟨ refl ⟩
      μ x ∘ μ ([ TF ]₀ x) ∎
    
    ηCoherL : {x : Obj C} → μ x ∘ ([ TF ]₁ (η x)) ≡ η⟨ Id⟨ TF ⟩ ⟩ x
    ηCoherL {x = x} = begin
      μ x ∘ ([ TF ]₁ (η x)) 
        ≡⟨ refl ⟩
      kext id ∘ kext (ηk ∘ ηk) 
        ≡⟨ sym (KleisliTriple.coher km) ⟩
      kext (kext id ∘ (ηk ∘ ηk))
        ≡⟨ cong kext assoc ⟩
      kext ((kext id ∘ ηk) ∘ ηk)
        ≡⟨ cong (λ X → kext (X ∘ ηk)) (KleisliTriple.right-id km) ⟩
      kext (id ∘ ηk)
        ≡⟨ cong kext (Category.right-id C) ⟩
      kext ηk
        ≡⟨ KleisliTriple.left-id km ⟩
      id
        ≡⟨ refl ⟩
      η⟨ Id⟨ TF ⟩ ⟩ x ∎
    
    ηCoherR : {x : Obj C} → μ x ∘ (η ([ TF ]₀ x)) ≡ η⟨ Id⟨ TF ⟩ ⟩ x
    ηCoherR {x = x} = KleisliTriple.right-id km
    
    μNatTrans : NaturalTransformation [ TF ]∘[ TF ] TF
    μNatTrans = record 
      { η = μ 
      ; natural = μNatural
      }
    
    ηNatTrans : NaturalTransformation Id[ C ] TF
    ηNatTrans = record 
      { η = η 
      ; natural = ηNatural
      }

-- -----------------------------------------------------------------------------
-- Every monad gives rise to a Kleisli triple
-- -----------------------------------------------------------------------------
Monad→KleisliTriple : {ℓC₀ ℓC₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {T : Functor C C}
                    → Monad T → KleisliTriple {C = C} (Functor.F₀ T)  
Monad→KleisliTriple {C = C} {T = T} m = record 
  { η = η 
  ; kext = kext
  ; right-id = right-id
  ; left-id  = left-id
  ; coher = coher 
  } where
    open Category C hiding ( Obj ; Hom ; right-id ; left-id )
    
    T₀ : Obj C → Obj C
    T₀ a = [ T ]₀ a

    T₁ : {a b : Obj C} → Hom C a b → Hom C (T₀ a) (T₀ b)
    T₁ f = [ T ]₁ f
    
    η : {a : Obj C} → Hom C a (T₀ a)
    η {a = a} = η⟨ Monad.η m ⟩ a
    
    μ : {a : Obj C} → Hom C (T₀ (T₀ a)) (T₀ a)
    μ {a = a} = η⟨ Monad.μ m ⟩ a

    kext : {a b : Obj C} → Hom C a (T₀ b) → Hom C (T₀ a) (T₀ b)
    kext f = μ ∘ T₁ f
    
    right-id : {a b : Obj C} {k : Hom C a (T₀ b)} 
        → kext k ∘ η ≡ k
    right-id {a} {b} {k = k} = begin
      kext k ∘ η 
        ≡⟨ refl ⟩
      (μ ∘ T₁ k) ∘ η 
        ≡⟨ sym assoc ⟩
      μ ∘ (T₁ k ∘ η)
        ≡⟨ cong (λ X → μ ∘ X) (NaturalTransformation.natural (Monad.η m)) ⟩
      μ ∘ (η ∘ k)
        ≡⟨ assoc ⟩
      (μ ∘ η) ∘ k
        ≡⟨ cong (λ X → X ∘ k) (Monad.η-right-coher m) ⟩
      id ∘ k
        ≡⟨ Category.right-id C ⟩
      k ∎
      
    left-id : {a : Obj C} → kext {a = a} η ≡ id
    left-id = Monad.η-left-coher m
    
    coher : {a b c : Obj C} {k : Hom C a (T₀ b)} {l : Hom C b (T₀ c)}
          → kext (kext l ∘ k) ≡ kext l ∘ kext k
    coher {k = k} {l = l} = begin
      kext (kext l ∘ k) 
        ≡⟨ refl ⟩
      μ ∘ T₁ ((μ ∘ T₁ l) ∘ k)
        ≡⟨ cong (λ X → μ ∘ X) (Functor.compose T) ⟩
      μ ∘ (T₁ (μ ∘ T₁ l) ∘ T₁ k)
        ≡⟨ cong (λ X → μ ∘ (X ∘ T₁ k)) (Functor.compose T) ⟩
      μ ∘ ((T₁ μ ∘ T₁ (T₁ l)) ∘ T₁ k)
        ≡⟨ assoc ⟩
      (μ ∘ (T₁ μ ∘ T₁ (T₁ l))) ∘ T₁ k
        ≡⟨ cong (λ X → X ∘ T₁ k) assoc ⟩
      ((μ ∘ T₁ μ) ∘ T₁ (T₁ l)) ∘ T₁ k
        ≡⟨ cong (λ X → (X ∘ T₁ (T₁ l)) ∘ T₁ k) (Monad.μ-coher m) ⟩
      ((μ ∘ μ) ∘ T₁ (T₁ l)) ∘ T₁ k
        ≡⟨ cong (λ X → X ∘ T₁ k) (sym assoc) ⟩
      (μ ∘ (μ ∘ T₁ (T₁ l))) ∘ T₁ k
        ≡⟨ sym assoc ⟩
      μ ∘ ((μ ∘ T₁ (T₁ l)) ∘ T₁ k)
        ≡⟨ cong (λ X → μ ∘ (X ∘ T₁ k)) (sym (NaturalTransformation.natural (Monad.μ m))) ⟩
      μ ∘ ((T₁ l ∘ μ) ∘ T₁ k)
        ≡⟨ cong (λ X → μ ∘ X) (sym assoc) ⟩
      μ ∘ (T₁ l ∘ (μ ∘ T₁ k))
        ≡⟨ assoc ⟩
      (μ ∘ T₁ l) ∘ (μ ∘ T₁ k)
        ≡⟨ refl ⟩
      kext l ∘ kext k ∎
