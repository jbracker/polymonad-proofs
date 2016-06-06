
module Theory.Kleisli where

-- Stdlib
open import Level
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning 

-- Local
open import Theory.Category
open import Theory.Functor
open import Theory.NaturalTransformation 
open import Theory.Monad

open Category hiding ( idR ; idL ) renaming ( _∘_ to _∘C_ ; id to idC )

-- -----------------------------------------------------------------------------
-- Definition of a Kleisli monad/triple
-- -----------------------------------------------------------------------------
record KleisliMonad {ℓ : Level} {C : Category {ℓ = ℓ}} (T : Obj C → Obj C) : Set ℓ where
  field
    η : {a : Obj C} → (Hom C a (T a))
    kext : {a b : Obj C} → (Hom C a (T b)) → (Hom C (T a) (T b))
    
    idR : {a b : Obj C} {k : Hom C a (T b)} 
        → _∘C_ C (kext k) η ≡ k
    idL : {a : Obj C} → kext η ≡ idC C {a = T a}
    
    coher : {a b c : Obj C} {k : Hom C a (T b)} {l : Hom C b (T c)} 
          → kext ( _∘C_ C (kext l) k ) ≡ _∘C_ C (kext l) (kext k)

-- -----------------------------------------------------------------------------
-- Every Kleisli triple gives rise to a functor
-- -----------------------------------------------------------------------------
KleisliMonad→Functor : {ℓ : Level} {C : Category {ℓ = ℓ}} {T : Obj C → Obj C} 
                     → KleisliMonad {C = C} T → Functor C C
KleisliMonad→Functor {C = C} {T = T} km = record 
  { F₀ = F₀
  ; F₁ = F₁
  ; id = idF
  ; dist = distF
  } where
    _∘_ = _∘C_ C
    kext = KleisliMonad.kext km
    η = KleisliMonad.η km
    id = idC C
    F₀ = T
    
    F₁ : {a b : Obj C} → Hom C a b → Hom C (F₀ a) (F₀ b)
    F₁ f = kext (η ∘ f)
    
    idF : {a : Obj C} → F₁ {a = a} id ≡ id {T a}
    idF {a = a} = begin
      F₁ {a = a} id
        ≡⟨ refl ⟩ 
      kext (η ∘ id)
        ≡⟨ cong (λ X → kext X) (Category.idR C) ⟩ 
      kext η
        ≡⟨ KleisliMonad.idL km ⟩ 
      id ∎
    
    distF : {a b c : Obj C} {f : Hom C a b} {g : Hom C b c} 
          → F₁ (g ∘ f) ≡ (F₁ g) ∘ (F₁ f)
    distF {a = a} {b = b} {c = c} {f = f} {g = g} = begin
      F₁ (g ∘ f) 
        ≡⟨ refl ⟩
      kext ( η ∘ (g ∘ f) )
        ≡⟨ cong (λ X → kext X) (assoc C) ⟩
      kext ( (η ∘ g) ∘ f )
        ≡⟨ cong (λ X → kext (X ∘ f)) (sym (KleisliMonad.idR km)) ⟩
      kext ( (kext (η ∘ g) ∘ η) ∘ f )
        ≡⟨ cong (λ X → kext X) (sym (assoc C)) ⟩
      kext ( kext (η ∘ g) ∘ (η ∘ f) )
        ≡⟨ KleisliMonad.coher km ⟩
      kext (η ∘ g) ∘ kext (η ∘ f)
        ≡⟨ refl ⟩
      (F₁ g) ∘ (F₁ f) ∎
  
-- -----------------------------------------------------------------------------
-- Every Kleisli triple is a monad
-- -----------------------------------------------------------------------------
KleisliMonad→Monad : {ℓ : Level} {C : Category {ℓ = ℓ}} {T : Obj C → Obj C}
                   → (km : KleisliMonad {C = C} T) → Monad (KleisliMonad→Functor km)
KleisliMonad→Monad {C = C} {T = T} km = record 
  { η = ηNatTrans 
  ; μ = μNatTrans 
  ; μCoher = μCoher 
  ; ηCoherL = ηCoherL 
  ; ηCoherR = ηCoherR
  } where
    TF = KleisliMonad→Functor km
    IdC = Id[ C ]
    _∘_ = _∘C_ C
    id = idC C
    kext = KleisliMonad.kext km
    ηk = KleisliMonad.η km
    
    μ : (x : Obj C) → Hom C ([ [ TF ]∘[ TF ] ]₀ x) ([ TF ]₀ x)
    μ x = kext (id {a = T x})
    
    η : (x : Obj C) → Hom C ([ IdC ]₀ x) ([ TF ]₀ x)
    η x = KleisliMonad.η km {a = x}
    
    μNatural : {a b : Obj C} {f : Hom C a b} 
            → ([ TF ]₁ f) ∘ μ a ≡ μ b ∘ ([ [ TF ]∘[ TF ] ]₁ f)
    μNatural {a = a} {b = b} {f = f} = begin
      ([ TF ]₁ f) ∘ μ a 
        ≡⟨ refl ⟩
      kext (ηk ∘ f) ∘ kext id
        ≡⟨ sym (KleisliMonad.coher km) ⟩
      kext (kext (ηk ∘ f) ∘ id)
        ≡⟨ cong (λ X → kext X) (Category.idR C) ⟩
      kext (kext (ηk ∘ f))
        ≡⟨ cong (λ X → kext X) (sym (Category.idL C)) ⟩
      kext (id ∘ kext (ηk ∘ f))
        ≡⟨ cong (λ X → kext (X ∘ kext (ηk ∘ f))) (sym (KleisliMonad.idR km)) ⟩
      kext ((kext id ∘ ηk) ∘ kext (ηk ∘ f))
        ≡⟨ cong (λ X → kext X) (sym (assoc C)) ⟩
      kext (kext id ∘ (ηk ∘ kext (ηk ∘ f)))
        ≡⟨ KleisliMonad.coher km ⟩
      kext id ∘ kext (ηk ∘ kext (ηk ∘ f))
        ≡⟨ refl ⟩
      μ b ∘ ([ [ TF ]∘[ TF ] ]₁ f) ∎
    
    ηNatural : {a b : Obj C} {f : Hom C a b} 
            → ([ TF ]₁ f) ∘ η a ≡ η b ∘ ([ IdC ]₁ f)
    ηNatural {a = a} {b = b} {f = f} = begin
      ([ TF ]₁ f) ∘ η a 
        ≡⟨ refl ⟩ 
      kext (η b ∘ f) ∘ η a
        ≡⟨ KleisliMonad.idR km ⟩ 
      η b ∘ f
        ≡⟨ refl ⟩ 
      η b ∘ ([ IdC ]₁ f) ∎
    
    μCoher : {x : Obj C} → μ x ∘ ([ TF ]₁ μ x) ≡ μ x ∘ μ ([ TF ]₀ x)
    μCoher {x = x} = begin
      μ x ∘ ([ TF ]₁ μ x)
        ≡⟨ refl ⟩
      kext id ∘ kext (ηk ∘ kext id)
        ≡⟨ sym (KleisliMonad.coher km) ⟩ 
      kext (kext id ∘ (ηk ∘ kext id))
        ≡⟨ cong kext (assoc C) ⟩ 
      kext ((kext id ∘ ηk) ∘ kext id)
        ≡⟨ cong (λ X → kext (X ∘ kext id)) (KleisliMonad.idR km) ⟩ 
      kext (id ∘ kext id)
        ≡⟨ cong kext (Category.idL C) ⟩ 
      kext (kext id)
        ≡⟨ cong kext (sym (Category.idR C)) ⟩ 
      kext (kext id ∘ id)
        ≡⟨ KleisliMonad.coher km ⟩ 
      kext id ∘ kext id
        ≡⟨ refl ⟩
      μ x ∘ μ ([ TF ]₀ x) ∎
    
    ηCoherL : {x : Obj C} → μ x ∘ ([ TF ]₁ η x) ≡ η⟨ Id⟨ TF ⟩ ⟩ x
    ηCoherL {x = x} = begin
      μ x ∘ ([ TF ]₁ η x) 
        ≡⟨ refl ⟩
      kext id ∘ kext (ηk ∘ ηk) 
        ≡⟨ sym (KleisliMonad.coher km) ⟩
      kext (kext id ∘ (ηk ∘ ηk))
        ≡⟨ cong kext (assoc C) ⟩
      kext ((kext id ∘ ηk) ∘ ηk)
        ≡⟨ cong (λ X → kext (X ∘ ηk)) (KleisliMonad.idR km) ⟩
      kext (id ∘ ηk)
        ≡⟨ cong kext (Category.idL C) ⟩
      kext ηk
        ≡⟨ KleisliMonad.idL km ⟩
      id
        ≡⟨ refl ⟩
      η⟨ Id⟨ TF ⟩ ⟩ x ∎
    
    ηCoherR : {x : Obj C} → μ x ∘ (η ([ TF ]₀ x)) ≡ η⟨ Id⟨ TF ⟩ ⟩ x
    ηCoherR {x = x} = KleisliMonad.idR km
    
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
Monad→KleisliMonad : {ℓ : Level} {C : Category {ℓ = ℓ}} {T : Functor C C}
                   → Monad T → KleisliMonad {C = C} (Functor.F₀ T)  
Monad→KleisliMonad {C = C} {T = T} m = record 
  { η = η 
  ; kext = kext
  ; idR = idR
  ; idL = idL
  ; coher = coher 
  } where
    _∘_ = _∘C_ C
    id = idC C
    
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
    
    idR : {a b : Obj C} {k : Hom C a (T₀ b)} 
        → kext k ∘ η ≡ k
    idR {a} {b} {k = k} = begin
      kext k ∘ η 
        ≡⟨ refl ⟩
      (μ ∘ T₁ k) ∘ η 
        ≡⟨ sym (assoc C) ⟩
      μ ∘ (T₁ k ∘ η)
        ≡⟨ cong (λ X → μ ∘ X) (NaturalTransformation.natural (Monad.η m)) ⟩
      μ ∘ (η ∘ k)
        ≡⟨ assoc C ⟩
      (μ ∘ η) ∘ k
        ≡⟨ cong (λ X → X ∘ k) (Monad.ηCoherR m) ⟩
      id ∘ k
        ≡⟨ Category.idL C ⟩
      k ∎
      
    idL : {a : Obj C} → kext {a = a} η ≡ id
    idL = Monad.ηCoherL m

    p : {a : Obj C} → T₁ (μ {a = a}) ≡ μ
    p = {!!}
    
    coher : {a b c : Obj C} {k : Hom C a (T₀ b)} {l : Hom C b (T₀ c)}
          → kext (kext l ∘ k) ≡ kext l ∘ kext k
    coher {k = k} {l = l} = begin
      kext (kext l ∘ k) 
        ≡⟨ refl ⟩
      μ ∘ T₁ ((μ ∘ T₁ l) ∘ k)
        ≡⟨ cong (λ X → μ ∘ X) (Functor.dist T) ⟩
      μ ∘ (T₁ (μ ∘ T₁ l) ∘ T₁ k)
        ≡⟨ cong (λ X → μ ∘ (X ∘ T₁ k)) (Functor.dist T) ⟩
      μ ∘ ((T₁ μ ∘ T₁ (T₁ l)) ∘ T₁ k)
        ≡⟨ cong (λ X → μ ∘ ((X ∘ T₁ (T₁ l)) ∘ T₁ k)) {!p!} ⟩
      μ ∘ ((μ ∘ T₁ (T₁ l)) ∘ T₁ k)
        ≡⟨ cong (λ X → μ ∘ (X ∘ T₁ k)) (sym (NaturalTransformation.natural (Monad.μ m))) ⟩
      μ ∘ ((T₁ l ∘ μ) ∘ T₁ k)
        ≡⟨ cong (λ X → μ ∘ X) (sym (assoc C)) ⟩
      μ ∘ (T₁ l ∘ (μ ∘ T₁ k))
        ≡⟨ assoc C ⟩
      (μ ∘ T₁ l) ∘ (μ ∘ T₁ k)
        ≡⟨ refl ⟩
      kext l ∘ kext k ∎
-- μ ∘ Tμ ≡ μ ∘ μT

-- dist : ∀ {a b c} {f : Hom C a b} {g : Hom C b c} 
--         → F₁ (g ∘ f) ≡ (F₁ g) ∘ (F₁ f)
