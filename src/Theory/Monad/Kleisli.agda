
module Theory.Monad.Kleisli where

-- Stdlib
open import Level
open import Function hiding ( id ) renaming ( _∘_ to _∘F_ )
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( refl to hrefl ; sym to hsym ; trans to htrans ; cong to hcong ; proof-irrelevance to het-proof-irrelevance )
open ≡-Reasoning 

-- Local
open import Bijection renaming ( refl to brefl ; sym to bsym ; trans to btrans )
open import Equality
open import Congruence
open import Extensionality

open import Theory.Category.Definition
open import Theory.Functor.Definition
open import Theory.Functor.Composition
open import Theory.Natural.Transformation 
open import Theory.Monad.Definition

open Category using ( Obj ; Hom )

open NaturalTransformation renaming ( η to nat-η )

-- -----------------------------------------------------------------------------
-- Definition of a Kleisli monad/triple
-- -----------------------------------------------------------------------------
record KleisliTriple {ℓC₀ ℓC₁ : Level} {C : Category {ℓC₀} {ℓC₁}} (T : Obj C → Obj C) : Set (ℓC₀ ⊔ ℓC₁) where
  constructor kleisli-triple
  
  open Category C hiding ( Obj ; Hom ; left-id ; right-id )
  
  field
    η : {a : Obj C} → (Hom C a (T a))
    kext : {a b : Obj C} → (Hom C a (T b)) → (Hom C (T a) (T b))
  
  field
    right-id : {a b : Obj C} {k : Hom C a (T b)} → kext k ∘ η ≡ k
    
    left-id : {a : Obj C} → kext η ≡ id {a = T a}
    
    coher : {a b c : Obj C} {k : Hom C a (T b)} {l : Hom C b (T c)} 
          → kext ( kext l ∘ k ) ≡ kext l ∘ kext k


private
  module KleisliEquality {Cℓ₀ Cℓ₁ : Level} {C : Category {Cℓ₀} {Cℓ₁}} {T : Obj C → Obj C} where
    _∘_ = Category._∘_ C
    id = Category.id C
    
    abstract
      kleisli-triple-eq : {η₀ : {a : Obj C} → (Hom C a (T a))}
                        → {η₁ : {a : Obj C} → (Hom C a (T a))}
                        → {kext₀ : {a b : Obj C} → (Hom C a (T b)) → (Hom C (T a) (T b))}
                        → {kext₁ : {a b : Obj C} → (Hom C a (T b)) → (Hom C (T a) (T b))}
                        → {right-id₀ : {a b : Obj C} {k : Hom C a (T b)} → kext₀ k ∘ η₀ ≡ k}
                        → {right-id₁ : {a b : Obj C} {k : Hom C a (T b)} → kext₁ k ∘ η₁ ≡ k}
                        → {left-id₀ : {a : Obj C} → kext₀ η₀ ≡ id {a = T a}}
                        → {left-id₁ : {a : Obj C} → kext₁ η₁ ≡ id {a = T a}}
                        → {coher₀ : {a b c : Obj C} {k : Hom C a (T b)} {l : Hom C b (T c)} → kext₀ ( kext₀ l ∘ k ) ≡ kext₀ l ∘ kext₀ k}
                        → {coher₁ : {a b c : Obj C} {k : Hom C a (T b)} {l : Hom C b (T c)} → kext₁ ( kext₁ l ∘ k ) ≡ kext₁ l ∘ kext₁ k}
                        → (λ {a} → η₀ {a}) ≡ η₁
                        → (λ {a} {b} f → kext₀ {a} {b} f) ≡ kext₁
                        → kleisli-triple {C = C} {T = T} η₀ kext₀ right-id₀ left-id₀ coher₀ ≡ kleisli-triple {T = T} η₁ kext₁ right-id₁ left-id₁ coher₁
      kleisli-triple-eq {η₀ = η} {.η} {kext} {.kext} {right-id₀} {right-id₁} {left-id₀} {left-id₁} {coher₀} {coher₁} refl refl 
        = cong₃ (kleisli-triple η kext) 
                (implicit-fun-ext $ λ a → implicit-fun-ext $ λ b → implicit-fun-ext $ λ k → proof-irrelevance right-id₀ right-id₁)
                (implicit-fun-ext $ λ a → proof-irrelevance left-id₀ left-id₁)
                (implicit-fun-ext $ λ a → implicit-fun-ext $ λ b → implicit-fun-ext $ λ c → implicit-fun-ext $ λ k → implicit-fun-ext $ λ l → proof-irrelevance coher₀ coher₁)

open KleisliEquality using ( kleisli-triple-eq ) public

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
    
    abstract
      idF : {a : Obj C} → F₁ {a = a} id ≡ id {T a}
      idF {a = a} = begin
        F₁ {a = a} id
          ≡⟨ refl ⟩ 
        kext (η ∘ id)
          ≡⟨ cong (λ X → kext X) (Category.left-id C) ⟩ 
        kext η
          ≡⟨ KleisliTriple.left-id km ⟩ 
        id ∎
    
    abstract
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
    
    abstract
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
    
    abstract
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
    
    abstract
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
    
    abstract
      ηCoherL : {x : Obj C} → μ x ∘ ([ TF ]₁ (η x)) ≡ nat-η Id⟨ TF ⟩ x
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
        nat-η Id⟨ TF ⟩ x ∎
    
    abstract
      ηCoherR : {x : Obj C} → μ x ∘ (η ([ TF ]₀ x)) ≡ nat-η Id⟨ TF ⟩ x
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
    η {a = a} = nat-η (Monad.η m) a
    
    μ : {a : Obj C} → Hom C (T₀ (T₀ a)) (T₀ a)
    μ {a = a} = nat-η (Monad.μ m) a

    kext : {a b : Obj C} → Hom C a (T₀ b) → Hom C (T₀ a) (T₀ b)
    kext f = μ ∘ T₁ f
    
    abstract
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
    
    abstract
      left-id : {a : Obj C} → kext {a = a} η ≡ id
      left-id = Monad.η-left-coher m
    
    abstract
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


Monad↔KleisliTriple : {ℓC₀ ℓC₁ : Level} {C : Category {ℓC₀} {ℓC₁}}
                    → Σ (Functor C C) Monad
                    ↔ Σ (Obj C → Obj C) (KleisliTriple {C = C})
Monad↔KleisliTriple {ℓC₀} {ℓC₁} {C} =
  bijection m→km km→m
    (λ x → Σ-eq refl (≡-to-≅ (kleisli-triple-eq refl (implicit-fun-ext $ λ a → implicit-fun-ext $ λ b → fun-ext $ λ f → kext-eq x {a} {b} f))))
    (λ x → Σ-eq (F-eq x) (het-monad-eq (F-eq x)
                                       (het-natural-transformation-eq refl (F-eq x) (≡-to-≅ (η-eq x)))
                                       (het-natural-transformation-eq (cong (λ X → [ X ]∘[ X ]) (F-eq x)) (F-eq x) (≡-to-≅ (μ-eq x)))))
  where
    m→km : Σ (Functor C C) Monad → Σ (Obj C → Obj C) (KleisliTriple {C = C})
    m→km (T , m) = Functor.F₀ T , Monad→KleisliTriple m

    km→m : Σ (Obj C → Obj C) (KleisliTriple {C = C}) → Σ (Functor C C) Monad
    km→m (T₀ , km) = (KleisliTriple→Functor km) , (KleisliTriple→Monad km)

    open KleisliTriple

    _∘_ = Category._∘_ C
    id = Category.id C
    
    kext-eq : (x : Σ (Obj C → Obj C) KleisliTriple)
            → {a b : Obj C} (f : Hom C a (proj₁ (m→km (km→m x)) b))
            → kext (proj₂ (m→km (km→m x))) f ≡ kext (proj₂ x) f
    kext-eq x f = begin
      kext (proj₂ (m→km (km→m x))) f
        ≡⟨ refl ⟩
      kext km id ∘ kext km (η km ∘ f)
        ≡⟨ sym $ coher km ⟩
      kext km (kext km id ∘ (η km ∘ f))
        ≡⟨ cong (λ X → kext km X) (Category.assoc C) ⟩
      kext km ((kext km id ∘ η km) ∘ f)
        ≡⟨ cong (λ X → kext km (X ∘ f)) (right-id km) ⟩
      kext km (id ∘ f)
        ≡⟨ cong (kext km) (Category.right-id C) ⟩
      kext km f ∎
      where km = proj₂ x

    F₁-eq : (x : Σ (Functor C C) Monad)
          → {a b : Obj C} (f : Hom C a b)
          → Functor.F₁ (proj₁ (km→m (m→km x))) f ≡ Functor.F₁ (proj₁ x) f
    F₁-eq x {a} {b} f = begin
      Functor.F₁ (proj₁ (km→m (m→km x))) f
        ≡⟨ refl ⟩
      nat-η (Monad.μ m) b ∘ [ F ]₁ (nat-η (Monad.η m) b ∘ f)
        ≡⟨ sym $ Monad.functor-connection m {α = a} {β = b} f ⟩
      Functor.F₁ F f ∎
      where m = proj₂ x
            F = proj₁ x

    F-eq : (x : Σ (Functor C C) Monad) → proj₁ (km→m (m→km x)) ≡ proj₁ x
    F-eq x = (functor-eq refl (≡-to-≅ (implicit-fun-ext $ λ a → implicit-fun-ext $ λ b → fun-ext $ λ f → F₁-eq x {a} {b} f)))

    η-eq : (x : Σ (Functor C C) Monad) → nat-η (Monad.η (proj₂ (km→m (m→km x)))) ≡ nat-η (Monad.η (proj₂ x))
    η-eq x = fun-ext $ λ a → refl
    
    μ-eq : (x : Σ (Functor C C) Monad) → nat-η (Monad.μ (proj₂ (km→m (m→km x)))) ≡ nat-η (Monad.μ (proj₂ x))
    μ-eq x = fun-ext $ λ a → begin
      nat-η (Monad.μ (proj₂ (km→m (m→km x)))) a
        ≡⟨ refl ⟩
      nat-η (Monad.μ m) a ∘ [ F ]₁ id 
        ≡⟨ cong (λ X → nat-η (Monad.μ m) a ∘ X) (Functor.id F) ⟩
      nat-η (Monad.μ m) a ∘ id 
        ≡⟨ Category.left-id C ⟩
      nat-η (Monad.μ m) a ∎
      where m = proj₂ x
            F = proj₁ x

KleisliTriple↔Monad : {ℓC₀ ℓC₁ : Level} {C : Category {ℓC₀} {ℓC₁}}
                    → Σ (Obj C → Obj C) (KleisliTriple {C = C})
                    ↔ Σ (Functor C C) Monad
KleisliTriple↔Monad = bsym Monad↔KleisliTriple

