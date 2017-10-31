
-- Stdlib
open import Level
open import Function hiding ( id ) renaming ( _∘_ to _∘F_ )
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( refl to hrefl ; sym to hsym ; trans to htrans ; subst to hsubst ; cong to hcong ; cong₂ to hcong₂ )
open ≅-Reasoning 

-- Local
open import Congruence

open import Theory.Category.Definition
open import Theory.Functor.Definition
open import Theory.Natural.Transformation

module Theory.Haskell.Parameterized.Relative.Monad where

open Category hiding ( right-id ; left-id )

-- -----------------------------------------------------------------------------
-- Definition of a parameterized relative monad
-- -----------------------------------------------------------------------------
record ParameterizedRelativeMonad {ℓC₀ ℓC₁ ℓD₀ ℓD₁ ℓI₀ ℓI₁ : Level} 
                                  {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}} (I : Category {ℓI₀} {ℓI₁}) 
                                  (T : {i j : Obj I} → Hom I i j → Obj C → Obj D) 
                                  (J : Functor C D) : Set (ℓC₀ ⊔ ℓC₁ ⊔ ℓD₀ ⊔ ℓD₁ ⊔ ℓI₀ ⊔ ℓI₁) where
  constructor parameterizedRelativeMonad
  
  private
    _∘D_ = _∘_ D
    _∘C_ = _∘_ C
    _∘I_ = _∘_ I
  
  field
    η :  (i : Obj I) → {a : Obj C} → Hom D ([ J ]₀ a) (T (id I {i}) a)
    
    kext : {i j k : Obj I} → (f : Hom I i j) (g : Hom I j k) 
         → {a b : Obj C} → Hom D ([ J ]₀ a) (T g b) → Hom D (T f a) (T (g ∘I f) b)
    
    right-id : {i j : Obj I} → (f : Hom I i j) 
             → {a b : Obj C} {k : Hom D ([ J ]₀ a) (T f b)} 
             → kext (id I) f k ∘D η i ≅ k
    
    left-id : {i j : Obj I} → (f : Hom I i j) 
            → {a : Obj C}
            → kext f (id I) (η j {a}) ≅ id D {a = T f a}
    
    coher : {i j v w : Obj I} → (f : Hom I i j) → (g : Hom I j v) → (h : Hom I v w) 
          → {a b c : Obj C} {k : Hom D ([ J ]₀ a) (T g b)} {l : Hom D ([ J ]₀ b) (T h c)} 
          → kext f (h ∘I g) ( (kext g h l) ∘D k ) ≅ kext (g ∘I f) h l ∘D kext f g k
  
  abstract
    functor-kext-compose : {i j : Obj I} → (fI : Hom I i j) 
                         → {a b c : Obj C} {f : Hom C a b} {g : Hom C b c} 
                         → kext fI (id I) (η j ∘D [ J ]₁ (g ∘C f)) ≅ kext (id I ∘I fI) (id I) (η j ∘D [ J ]₁ g) ∘D (kext fI (id I) (η j ∘D [ J ]₁ f))
    functor-kext-compose {i} {j} fI {a} {b} {c} {f} {g} = begin
      kext fI (id I) (η j ∘D [ J ]₁ (g ∘C f)) 
        ≡⟨ cong (λ X → kext fI (id I) (η j ∘D X)) (Functor.compose J) ⟩
      kext fI (id I) (η j ∘D ([ J ]₁ g ∘D [ J ]₁ f))
        ≡⟨ cong (kext fI (id I)) (assoc D) ⟩
      kext fI (id I) ((η j ∘D [ J ]₁ g) ∘D [ J ]₁ f)
        ≅⟨ hcong₂ (λ X Y → kext fI X (Y ∘D [ J ]₁ f)) (≡-to-≅ (sym (Category.right-id I))) (hsym (right-id (id I))) ⟩
      kext fI (id I ∘I id I) ((kext (id I) (id I) (η j ∘D [ J ]₁ g) ∘D η j) ∘D [ J ]₁ f)
        ≡⟨ cong (kext fI (id I ∘I id I)) (sym (assoc D)) ⟩
      kext fI (id I ∘I id I) (kext (id I) (id I) (η j ∘D [ J ]₁ g) ∘D (η j ∘D [ J ]₁ f))
        ≅⟨ coher fI (id I) (id I) ⟩
      kext (id I ∘I fI) (id I) (η j ∘D [ J ]₁ g) ∘D (kext fI (id I) (η j ∘D [ J ]₁ f)) ∎

  FunctorT : {i j : Obj I} → (f : Hom I i j) → Functor C D
  FunctorT {i} {j} f = functor T₀ T₁ T-id T-compose
    where
      T₀ = T f
      
      T₁ : {a b : Obj C} → Hom C a b → Hom D (T f a) (T f b)
      T₁ {a} {b} k = subst (λ X → Hom D (T f a) (T X b)) (Category.right-id I) (kext f (id I) (η j ∘D [ J ]₁ k))
      
      abstract
        T-id : {a : Obj C} → T₁ (id C) ≡ id D -- kext {a = a} (η ∘D [ J ]₁ (id C)) ≡ id D
        T-id {a} = ≅-to-≡ $ begin
          T₁ (id C) 
            ≡⟨⟩ 
          subst (λ X → Hom D (T f a) (T X a)) (Category.right-id I) (kext f (id I) (η j ∘D [ J ]₁ (id C)))
            ≅⟨ ≡-subst-removable (λ X → Hom D (T f a) (T X a)) (Category.right-id I) (kext f (id I) (η j ∘D [ J ]₁ (id C))) ⟩ 
          kext f (id I) (η j ∘D [ J ]₁ (id C))
            ≡⟨ cong (λ X → kext f (id I) (η j ∘D X)) (Functor.id J) ⟩ 
          kext f (id I) (η j ∘D id D)
            ≡⟨ cong (kext f (id I)) (Category.left-id D) ⟩ 
          kext f (id I) (η j)
            ≅⟨ left-id f ⟩
          id D ∎
      
      abstract
        T-compose : {a b c : Obj C} {g : Hom C a b} {h : Hom C b c} 
                  → T₁ (h ∘C g) ≡ T₁ h ∘D T₁ g
        T-compose {a} {b} {c} {g} {h} = ≅-to-≡ $ begin
          T₁ (h ∘C g)
            ≡⟨⟩
          subst (λ X → Hom D (T f a) (T X c)) (Category.right-id I) (kext f (id I) (η j ∘D [ J ]₁ (h ∘C g)))
            ≅⟨ ≡-subst-removable (λ X → Hom D (T f a) (T X c)) (Category.right-id I) (kext f (id I) (η j ∘D [ J ]₁ (h ∘C g))) ⟩
          kext f (id I) (η j ∘D [ J ]₁ (h ∘C g))
            ≅⟨ functor-kext-compose f ⟩
          kext (id I ∘I f) (id I) (η j ∘D [ J ]₁ h) ∘D kext f (id I) (η j ∘D [ J ]₁ g)
            ≅⟨ hcong₂ (λ Y Z → kext Y (id I) (η j ∘D [ J ]₁ h) ∘D Z) 
                      (≡-to-≅ (Category.right-id I)) 
                      (hsym (≡-subst-removable (λ X → Hom D (T f a) (T X b)) (Category.right-id I) (kext f (id I) (η j ∘D [ J ]₁ g)))) ⟩
          kext f (id I) (η j ∘D [ J ]₁ h) ∘D subst (λ X → Hom D (T f a) (T X b)) (Category.right-id I) (kext f (id I) (η j ∘D [ J ]₁ g))
            ≅⟨ hcong₂ (λ Y Z → (Hom D (T f b) (T Y c) ∋ Z) ∘D subst (λ X → Hom D (T f a) (T X b)) (Category.right-id I) (kext f (id I) (η j ∘D [ J ]₁ g))) 
                      (≡-to-≅ (Category.right-id I)) 
                      (hsym (≡-subst-removable (λ X → Hom D (T f b) (T X c)) (Category.right-id I) (kext f (id I) (η j ∘D [ J ]₁ h)))) ⟩
          subst (λ X → Hom D (T f b) (T X c)) (Category.right-id I) (kext f (id I) (η j ∘D [ J ]₁ h)) ∘D subst (λ X → Hom D (T f a) (T X b)) (Category.right-id I) (kext f (id I) (η j ∘D [ J ]₁ g))
            ≡⟨⟩
          T₁ h ∘D T₁ g ∎
  
  abstract
    functor-kext-coher : {i j : Obj I} → (fI : Hom I i j)
                       → {a b : Obj C} → (f : Hom C a b)
                       → [ FunctorT fI ]₁ f ≅ kext fI (id I) (η j ∘D [ J ]₁ f)
    functor-kext-coher {i} {j} f {a} {b} k = begin
      [ FunctorT f ]₁ k 
        ≡⟨⟩
      subst (λ X → Hom D (T f a) (T X b)) (Category.right-id I) (kext f (id I) (η j ∘D [ J ]₁ k))
        ≅⟨ ≡-subst-removable (λ X → Hom D (T f a) (T X b)) (Category.right-id I) (kext f (id I) (η j ∘D [ J ]₁ k)) ⟩
      kext f (id I) (η j ∘D [ J ]₁ k) ∎

  NaturalTransformation-η : (i : Obj I)
                          → NaturalTransformation J (FunctorT (id I {i}))
  NaturalTransformation-η i = naturalTransformation (λ _ → η i) natural
    where
      abstract
        natural : {a b : Obj C} {f : Hom C a b} 
                → [ FunctorT (id I) ]₁ f ∘D (η i) ≡ η i ∘D [ J ]₁ f
        natural {a} {b} {f} = ≅-to-≡ $ begin
          [ FunctorT (id I) ]₁ f ∘D η i
            ≡⟨⟩
          subst (λ X → Hom D (T (id I {i}) a) (T X b)) (Category.right-id I {i}) (kext (id I {i}) (id I {i}) (η i ∘D [ J ]₁ f)) ∘D η i 
            ≅⟨ hcong₂ (λ X Y → (Hom D (T (id I {i}) a) (T X b) ∋ Y) ∘D η i) 
                      (≡-to-≅ (sym (Category.right-id I {i}))) 
                      (≡-subst-removable (λ X → Hom D (T (id I {i}) a) (T X b)) (Category.right-id I {i}) (kext (id I {i}) (id I {i}) (η i ∘D [ J ]₁ f))) ⟩
          kext (id I {i}) (id I {i}) (η i ∘D [ J ]₁ f) ∘D η i 
            ≅⟨ right-id (id I {i}) ⟩
          η i ∘D [ J ]₁ f ∎

  NaturalTransformation-kext : {i j : Obj I} → (fI : Hom I i j)
                             → NaturalTransformation (FunctorT fI) (FunctorT fI)
  NaturalTransformation-kext {i} {j} fI = naturalTransformation nat-η natural
    where 
      nat-η : (x : Obj C) → Hom D ([ FunctorT fI ]₀ x) ([ FunctorT fI ]₀ x)
      nat-η x = subst (λ X → Hom D (T fI x) (T X x)) (Category.right-id I) (kext fI (id I) (η j {x}))

      abstract
        natural : {a b : Obj C} {f : Hom C a b} 
                → [ FunctorT fI ]₁ f ∘D nat-η a ≡ nat-η b ∘D [ FunctorT fI ]₁ f
        natural {a} {b} {f} = ≅-to-≡ $ begin
           [ FunctorT fI ]₁ f ∘D nat-η a 
             ≡⟨⟩
           subst (λ X → Hom D (T fI a) (T X b)) (Category.right-id I) (kext fI (id I) (η j ∘D [ J ]₁ f)) ∘D subst (λ X → Hom D (T fI a) (T X a)) (Category.right-id I) (kext fI (id I) (η j {a}))
             ≅⟨ hcong₂ (λ Y Z → (Hom D (T fI a) (T Y b) ∋ Z) ∘D subst (λ X → Hom D (T fI a) (T X a)) (Category.right-id I) (kext fI (id I) (η j {a}))) 
                       (≡-to-≅ (sym (Category.right-id I))) 
                       (≡-subst-removable (λ X → Hom D (T fI a) (T X b)) (Category.right-id I) (kext fI (id I) (η j ∘D [ J ]₁ f))) ⟩
           kext fI (id I) (η j ∘D [ J ]₁ f) ∘D subst (λ X → Hom D (T fI a) (T X a)) (Category.right-id I) (kext fI (id I) (η j {a}))
             ≅⟨ hcong₂ (λ Y Z → kext Y (id I) (η j ∘D [ J ]₁ f) ∘D Z) 
                       (≡-to-≅ (sym $ Category.right-id I))
                       (≡-subst-removable (λ X → Hom D (T fI a) (T X a)) (Category.right-id I) (kext fI (id I) (η j {a}))) ⟩
           kext (id I ∘I fI) (id I) (η j ∘D [ J ]₁ f) ∘D kext fI (id I) (η j {a})
             ≅⟨ hcong₂ (λ X Y → kext X (id I) (η j ∘D [ J ]₁ f) ∘D Y) 
                       (≡-to-≅ (Category.right-id I)) 
                       (left-id fI) ⟩
           kext fI (id I) (η j ∘D [ J ]₁ f) ∘D id D
             ≅⟨ hcong (λ X → kext X (id I) (η j ∘D [ J ]₁ f) ∘D id D) (≡-to-≅ (sym (Category.right-id I))) ⟩
           kext (id I ∘I fI) (id I) (η j ∘D [ J ]₁ f) ∘D id D
             ≡⟨ Category.left-id D ⟩
           kext (id I ∘I fI) (id I) (η j ∘D [ J ]₁ f)
             ≅⟨ hcong (λ X → kext X (id I) (η j ∘D [ J ]₁ f)) (≡-to-≅ (Category.right-id I)) ⟩
           kext fI (id I) (η j ∘D [ J ]₁ f)
             ≡⟨ sym (Category.right-id D) ⟩
           id D {T (id I ∘I fI) b} ∘D kext fI (id I) (η j ∘D [ J ]₁ f)
             ≅⟨ hcong₂ (λ X Y → (Hom D (T fI a) (T X b)) ∋ (Y ∘D kext fI (id I) (η j ∘D [ J ]₁ f))) (≡-to-≅ (sym (Category.right-id I))) (hsym (left-id (id I ∘I fI))) ⟩
           kext (id I ∘I fI) (id I) (η j {b}) ∘D kext fI (id I) (η j ∘D [ J ]₁ f)
             ≅⟨ hcong₂ (λ Y Z → kext Y (id I) (η j {b}) ∘D Z) 
                       (≡-to-≅ (Category.right-id I))
                       (hsym (≡-subst-removable (λ X → Hom D (T fI a) (T X b)) (Category.right-id I) (kext fI (id I) (η j ∘D [ J ]₁ f)))) ⟩
           kext fI (id I) (η j {b}) ∘D subst (λ X → Hom D (T fI a) (T X b)) (Category.right-id I) (kext fI (id I) (η j ∘D [ J ]₁ f))
             ≅⟨ hcong₂ (λ Y Z → (Hom D (T fI b) (T Y b) ∋ Z) ∘D subst (λ X → Hom D (T fI a) (T X b)) (Category.right-id I) (kext fI (id I) (η j ∘D [ J ]₁ f))) 
                       (≡-to-≅ (Category.right-id I)) 
                       (hsym (≡-subst-removable (λ X → Hom D (T fI b) (T X b)) (Category.right-id I) (kext fI (id I) (η j {b})))) ⟩
           subst (λ X → Hom D (T fI b) (T X b)) (Category.right-id I) (kext fI (id I) (η j {b})) ∘D subst (λ X → Hom D (T fI a) (T X b)) (Category.right-id I) (kext fI (id I) (η j ∘D [ J ]₁ f))
             ≡⟨⟩
           nat-η b ∘D [ FunctorT fI ]₁ f ∎
