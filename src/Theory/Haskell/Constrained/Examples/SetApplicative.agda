
open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Level

open import Data.Unit hiding ( _≤_ ; _≟_ ; total )
open import Data.Empty
open import Data.List
open import Data.List.All
open import Data.Product hiding ( map )
open import Data.Sum hiding ( map )

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality using ( refl ; _≅_ ; ≡-to-≅ )
open import Relation.Binary using ( Decidable ; IsDecEquivalence ; IsEquivalence ; IsDecTotalOrder ; IsPreorder ; IsPartialOrder )
open ≡-Reasoning

open import Extensionality
open import Equality
open import ProofIrrelevance
open import Haskell hiding ( Type )
open import Haskell.Applicative using ( _***_ )

open import Theory.Category.Definition
open import Theory.Category.Dependent
open import Theory.Category.Monoidal
open import Theory.Category.Monoidal.Dependent
open import Theory.Category.Monoidal.Examples.SetCat renaming ( setMonoidalCategory to SetMonCat )
open import Theory.Category.Examples.SetCat renaming ( setCategory to SetCat )

open import Theory.Functor.Definition

open import Theory.Haskell.Constrained
open import Theory.Haskell.Constrained.Functor
open import Theory.Haskell.Constrained.Applicative

open import Theory.Haskell.Constrained.Examples.LSet.Base
open import Theory.Haskell.Constrained.Examples.LSet.Instances
open import Theory.Haskell.Constrained.Examples.LSet.Product
open import Theory.Haskell.Constrained.Examples.LSet.Map
open import Theory.Haskell.Constrained.Examples.LSet.Insert
open import Theory.Haskell.Constrained.Examples.LSet.Union
open import Theory.Haskell.Constrained.Examples.LSet.KleisliExtension
open import Theory.Haskell.Constrained.Examples.LSet.Ap
open import Theory.Haskell.Constrained.Examples.SetFunctor
open import Theory.Haskell.Constrained.Examples.SetMonad using ( kext-coher ; kext-right-id )

module Theory.Haskell.Constrained.Examples.SetApplicative {ℓ : Level} where 

open DependentCategory

open NotApplicativeReady

private
  SetMonCat' = SetMonCat {ℓ}
  SetCat' = SetCat {ℓ}

ObjTensor : {A B : Category.Obj SetCat'} 
          → DepObj ConstraintCategoryLSet A → DepObj ConstraintCategoryLSet B 
          → DepObj ConstraintCategoryLSet (A × B)
ObjTensor {A} {B} (OrdA , StructEqA) (OrdB , StructEqB) = OrdInstance-× OrdA OrdB , IsStructuralEquality-× OrdA OrdB StructEqA StructEqB

ConstraintMonoidalCategoryLSet : MonoidalConstraintCategory {ℓ} {suc ℓ}
ConstraintMonoidalCategoryLSet = record
  { DC = ConstraintCategoryLSet
  ; _Dep⊗₀_ = ObjTensor
  ; _Dep⊗₁_ = λ _ _ → tt
  ; depUnit = (Ord-⊤ , IsStructuralEquality-⊤)
  ; dep-tensor-id = refl
  ; dep-tensor-compose = refl
  ; dep-α = λ x' y' z' → tt
  ; dep-α-inv = λ x' y' z' → tt
  ; dep-λ = λ x' → tt
  ; dep-λ-inv = λ x' → tt
  ; dep-ρ = λ x' → tt
  ; dep-ρ-inv = λ x' → tt
  ; dep-α-natural = refl
  ; dep-λ-natural = refl
  ; dep-ρ-natural = refl
  ; dep-α-left-id = λ a' b' c' → refl
  ; dep-α-right-id = λ a' b' c' → refl
  ; dep-λ-left-id = λ a' → refl
  ; dep-λ-right-id = λ a' → refl
  ; dep-ρ-left-id = λ a' → refl
  ; dep-ρ-right-id = λ a' → refl
  ; dep-triangle-id = λ x' y' → refl
  ; dep-pentagon-id = λ w' x' y' z' → refl
  }


ApplicativeLSet : ConstrainedApplicative ConstraintMonoidalCategoryLSet
ApplicativeLSet = record
  { CtsFunctor = FunctorLSet
  ; unit = unit
  ; prod-map = ap'
  ; naturality = λ {a a' b b'} {f} {f'} → fun-ext (naturality {a} {a'} {b} {b'} {f} {f'})
  ; associativity = associativity
  ; left-unitality = left-unitality
  ; right-unitality = right-unitality
  } where
    open Functor (ConstrainedFunctor.CtFunctor FunctorLSet) renaming ( id to map-id ; compose to map-compose )
    open MonoidalCategory (DependentMonoidalCategory.DepMonCat ConstraintMonoidalCategoryLSet) renaming ( unit to Unit )

    set-α = MonoidalCategory.α SetMonCat'
    set-λ = MonoidalCategory.λ' SetMonCat'
    set-ρ = MonoidalCategory.ρ SetMonCat'
    
    ⊤-Obj : Obj
    ⊤-Obj = (Lift ⊤ , Ord-⊤ , IsStructuralEquality-⊤)
    
    tyOrd : Obj → Σ (Set ℓ) (OrdInstance {ℓ} {ℓ} {ℓ})
    tyOrd (A , OrdA , StructEqA) = A , OrdA

    ty : Obj → Set ℓ
    ty (A , _) = A
    
    ty-× : Obj → Obj → Set ℓ
    ty-× A B = ty A × ty B
    
    ord : (A : Obj) → OrdInstance {ℓ} {ℓ} {ℓ} (ty A)
    ord (_ , OrdA , _) = OrdA
    
    sEq : (A : Obj) → IsStructuralEquality (OrdInstance.eqInstance (ord A))
    sEq (_ , _ , StructEqA) = StructEqA
    
    ord-× : (A B : Obj) → OrdInstance {ℓ} {ℓ} {ℓ} (ty A × ty B)
    ord-× A B = OrdInstance-× (ord A) (ord B)
    
    sEq-× : (A B : Obj) → IsStructuralEquality (OrdInstance.eqInstance (ord-× A B))
    sEq-× A B = IsStructuralEquality-× (ord A) (ord B) (sEq A) (sEq B)

    tyOrd-× : Obj → Obj → Σ (Set ℓ) (OrdInstance {ℓ} {ℓ} {ℓ})
    tyOrd-× A B = (ty A × ty B) , (ord-× A B)
    
    ap' : (x y : Obj) → F₀ x × F₀ y → F₀ (x ⊗₀ y)
    ap' A B (sa , sb) = ap {A = tyOrd A} {tyOrd B} (sa , sb)
    
    all-× : Obj → Obj → Obj
    all-× A B = (ty A × ty B) , (ord-× A B) , sEq-× A B
    
    lset-× : Obj → Obj → Obj
    lset-× A B = LSet (tyOrd-× A B) , OrdLSet {A = tyOrd-× A B} , IsStructuralEquality-LSet (ord-× A B) (sEq-× A B)
    
    pure : (A : Obj) → ty A → LSet (tyOrd A)
    pure A a = singleton (tyOrd A) a
    
    unit : LSet (tyOrd Unit)
    unit = pure ⊤-Obj (lift tt) 
    
    abstract
      naturality : {a a' b b' : Obj}
                 → {f : Hom a b} {f' : Hom a' b'}
                 → (x : F₀ a × F₀ a')
                 → (F₁ {a ⊗₀ a'} {b ⊗₀ b'} (_⊗₁_ {a} {b} {a'} {b'} f f') ∘F ap' a a') x
                 ≡ (ap' b b' ∘F (λ x → F₁ {a} {b} f (proj₁ x) , F₁ {a'} {b'} f' (proj₂ x))) x
      naturality {A} {A'} {B} {B'} {f , tt} {f' , tt} (xs , ys) = begin
        (F₁ {A ⊗₀ A'} {B ⊗₀ B'} (_⊗₁_ {A} {B} {A'} {B'} (f , tt) (f' , tt)) ∘F ap' A A') (xs , ys)
          ≡⟨ refl ⟩
        mapSet {OrdA = ord-× A A'} {ord-× B B'} (f *** f') (ap' A A' (xs , ys))
          ≡⟨ refl ⟩
        mapSet {OrdA = ord-× A A'} {ord-× B B'} (f *** f') (kext (λ a → kext (λ b → pure (A ⊗₀ A') (a , b)) ys) xs)
          ≡⟨ sym (kext-map-eq (f *** f') (kext (λ a → kext (λ b → pure (A ⊗₀ A') (a , b)) ys) xs)) ⟩
        kext (pure (B ⊗₀ B') ∘F (f *** f')) (kext (λ a → kext (λ b → pure (A ⊗₀ A') (a , b)) ys) xs)
          ≡⟨ sym (kext-coher (λ a → kext (λ b → pure (A ⊗₀ A') (a , b)) ys) (pure (B ⊗₀ B') ∘F (f *** f')) xs (sEq-× A A') (sEq-× B B')) ⟩
        kext (kext (pure (B ⊗₀ B') ∘F (f *** f')) ∘F (λ a → kext (λ b → pure (A ⊗₀ A') (a , b)) ys)) xs
          ≡⟨ refl ⟩
        kext (λ a → kext (pure (B ⊗₀ B') ∘F (f *** f')) (kext (λ b → pure (A ⊗₀ A') (a , b)) ys)) xs
          ≡⟨ cong (λ X → kext X xs) (fun-ext p) ⟩
        kext (kext (λ a → kext (λ b → pure (B ⊗₀ B') (a , b)) (kext (pure B' ∘F f') ys)) ∘F (pure B ∘F f)) xs
          ≡⟨ kext-coher (pure B ∘F f) (λ a → kext (λ b → pure (B ⊗₀ B') (a , b)) (kext (pure B' ∘F f') ys)) xs (sEq B) (sEq-× B B') ⟩
        kext (λ a → kext (λ b → pure (B ⊗₀ B') (a , b)) (kext (pure B' ∘F f') ys)) (kext (pure B ∘F f) xs)
          ≡⟨ cong₂ (λ X Y → kext (λ a → kext (λ b → pure (B ⊗₀ B') (a , b)) X) Y) (kext-map-eq f' ys) (kext-map-eq f xs) ⟩
        kext (λ a → kext (λ b → pure (B ⊗₀ B') (a , b)) (mapSet {OrdA = ord A'} {ord B'} f' ys)) (mapSet {OrdA = ord A} {ord B} f xs)
          ≡⟨ refl ⟩
        ap' B B' (mapSet {OrdA = ord A} {ord B} f xs , mapSet {OrdA = ord A'} {ord B'} f' ys)
          ≡⟨ refl ⟩
        (ap' B B' ∘F (λ x → F₁ {A} {B} (f , tt) (proj₁ x) , F₁ {A'} {B'} (f' , tt) (proj₂ x))) (xs , ys) ∎
          where
            p : (a : ty A) 
              → kext (pure (B ⊗₀ B') ∘F (f *** f')) (kext (λ b → pure (A ⊗₀ A') (a , b)) ys)
              ≡ (kext (λ a → kext (λ b → pure (B ⊗₀ B') (a , b)) (kext (pure B' ∘F f') ys)) ∘F pure B ∘F f) a
            p a = begin
              kext (pure (B ⊗₀ B') ∘F (f *** f')) (kext (λ b → pure (A ⊗₀ A') (a , b)) ys)
                ≡⟨ kext-map-eq (f *** f') (kext (λ b → pure (A ⊗₀ A') (a , b)) ys) ⟩
              mapSet (f *** f') (kext (λ b → pure (A ⊗₀ A') (a , b)) ys)
                ≡⟨ cong (mapSet (f *** f')) (kext-map-eq (λ b → (a , b)) ys) ⟩
              mapSet (f *** f') (mapSet (λ b → (a , b)) ys)
                ≡⟨ cong (λ X → X ys) (sym (map-compose {a = A'} {all-× A A'} {all-× B B'} {(λ b → (a , b)) , tt} {f *** f' , tt})) ⟩
              mapSet ((f *** f') ∘F (λ b → (a , b))) ys
                ≡⟨ cong (λ X → X ys) (map-compose {a = A'} {B'} {all-× B B'} {f' , tt} {(λ b → (f a , b)) , tt} ) ⟩
              mapSet (λ b → (f a , b)) (mapSet f' ys)
                ≡⟨ cong (mapSet (λ b → (f a , b))) (sym (kext-map-eq f' ys)) ⟩
              mapSet (λ b → (f a , b)) (kext (pure B' ∘F f') ys)
                ≡⟨ sym (kext-map-eq (λ b → (f a , b)) (kext (pure B' ∘F f') ys)) ⟩
              kext (λ b → pure (B ⊗₀ B') (f a , b)) (kext (pure B' ∘F f') ys)
                ≡⟨ sym (kext-right-id {OrdA = ord B} (λ a → kext (λ b → pure (B ⊗₀ B') (a , b)) (kext (pure B' ∘F f') ys)) (f a)) ⟩
              kext (λ a → kext (λ b → pure (B ⊗₀ B') (a , b)) (kext (pure B' ∘F f') ys)) (pure B (f a)) ∎

    abstract
      kext-compose : (A B C : Obj)
                   → (f : ty A → ty B) (g : ty B → ty C) 
                   → (z : LSet (tyOrd A))
                   → kext (pure C ∘F g) (kext (pure B ∘F f) z) ≡ kext (pure C ∘F (g ∘F f)) z
      kext-compose A B C f g z = begin
        kext (pure C ∘F g) (kext (pure B ∘F f) z) 
          ≡⟨ kext-map-eq g (kext (pure B ∘F f) z) ⟩ 
        mapSet g (kext (pure B ∘F f) z) 
          ≡⟨ cong (mapSet g) (kext-map-eq f z) ⟩ 
        mapSet g (mapSet f z) 
          ≡⟨ sym (cong (λ X → X z) (map-compose {a = A} {B} {C} {f , tt} {g , tt})) ⟩ 
        mapSet (g ∘F f) z 
          ≡⟨ sym (kext-map-eq (g ∘F f) z) ⟩ 
        kext (pure C ∘F (g ∘F f)) z ∎
    
    abstract
      associativity : (x y z : Obj) 
                    → F₁ {(x ⊗₀ y) ⊗₀ z} {x ⊗₀ (y ⊗₀ z)} (α x y z) ∘F (ap' (x ⊗₀ y) z ∘F (λ a → ap' x y (proj₁ a) , proj₂ a))
                    ≡ ap' x (y ⊗₀ z) ∘F ((λ a → proj₁ a , ap' y z (proj₂ a)) ∘F set-α (F₀ x) (F₀ y) (F₀ z))
      associativity A B C = fun-ext $ λ { ((x , y) , z) → begin
        (F₁ {(A ⊗₀ B) ⊗₀ C} {A ⊗₀ (B ⊗₀ C)} (α A B C) ∘F (ap' (A ⊗₀ B) C ∘F (λ a → ap' A B (proj₁ a) , proj₂ a))) ((x , y) , z)
          ≡⟨ refl ⟩
        mapSet (λ { ((a , b) , c) → (a , (b , c)) }) (kext (λ a → kext (λ b → pure (all-× (all-× A B) C) (a , b)) z) (kext (λ a → kext (λ b → pure (all-× A B) (a , b)) y) x ) )
          ≡⟨ sym (kext-map-eq (λ { ((a , b) , c) → (a , (b , c)) }) (kext (λ a → kext (λ b → pure (all-× (all-× A B) C) (a , b)) z) (kext (λ a → kext (λ b → pure (all-× A B) (a , b)) y) x ))) ⟩
        kext (pure (all-× A (all-× B C)) ∘F (λ { ((a , b) , c) → (a , (b , c)) })) (kext (λ a → kext (λ b → pure (all-× (all-× A B) C) (a , b)) z) (kext (λ a → kext (λ b → pure (all-× A B) (a , b)) y) x ) )
          ≡⟨ sym (kext-coher (λ a → kext (λ b → pure (all-× (all-× A B) C) (a , b)) z) 
                             (pure (all-× A (all-× B C)) ∘F (λ { ((a , b) , c) → (a , (b , c)) })) 
                             ((kext (λ a → kext (λ b → pure (all-× A B) (a , b)) y) x )) 
                             (sEq (all-× (all-× A B) C)) (sEq (all-× A (all-× B C)))) ⟩
        kext (kext (pure (all-× A (all-× B C)) ∘F (λ { ((a , b) , c) → (a , (b , c)) })) ∘F (λ a → kext (λ b → pure (all-× (all-× A B) C) (a , b)) z)) (kext (λ a → kext (λ b → pure (all-× A B) (a , b)) y) x )
          ≡⟨ refl ⟩
        kext (λ a → kext (pure (all-× A (all-× B C)) ∘F (λ { ((a , b) , c) → (a , (b , c)) })) (kext (λ b → pure (all-× (all-× A B) C) (a , b)) z)) (kext (λ a → kext (λ b → pure (all-× A B) (a , b)) y) x )
          ≡⟨ cong (λ X → kext X (kext (λ a → kext (λ b → pure (all-× A B) (a , b)) y) x)) 
                  (fun-ext $ λ a → kext-compose C (all-× (all-× A B) C) (all-× A (all-× B C)) (λ b → (a , b)) (λ { ((v , u) , w) → (v , (u , w)) }) z) ⟩
        kext (λ a → kext (pure (all-× A (all-× B C)) ∘F ((λ { ((v , u) , w) → (v , (u , w)) }) ∘F (λ b → (a , b)))) z) (kext (λ a → kext (λ b → pure (all-× A B) (a , b)) y) x )
          ≡⟨ sym $ kext-coher (λ a → kext (λ b → pure (all-× A B) (a , b)) y) 
                              (λ a → kext (pure (all-× A (all-× B C)) ∘F ((λ { ((v , u) , w) → (v , (u , w)) }) ∘F (λ b → (a , b)))) z)
                              x (sEq (all-× A B)) (sEq (all-× A (all-× B C))) ⟩
        kext (λ a → kext (λ c → kext (pure (all-× A (all-× B C)) ∘F ((λ { ((v , u) , w) → (v , (u , w)) }) ∘F (λ b → (c , b)))) z) (kext (λ b → pure (all-× A B) (a , b)) y)) x
          ≡⟨ cong (λ X → kext X x) (fun-ext (λ a → sym (kext-coher ((λ b → pure (all-× A B) (a , b))) 
                                                                   ((λ c → kext (pure (all-× A (all-× B C)) ∘F ((λ { ((v , u) , w) → (v , (u , w)) }) ∘F (λ b → (c , b)))) z)) 
                                                                   y (sEq (all-× A B)) (sEq (all-× A (all-× B C)))))) ⟩
        kext (λ a → kext (λ b → kext (λ c → kext (pure (all-× A (all-× B C)) ∘F ((λ { ((v , u) , w) → (v , (u , w)) }) ∘F (λ b → (c , b)))) z) (pure (all-× A B) (a , b))) y) x
          ≡⟨ (cong (λ X → kext X x) $ fun-ext $ λ a → cong (λ X → kext X y) 
                                    $ fun-ext $ λ b → kext-right-id {OrdA = ord-× A B} (λ c → kext (pure (all-× A (all-× B C)) ∘F ((λ { ((v , u) , w) → (v , (u , w)) }) ∘F (λ b → (c , b)))) z) (a , b) ) ⟩
        kext (λ a → kext (λ b → (λ c → kext (pure (all-× A (all-× B C)) ∘F ((λ { ((v , u) , w) → (v , (u , w)) }) ∘F (λ b → (c , b)))) z) (a , b)) y) x
          ≡⟨ refl ⟩
        kext (λ a → kext (λ c → kext (pure (all-× A (all-× B C)) ∘F ((λ b → (a , b)) ∘F (λ d → (c , d)))) z) y ) x
          ≡⟨ cong (λ X → kext X x) (fun-ext (λ a → cong (λ X → kext X y) (fun-ext (λ c → sym (kext-compose C (all-× B C) (all-× A (all-× B C)) (λ d → (c , d)) (λ b → (a , b)) z))))) ⟩
        kext (λ a → kext (λ c → kext (λ b → pure (all-× A (all-× B C)) (a , b)) (kext {OrdA = ord C} (λ d → pure (all-× B C) (c , d)) z)) y ) x
          ≡⟨ cong (λ X → kext X x) (fun-ext (λ a → kext-coher (λ a → kext {OrdA = ord C} (λ b → pure (all-× B C) (a , b)) z) (λ b → pure (all-× A (all-× B C)) (a , b)) y (sEq-× B C) (sEq (all-× A (all-× B C))))) ⟩
        kext (λ a → kext (λ b → pure (all-× A (all-× B C)) (a , b)) (kext {OrdA = ord B} (λ a → kext {OrdA = ord C} (λ b → pure (all-× B C) (a , b)) z) y) ) x
          ≡⟨ refl ⟩
        (ap' A (B ⊗₀ C) ∘F ((λ a → proj₁ a , ap' B C (proj₂ a)) ∘F set-α (F₀ A) (F₀ B) (F₀ C))) ((x , y) , z) ∎ }
    
    abstract
      left-unitality : (A : Obj)
                     → set-λ (F₀ A)
                     ≡ F₁ {Unit ⊗₀ A} {A} (λ' A) ∘F (ap' Unit A ∘F (λ a → unit , proj₂ a))
      left-unitality A = fun-ext $ λ {x → begin
        set-λ (F₀ A) x
          ≡⟨ refl ⟩ 
        proj₂ x
          ≡⟨ cong (λ X → X (proj₂ x)) (sym $ map-id {a = A}) ⟩ 
        mapSet {OrdA = ord A} (proj₂ {a = ℓ} ∘F (λ b → (lift tt , b))) (proj₂ x)
          ≡⟨ cong (λ X → X (proj₂ x)) (map-compose {a = A} {all-× Unit A} {A} {(λ b → (lift tt , b)) , tt} {proj₂ , tt}) ⟩ 
        mapSet {OrdA = ord-× Unit A} proj₂ (mapSet (λ b → (lift tt , b)) (proj₂ x))
          ≡⟨ cong (mapSet {OrdA = ord-× Unit A} proj₂) (sym $ union-with-empty (mapSet (λ b → (lift tt , b)) (proj₂ x))) ⟩ 
        mapSet {OrdA = ord-× Unit A} proj₂ (union (mapSet (λ b → (lift tt , b)) (proj₂ x)) (empty (tyOrd-× Unit A)))
          ≡⟨ cong (λ X → mapSet {OrdA = ord-× Unit A} proj₂ (union X (empty (tyOrd-× Unit A)))) (sym (kext-map-eq (λ b → (lift tt , b)) (proj₂ x))) ⟩
        mapSet {OrdA = ord-× Unit A} proj₂ (union (kext (λ b → pure (all-× Unit A) (lift tt , b)) (proj₂ x)) (empty (tyOrd-× Unit A)))
          ≡⟨ refl ⟩ 
        mapSet {OrdA = ord-× Unit A} proj₂ (kext (λ a → kext (λ b → pure (all-× Unit A) (a , b)) (proj₂ x) ) unit)
          ≡⟨ refl ⟩ 
        F₁ {Unit ⊗₀ A} {A} (λ' A) (ap' Unit A (unit , proj₂ x)) ∎ }
    
    abstract
      right-unitality : (A : Obj) 
                      → set-ρ (F₀ A)
                      ≡ F₁ {A ⊗₀ Unit} {A} (ρ A) ∘F (ap' A Unit ∘F (λ a → proj₁ a , unit))
      right-unitality A = fun-ext $ λ x → begin
        set-ρ (F₀ A) x
          ≡⟨ refl ⟩
        proj₁ x
          ≡⟨ cong (λ X → X (proj₁ x)) (sym (map-id {a = A})) ⟩
        mapSet {OrdA = ord A} (λ a → proj₁ {b = ℓ} (a , lift tt)) (proj₁ x)
          ≡⟨ cong (λ X → X (proj₁ x)) (map-compose {a = A} {all-× A Unit} {A} {(λ a → (a , lift tt)) , tt} {proj₁ , tt})  ⟩
        mapSet {OrdA = ord-× A Unit} proj₁ (mapSet (λ a → (a , lift tt)) (proj₁ x))
          ≡⟨ cong (mapSet {OrdA = ord-× A Unit} proj₁) (sym $ kext-map-eq (λ a → (a , lift tt)) (proj₁ x)) ⟩
        mapSet {OrdA = ord-× A Unit} proj₁ (kext (λ a → pure (all-× A Unit) (a , lift tt)) (proj₁ x))
          ≡⟨ refl ⟩
        mapSet {OrdA = ord-× A Unit} proj₁ (kext (λ a → kext (λ b → pure (all-× A Unit) (a , b)) unit) (proj₁ x))
          ≡⟨ refl ⟩
        F₁ {A ⊗₀ Unit} {A} (ρ A) (ap' A Unit (proj₁ x , unit)) ∎

