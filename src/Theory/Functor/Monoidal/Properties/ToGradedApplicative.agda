 
open import Level
open import Function hiding ( id ) renaming ( _∘_ to _∘F_ )

open import Data.Unit
open import Data.Product

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( sym to hsym ; trans to htrans ; cong to hcong ; cong₂ to hcong₂ )
open ≡-Reasoning hiding ( _≅⟨_⟩_ )
open ≅-Reasoning hiding ( _≡⟨_⟩_ ) renaming ( begin_ to hbegin_ ; _∎ to _∎h )

open import Haskell hiding ( Hask )
open import Haskell.Functor renaming ( Functor to HaskellFunctor )
open import Haskell.Applicative using ( _***_ )
open import Haskell.Parameterized.Graded.Applicative

open import Theory.Monoid
open import Theory.Category.Definition
open import Theory.Category.Examples.Discrete
open import Theory.Category.Examples.SetCat
open import Theory.Category.Monoidal
open import Theory.Category.Monoidal.Product
open import Theory.Category.Monoidal.Examples.SetCat
open import Theory.Category.Monoidal.Examples.Monoid
open import Theory.Functor.Definition
open import Theory.Functor.Monoidal
open import Theory.Functor.Composition
open import Theory.Natural.Transformation

module Theory.Functor.Monoidal.Properties.ToGradedApplicative where

open LaxMonoidalFunctor renaming ( ε to ε' ; F to F' )
open MonoidalCategory renaming ( unit to unit' ; α to ass ) hiding ( left-id ; right-id ; assoc )
open NaturalTransformation renaming ( η to nat-η )

MonoidalFunctor→GradedApplicative : {ℓ : Level} {M : Set ℓ} {mon : Monoid M}
                                  → (FMon : LaxMonoidalFunctor (monoidMonoidalCategory mon ×CMon setMonoidalCategory {zero}) (setMonoidalCategory {zero}))
                                  → GradedApplicative mon (λ i α → F₀ FMon (i , α))
MonoidalFunctor→GradedApplicative {ℓ} {M} {mon} FMon = graded-applicative pure _<*>_ fun law-id law-composition law-homomorphism law-interchange law-applicative-fmap
  where
    open Monoid mon

    MonMonCat = monoidMonoidalCategory mon
    MonCat = discreteCategory M
    
    SetMonCat = setMonoidalCategory {zero}
    SetCat = setCategory {zero}
    
    F : M → TyCon
    F i α = F₀ FMon (i , α)

    fmap : {i : M} {α β : Type} → (α → β) → F i α → F i β
    fmap {i} {α} {β} f ma = F₁ FMon (refl , f) ma

    unit : F ε (Lift ⊤)
    unit = ε' FMon (lift tt)
    
    _**_ : {i j : M} {α β : Type} → F i α → F j β → F (i ∙ j) (α × β)
    _**_ {i} {j} {α} {β} a b = μ FMon (i , α) (j , β) (a , b)
    
    pure : {α : Type} → α → F ε α
    pure a = fmap (λ _ → a) unit

    _<*>_ : {i j : M} {α β : Type} → F i (α → β) → F j α → F (i ∙ j) β
    _<*>_ mf ma = fmap (λ {(f , a) → f a}) (mf ** ma)

    fun : (i : M) → HaskellFunctor (F i)
    fun i = functor fmap (λ {α} → LaxMonoidalFunctor.id FMon)
                         (λ {α β γ} f g → LaxMonoidalFunctor.compose FMon {f = refl , g} {refl , f})
    
    abstract
      law-naturality : {i j k l : M} {α β γ δ : Type}
                     → (p : i ≡ j) (q : k ≡ l)
                     → (f : α → β) (g : γ → δ) (u : F i α) (v : F k γ) 
                     → fmap (f *** g) (u ** v) ≡ fmap f u ** fmap g v
      law-naturality {i} {j} {k} {l} {α} {β} {γ} {δ} refl refl f g u v = begin
        ( ([ F' FMon  ]₁ ([ MonoidalCategory.tensor MonMonCat ]₁ (refl , refl) , f *** g)) ∘F (μ FMon (i , α) (k , γ)) ) (u , v)
          ≡⟨ cong (λ X → X (u , v)) (NaturalTransformation.natural (LaxMonoidalFunctor.μ-natural-transformation FMon) {f = ((refl , f) , (refl , g))}) ⟩
       μ FMon (j , β) (l , δ) (F₁ FMon (refl , f) u , F₁ FMon (refl , g) v) ∎

    abstract
      het-proof-irr : {i j : M} → (p : i ≡ j) → _≅_ {A = i ≡ i} refl p
      het-proof-irr {i} {.i} refl = refl
    
    abstract
      law-left-identity' : {i : M} {α : Type} → (v : F i α) 
                         → fmap proj₂ (unit ** v) ≅ v
      law-left-identity' {i} {α} v = hbegin
        (F (ε ∙ i) α ∋ (F₁ FMon (refl , proj₂) ∘F μ FMon (ε , Lift ⊤) (i , α) ∘F (ε' FMon *** (λ x → x)) ) (lift tt , v))
          ≅⟨ hcong₂ (λ X Y → F X α ∋ (F₁ FMon (Y , proj₂) ∘F μ FMon (ε , Lift ⊤) (i , α) ∘F (ε' FMon *** (λ x → x)) ) (lift tt , v)) (≡-to-≅ left-id) (het-proof-irr left-id) ⟩
        (F i α ∋ (F₁ FMon (left-id , proj₂) ∘F μ FMon (ε , Lift ⊤) (i , α) ∘F (ε' FMon *** (λ x → x)) ) (lift tt , v))
          ≅⟨ hcong (λ X → X (lift tt , v)) (hsym (≡-to-≅ $ left-unitality FMon (i , α))) ⟩
        (F i α ∋ proj₂ {a = zero} (lift tt , v))
          ≅⟨ refl ⟩
        (F i α ∋ v) ∎h
    
    abstract
      law-left-identity : {i : M} {α : Type} → (v : F i α) 
                        → (unit ** v) ≅ fmap (λ a → (lift tt , a)) v
      law-left-identity {i} {α} v = hbegin
        (μ FMon (ε , Lift ⊤) (i , α) ∘F (ε' FMon *** (λ x → x))) (lift tt , v)
          ≅⟨ hcong (λ X → (X ∘F μ FMon (ε , Lift ⊤) (i , α) ∘F (ε' FMon *** (λ x → x))) (lift tt , v)) (hsym (≡-to-≅ $ Functor.id (F' FMon))) ⟩
        (F₁ FMon (refl , (λ x → x)) ∘F μ FMon (ε , Lift ⊤) (i , α) ∘F (ε' FMon *** (λ x → x))) (lift tt , v)
          ≅⟨ refl ⟩
        (F₁ FMon (refl , ((λ a → (lift tt , a)) ∘F proj₂)) ∘F μ FMon ( , Lift ⊤) (i , α) ∘F (ε' FMon *** (λ x → x))) (lift tt , v)
          ≅⟨ hcong (λ X → (X ∘F μ FMon (ε , Lift ⊤) (i , α) ∘F (ε' FMon *** (λ x → x))) (lift tt , v)) (≡-to-≅ $ Functor.compose (F' FMon)) ⟩
        (F₁ FMon (refl , (λ a → (lift tt , a))) ∘F F₁ FMon (refl , proj₂) ∘F μ FMon (ε , Lift ⊤) (i , α) ∘F (ε' FMon *** (λ x → x))) (lift tt , v)
          ≅⟨ hcong₂ (λ X Y → F X (Lift ⊤ × α) ∋ fmap (λ a → (lift tt , a)) Y) (≡-to-≅ left-id) (law-left-identity' v) ⟩
        fmap (λ a → (lift tt , a)) v ∎h

    abstract
      law-right-identity' : {i : M} {α : Type} → (v : F i α) 
                          → fmap proj₁ (v ** unit) ≅ v
      law-right-identity' {i} {α} v = hbegin
        (F (i ∙ ε) α ∋ (F₁ FMon (refl , proj₁) ∘F μ FMon (i , α) (ε , Lift ⊤) ∘F ((λ x → x) *** ε' FMon) ) (v , lift tt))
          ≅⟨ hcong₂ (λ X Y → F X α ∋ (F₁ FMon (Y , proj₁) ∘F μ FMon (i , α) (ε , Lift ⊤) ∘F ((λ x → x) *** ε' FMon) ) (v , lift tt)) (≡-to-≅ right-id) (het-proof-irr right-id) ⟩
        (F i α ∋ (F₁ FMon (right-id , proj₁) ∘F μ FMon (i , α) (ε , Lift ⊤) ∘F ((λ x → x) *** ε' FMon) ) (v , lift tt))
          ≅⟨ hcong (λ X → X (v , lift tt)) (hsym (≡-to-≅ $ right-unitality FMon (i , α))) ⟩
        (F i α ∋ proj₁ {a = zero} {b = zero} (v , lift tt))
          ≅⟨ refl ⟩
        (F i α ∋ v) ∎h
    
    abstract
      law-right-identity : {i : M} {α : Type} → (v : F i α) 
                          → (v ** unit) ≅ fmap (λ a → (a , lift tt)) v
      law-right-identity {i} {α} v = hbegin
        (μ FMon (i , α) (ε , Lift ⊤) ∘F ((λ x → x) *** ε' FMon)) (v , lift tt)
          ≅⟨ hcong (λ X → (X ∘F μ FMon (i , α) (ε , Lift ⊤) ∘F ((λ x → x) *** ε' FMon)) (v , lift tt)) (hsym (≡-to-≅ $ Functor.id (F' FMon))) ⟩
        (F₁ FMon (refl , (λ x → x)) ∘F μ FMon (i , α) (ε , Lift ⊤) ∘F ((λ x → x) *** ε' FMon)) (v , lift tt)
          ≅⟨ refl ⟩
        (F₁ FMon (refl , ((λ a → (a , lift tt)) ∘F proj₁)) ∘F μ FMon (i , α) (ε , Lift ⊤) ∘F ((λ x → x) *** ε' FMon)) (v , lift tt)
          ≅⟨ hcong (λ X → (X ∘F μ FMon (i , α) (ε , Lift ⊤) ∘F ((λ x → x) *** ε' FMon)) (v , lift tt)) (≡-to-≅ $ Functor.compose (F' FMon)) ⟩
        (F₁ FMon (refl , (λ a → (a , lift tt))) ∘F F₁ FMon (refl , proj₁) ∘F μ FMon (i , α) (ε , Lift ⊤) ∘F ((λ x → x) *** ε' FMon)) (v , lift tt)
          ≅⟨ hcong₂ (λ X Y → F X (α × Lift ⊤) ∋ fmap (λ a → (a , lift tt)) Y) (≡-to-≅ right-id) (law-right-identity' v) ⟩
        fmap (λ a → (a , lift tt)) v ∎h

    abstract
      law-applicative-fmap : {i : M} {α β : Type} 
                           → (f : α → β) → (x : F i α) 
                           → fmap f x ≅ pure f <*> x
      law-applicative-fmap {i} {α} {β} f x = hbegin
        fmap f x 
          ≅⟨ refl ⟩
        fmap ((λ x → f (proj₂ {a = zero} x)) ∘F (λ a → (lift tt , a))) x
          ≅⟨ hcong (λ X → X x) (≡-to-≅ $ Functor.compose (F' FMon)) ⟩
        fmap (λ x → f (proj₂ x)) (fmap (λ a → (lift tt , a)) x)
          ≅⟨ hcong₂ (λ X Y → F X β ∋ fmap (λ x₁ → f (proj₂ x₁)) Y) (≡-to-≅ (sym left-id)) (hsym $ law-left-identity x) ⟩
        fmap (λ x → f (proj₂ x)) (unit ** x)
          ≅⟨ refl ⟩
        fmap ( (λ {(f , a) → f a}) ∘F ((λ _ → f) *** (λ x → x)) ) (ε' FMon (lift tt) ** x)
          ≅⟨ hcong (λ X → X (ε' FMon (lift tt) ** x)) (≡-to-≅ $ Functor.compose (F' FMon)) ⟩
        fmap (λ {(f , a) → f a}) (fmap ((λ _ → f) *** (λ x → x)) (ε' FMon (lift tt) ** x))
          ≅⟨ hcong (λ X → fmap (λ {(f , a) → f a }) X) (≡-to-≅ $ law-naturality (sym left-id) (sym left-id) (λ _ → f) (λ z → z) (ε' FMon (lift tt)) x) ⟩
        fmap (λ {(f , a) → f a}) ((fmap (λ _ → f) (ε' FMon (lift tt))) ** fmap (λ x → x) x)
          ≅⟨ hcong (λ X → fmap (λ {(f , a) → f a}) ((fmap (λ _ → f) (ε' FMon (lift tt))) ** X)) (hcong (λ X → X x) (≡-to-≅ $ Functor.id (F' FMon))) ⟩
        fmap (λ {(f , a) → f a}) ((fmap (λ _ → f) (ε' FMon (lift tt))) ** x) ∎h
    
    abstract
      law-id : {i : M} {α : Type} 
             → (v : F i α) 
             → (pure (λ x → x) <*> v) ≅ v
      law-id {i} {α} v = hbegin
        (pure (λ x → x) <*> v)
          ≅⟨ hsym $ law-applicative-fmap (λ x → x) v ⟩
        fmap (λ x → x) v
          ≅⟨ hcong (λ X → X v) (≡-to-≅ $ Functor.id (F' FMon)) ⟩
        v ∎h
    
    abstract
      law-associativity : {i j k : M} {α β γ : Type} → (u : F i α) (v : F j β) (w : F k γ) 
                        → u ** (v ** w) ≅ fmap (λ {((a , b) , c) → (a , (b , c))}) ( (u ** v) ** w ) 
      law-associativity {i} {j} {k} {α} {β} {γ} u v w = hbegin
        (F (i ∙ (j ∙ k)) (α × (β × γ)) ∋ (μ FMon (i , α) ((j ∙ k) , (β × γ)) ∘F ((λ x → x) *** μ FMon (j , β) (k , γ))) (u , (v , w))) 
          ≅⟨ hsym $ ≡-to-≅ $ cong (λ X → X ((u , v) , w)) (assoc FMon (i , α) (j , β) (k , γ)) ⟩
        (F (i ∙ (j ∙ k)) (α × (β × γ)) ∋ ((F₁ FMon (ass (MonMonCat ×CMon SetMonCat) (i , α) (j , β) (k , γ))
                                              ∘F ((μ FMon ((i ∙ j) , (α × β)) (k , γ))
                                              ∘F (μ FMon (i , α) (j , β) *** (λ x → x)))) ((u , v) , w)))
          ≅⟨ hcong₂ (λ X Y → F X (α × (β × γ)) ∋ ((F₁ FMon (Y , λ {((a , b) , c) → (a , (b , c))})
                                                      ∘F ((μ FMon ((i ∙ j) , (α × β)) (k , γ))
                                                      ∘F (μ FMon (i , α) (j , β) *** (λ x → x)))) ((u , v) , w)))
                    (≡-to-≅ $ Monoid.assoc mon)
                    (hsym $ het-proof-irr (sym $ Monoid.assoc mon)) ⟩
        (F ((i ∙ j) ∙ k) (α × (β × γ)) ∋ (F₁ FMon (refl , λ {((a , b) , c) → (a , (b , c))}) ∘F μ FMon ((i ∙ j) , (α × β)) (k , γ) ∘F (μ FMon (i , α) (j , β) *** (λ x → x))) ((u , v) , w)) ∎h

    abstract
      law-homomorphism : {α β : Type} 
                       → (x : α) → (f : α → β) 
                       → pure f <*> pure x ≅ pure (f x)
      law-homomorphism {α} {β} x f = hbegin
        fmap (λ {(f , a) → f a}) (fmap (λ _ → f) unit ** fmap (λ _ → x) unit)
          ≅⟨ hcong (fmap (λ {(f , a) → f a})) (≡-to-≅ $ sym $ law-naturality refl refl (λ _ → f) (λ _ → x) unit unit) ⟩
        fmap (λ {(f , a) → f a}) (fmap ((λ _ → f) *** (λ _ → x)) (unit ** unit))
          ≅⟨ hcong (λ X → X (unit ** unit)) (≡-to-≅ $ sym $ Functor.compose (F' FMon)) ⟩
        fmap ((λ {(f , a) → f a}) ∘F ((λ _ → f) *** (λ _ → x))) (unit ** unit)
          ≅⟨ hcong₂ (λ X Y → F X β ∋ fmap ((λ {(f , a) → f a}) ∘F ((λ _ → f) *** (λ _ → x))) Y) (≡-to-≅ left-id) (law-left-identity unit) ⟩
        fmap ((λ {(f , a) → f a}) ∘F ((λ _ → f) *** (λ _ → x))) (fmap (λ a → (lift tt , a)) unit)
          ≅⟨ hcong (λ X → X unit) (≡-to-≅ $ sym $ Functor.compose (F' FMon)) ⟩
        fmap (λ _ → f x) unit ∎h

    abstract
      law-interchange : {i : M} {α β : Type} 
                      → (u : F i (α → β)) → (x : α) 
                      → (u <*> pure x) ≅ (pure (λ f → f x) <*> u)
      law-interchange {i} {α} {β} u x = hbegin
        fmap (λ {(f , a) → f a}) (u ** fmap (λ _ → x) unit)
          ≅⟨ hcong (λ X → fmap (λ {(f , a) → f a}) (X u ** fmap (λ _ → x) unit)) (≡-to-≅ $ sym $ Functor.id (F' FMon)) ⟩
        fmap (λ {(f , a) → f a}) (fmap (λ x → x) u ** fmap (λ _ → x) unit)
          ≅⟨ hcong (fmap (λ {(f , a) → f a})) (≡-to-≅ $ sym $ law-naturality refl refl (λ x → x) (λ _ → x) u unit) ⟩
        fmap (λ {(f , a) → f a}) (fmap ((λ x → x) *** (λ _ → x)) (u ** unit))
          ≅⟨ hcong (λ X → X (u ** unit)) (≡-to-≅ $ sym $ Functor.compose (F' FMon)) ⟩
        fmap ((λ {(f , a) → f a}) ∘F ((λ x → x) *** (λ _ → x))) (u ** unit)
          ≅⟨ hcong₂ (λ X Y → F X β ∋ (fmap ((λ {(f , a) → f a}) ∘F ((λ x → x) *** (λ _ → x))) Y)) (≡-to-≅ right-id) (law-right-identity u) ⟩
        fmap ((λ {(f , a) → f a}) ∘F ((λ x → x) *** (λ _ → x))) (fmap (λ a → (a , lift tt)) u)
          ≅⟨ hcong (λ X → X u) (≡-to-≅ $ sym $ Functor.compose (F' FMon)) ⟩
        fmap ((λ {(f , a) → f a}) ∘F ((λ _ → (λ f → f x)) *** (λ x → x)) ∘F (λ a → (lift tt , a))) u 
          ≅⟨ hcong (λ X → X u) (≡-to-≅ $ Functor.compose (F' FMon)) ⟩
        fmap ((λ {(f , a) → f a}) ∘F ((λ _ → (λ f → f x)) *** (λ x → x))) (fmap (λ a → (lift tt , a)) u)
          ≅⟨ hcong₂ (λ X Y → F X β ∋ (fmap ((λ {(f , a) → f a}) ∘F ((λ _ → (λ f → f x)) *** (λ x → x))) Y)) (hsym (≡-to-≅ left-id)) (hsym $ law-left-identity u) ⟩
        fmap ((λ {(f , a) → f a}) ∘F ((λ _ → (λ f → f x)) *** (λ x → x))) (unit ** u)
          ≅⟨ hcong (λ X → X (unit ** u)) (≡-to-≅ $ Functor.compose (F' FMon)) ⟩
        fmap (λ {(f , a) → f a}) (fmap ((λ _ → (λ f → f x)) *** (λ x → x)) (unit ** u))
          ≅⟨ hcong (fmap (λ {(f , a) → f a})) (≡-to-≅ $ law-naturality refl refl (λ _ f → f x) (λ x → x) unit u) ⟩
        fmap (λ {(f , a) → f a}) (fmap (λ _ → (λ f → f x)) unit ** fmap (λ x → x) u)
          ≅⟨ hcong (λ X → fmap (λ {(f , a) → f a}) (fmap (λ _ → (λ f → f x)) unit ** X u)) (≡-to-≅ $ Functor.id (F' FMon)) ⟩
        fmap (λ {(f , a) → f a}) (fmap (λ _ → (λ f → f x)) unit ** u) ∎h

    abstract
      law-composition : {i j k : M} {α β γ : Type} 
                      → (u : F i (β → γ)) (v : F j (α → β)) (w : F k α)
                      → (((pure _∘′_ <*> u) <*> v) <*> w) ≅ (u <*> (v <*> w))
      law-composition {i} {j} {k} {α} {β} {γ} u v w = hbegin
        fmap (λ {(f , a) → f a}) (fmap (λ {(f , a) → f a}) ((fmap (λ {(f , a) → f a}) (fmap (λ _ → _∘′_) unit ** u)) ** v) ** w) 
          ≅⟨ hcong (λ X → fmap (λ {(f , a) → f a}) (fmap (λ {(f , a) → f a}) ((fmap (λ {(f , a) → f a}) (fmap (λ _ → _∘′_) unit ** X u)) ** v) ** w)) (≡-to-≅ $ sym $ Functor.id (F' FMon)) ⟩
        fmap (λ {(f , a) → f a}) (fmap (λ {(f , a) → f a}) ((fmap (λ {(f , a) → f a}) (fmap (λ _ → _∘′_) unit ** fmap (λ x → x) u)) ** v) ** w) 
          ≅⟨ hcong (λ X → fmap (λ { (f , a) → f a }) (fmap (λ { (f , a) → f a }) (fmap (λ { (f , a) → f a }) X ** v) ** w))
                  (≡-to-≅ $ sym $ law-naturality refl refl (λ _ → _∘′_) (λ x → x) unit u) ⟩
        fmap (λ {(f , a) → f a}) (fmap (λ {(f , a) → f a}) ((fmap (λ {(f , a) → f a}) (fmap ((λ _ → _∘′_) *** (λ x → x)) (unit ** u))) ** v) ** w) 
          ≅⟨ hcong₂ (λ X Y → F ((X ∙ j) ∙ k) γ ∋ (fmap (λ {(f , a) → f a}) (fmap (λ {(f , a) → f a}) ((fmap (λ {(f , a) → f a}) (fmap ((λ _ → _∘′_) *** (λ x → x)) Y)) ** v) ** w)) )
                    (≡-to-≅ left-id)
                    (law-left-identity u) ⟩
        fmap (λ {(f , a) → f a}) (fmap (λ {(f , a) → f a}) ((fmap (λ {(f , a) → f a}) (fmap ((λ _ → _∘′_) *** (λ x → x)) (fmap (λ a → (lift tt , a)) u))) ** v) ** w) 
          ≅⟨ hcong (λ X → fmap (λ {(f , a) → f a}) (fmap (λ {(f , a) → f a}) ((X (fmap (λ a → (lift tt , a)) u)) ** v) ** w)) (≡-to-≅ $ sym $ Functor.compose (F' FMon)) ⟩
        fmap (λ {(f , a) → f a}) (fmap (λ {(f , a) → f a}) ((fmap ((λ {(f , a) → f a}) ∘F ((λ _ → _∘′_) *** (λ x → x))) (fmap (λ a → (lift tt , a)) u)) ** v) ** w)
          ≅⟨ hcong (λ X → fmap (λ {(f , a) → f a}) (fmap (λ {(f , a) → f a}) ((X u) ** v) ** w)) (≡-to-≅ $ sym $ Functor.compose (F' FMon)) ⟩
        fmap (λ {(f , a) → f a}) (fmap (λ {(f , a) → f a}) ((fmap g u) ** v) ** w)
          ≅⟨ hcong (λ X → fmap (λ {(f , a) → f a}) (fmap (λ {(f , a) → f a}) ((fmap g u) ** X v) ** w)) (≡-to-≅ $ sym $ Functor.id (F' FMon)) ⟩
        fmap (λ {(f , a) → f a}) (fmap (λ {(f , a) → f a}) ((fmap g u) ** fmap (λ x → x) v) ** w)
          ≅⟨ hcong (λ X → fmap (λ {(f , a) → f a}) (fmap (λ {(f , a) → f a}) X ** w)) (≡-to-≅ $ sym $ law-naturality refl refl g (λ x → x) u v) ⟩
        fmap (λ {(f , a) → f a}) (fmap (λ {(f , a) → f a}) (fmap (g *** (λ x → x)) (u ** v)) ** w)
          ≅⟨ hcong (λ X → fmap (λ {(f , a) → f a}) (X (u ** v) ** w)) (≡-to-≅ $ sym $ Functor.compose (F' FMon)) ⟩
        fmap (λ {(f , a) → f a}) (fmap ((λ {(f , a) → f a}) ∘F (g *** (λ x → x))) (u ** v) ** w)
          ≅⟨ hcong (λ X → fmap (λ {(f , a) → f a}) (fmap ((λ {(f , a) → f a}) ∘F (g *** (λ x → x))) (u ** v) ** X w)) (≡-to-≅ $ sym $ Functor.id (F' FMon)) ⟩
        fmap (λ {(f , a) → f a}) (fmap ((λ {(f , a) → f a}) ∘F (g *** (λ x → x))) (u ** v) ** fmap (λ x → x) w)
          ≅⟨ hcong (fmap (λ {(f , a) → f a})) (≡-to-≅ $ sym $ law-naturality refl refl ((λ {(f , a) → f a}) ∘F (g *** (λ x → x))) (λ x → x) (u ** v) w) ⟩
        fmap (λ {(f , a) → f a}) (fmap (((λ {(f , a) → f a}) ∘F (g *** (λ x → x))) *** (λ x → x)) ((u ** v) ** w))
          ≅⟨ hcong (λ X → X ((u ** v) ** w)) (≡-to-≅ $ sym $ Functor.compose (F' FMon)) ⟩
        fmap h ((u ** v) ** w)
          ≅⟨ refl ⟩
        fmap (h' ∘F (λ {((a , b) , c) → (a , (b , c))})) ( (u ** v) ** w )
          ≅⟨ hcong (λ X → X ( (u ** v) ** w )) (≡-to-≅ $ Functor.compose (F' FMon)) ⟩
        fmap h' (fmap (λ {((a , b) , c) → (a , (b , c))}) ( (u ** v) ** w ) )
          ≅⟨ hcong₂ (λ X Y → F X γ ∋ fmap h' Y) (≡-to-≅ $ sym $ Monoid.assoc mon) (hsym $ law-associativity u v w) ⟩
        fmap h' (u ** (v ** w))
          ≅⟨ hcong (λ X → X (u ** (v ** w))) (≡-to-≅ $ Functor.compose (F' FMon)) ⟩
        fmap (λ {(f , a) → f a}) (fmap ((λ x → x) *** (λ {(f , a) → f a})) (u ** (v ** w)))
          ≅⟨ hcong (fmap (λ { (f , a) → f a })) (≡-to-≅ $ law-naturality refl refl (λ x → x) (λ {(f , a) → f a}) u (v ** w)) ⟩
        fmap (λ {(f , a) → f a}) (fmap (λ x → x) u ** fmap (λ {(f , a) → f a}) (v ** w))
          ≅⟨ hcong (λ X → fmap (λ { (f , a) → f a }) (X u ** fmap (λ { (f , a) → f a }) (v ** w))) (≡-to-≅ $ Functor.id (F' FMon)) ⟩
        fmap (λ {(f , a) → f a}) (u ** fmap (λ {(f , a) → f a}) (v ** w)) ∎h
        where
          g = (((λ {(f , a) → f a}) ∘F ((λ _ → _∘′_) *** (λ x → x))) ∘F (λ a → (lift tt , a)))
          h = ((λ {(f , a) → f a}) ∘F (((λ {(f , a) → f a}) ∘F (g *** (λ x → x))) *** (λ x → x)))
          h' = ((λ {(f , a) → f a}) ∘F ((λ x → x) *** (λ {(f , a) → f a})))
