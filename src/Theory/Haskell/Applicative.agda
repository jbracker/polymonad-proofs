
open import Level
open import Function hiding ( id )

open import Data.Unit
open import Data.Product renaming ( _,_ to _,'_ )

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Theory.Category.Definition
open import Theory.Category.Examples.SetCat
open import Theory.Category.Closed
open import Theory.Category.Closed.Examples
open import Theory.Category.Monoidal
open import Theory.Category.Monoidal.Examples.SetCat
open import Theory.Functor.Definition
open import Theory.Functor.Closed
open import Theory.Functor.Monoidal
open import Theory.Natural.Transformation

open import Congruence

open import Haskell.Applicative

module Theory.Haskell.Applicative where

private
  Hask = setCategory {zero}
  Type = Set zero
  HaskClosed = setClosedCategory {zero}
  HaskMonoidal = setMonoidalCategory {zero}

LaxClosedFunctor→Applicative
  : (LCF : LaxClosedFunctor HaskClosed HaskClosed)
  → Applicative [ LaxClosedFunctor.F LCF ]₀
LaxClosedFunctor→Applicative LCF = record
  { pure = pure
  ; _<*>_ = _<*>_
  ; functor = record 
    { fmap = fmap
    ; law-id = Functor.id F
    ; law-compose = λ {α} {β} {γ} f g → Functor.compose F {α} {β} {γ} {g} {f}
    }
  ; law-id = law-id
  ; law-composition = law-composition
  ; law-homomorphism = law-homomorphism
  ; law-interchange = law-interchange
  ; law-applicative-fmap = law-applicative-fmap
  } where
    open LaxClosedFunctor LCF
    open ClosedCategory HaskClosed hiding ( _∘_ )
    
    fmap : {α β : Type} → (α → β) → F₀ α → F₀ β
    fmap f Fa = F₁ f Fa
    
    unit : F₀ (Lift ⊤)
    unit = F⁰ (lift tt)
    
    pure : {α : Type} → α → F₀ α
    pure a = fmap (λ _ → a) unit 

    _<*>_ : {α β : Type} → F₀ (α → β) → F₀ α → F₀ β
    _<*>_ {α} {β} Ff Fa = F̂ α β Ff Fa
    
    law-id : {α : Type} → (v : F₀ α) 
           → pure (λ x → x) <*> v ≡ v
    law-id {α} v = begin
      ((F̂ α α ∘ (F₁ (j α) ∘ F⁰)) (lift tt)) v
        ≡⟨ cong (λ P → (P (lift tt)) v) (sym (LaxClosedFunctor.coher-1 LCF α)) ⟩
      ((j (F₀ α)) (lift tt)) v
        ≡⟨⟩
      v ∎ 
    
    F̂-natural-y' : (x y y' : Type) (f : y → y') → (Fg : F₀ (x → y)) → (Fx : F₀ x)
                 → F₁ f (F̂ x y Fg (F₁ (λ a → a) Fx))
                 ≡ F̂ x y' (F₁ (λ g → f ∘ g) Fg) Fx
    F̂-natural-y' x y y' f Fg Fx = cong (λ P → P Fg Fx) (LaxClosedFunctor.F̂-natural-y LCF x {y} {y'} {f})
    
    coher-1' : (x : Type) → (Fx : F₀ x)
             → Fx ≡ F̂ x x (F₁ (λ _ a → a) (F⁰ (lift tt))) Fx
    coher-1' x Fx = cong (λ P → P (lift tt) Fx) (LaxClosedFunctor.coher-1 LCF x)
    
    coher-2' : (x : Type) (Ff : F₀ (I → x))
             → F₁ (λ h → h (lift tt)) Ff ≡ F̂ I x Ff (F⁰ (lift tt))
    coher-2' x Ff = cong (λ P → P Ff (lift tt)) (LaxClosedFunctor.coher-2 LCF x)
    
    coher-3' : (x y z : Type) → (Ff : F₀ (y → z)) → (Fg : F₀ (x → y)) → (Fx : F₀ x)
             → F̂ x z (F̂ (x → y) (x → z) (F₁ (λ g f → g ∘ f) Ff) Fg) Fx
             ≡ F̂ y z Ff (F̂ x y Fg Fx)
    coher-3' x y z Ff Fg Fx = cong (λ P → P Ff Fg Fx) (LaxClosedFunctor.coher-3 LCF x y z) 

    law-composition : {α β γ : Type} → (u : F₀ (β → γ)) (v : F₀ (α → β)) (w : F₀ α) 
                    → ((pure _∘′_ <*> u) <*> v) <*> w ≡ u <*> (v <*> w)
    law-composition {α} {β} {γ} u v w = begin
      F̂ α γ (F̂ (α → β) (α → γ) (F̂ (β → γ) ((α → β) → (α → γ)) (F₁ (λ _ → (λ f g → f ∘ g)) (F⁰ (lift tt))) u) v) w 
        ≡⟨ cong (λ P → F̂ α γ (F̂ (α → β) (α → γ) P v) w) helper ⟩
      F̂ α γ (F̂ (α → β) (α → γ) (F₁ (λ f g → f ∘ g) u) v) w
        ≡⟨ coher-3' α β γ u v w ⟩
      F̂ β γ u (F̂ α β v w) ∎
      where
        helper : F̂ (β → γ) ((α → β) → α → γ) (F₁ (λ _ f g → f ∘ g) (F⁰ (lift tt))) u 
               ≡ F₁ (λ f g → f ∘ g) u
        helper = begin
          F̂ (β → γ) ((α → β) → α → γ) (F₁ (λ _ f g → f ∘ g) (F⁰ (lift tt))) u 
            ≡⟨ {!!} ⟩
          F₁ (λ f g → f ∘ g) u ∎
    
    {-
    LaxClosedFunctor
    F̂ : (x y : Obj C) → Hom D (F₀ C[ x , y ]₀) (D[ F₀ x , F₀ y ]₀)
    
    F⁰ : Hom D (I D) (F₀ (I C))
    
    F̂-natural-x : (y : Obj C) → {x x' : Obj C} {f : Hom C x' x} 
                → D[ F₁ f , F₁ (idC C {y}) ]₁ ∘D F̂ x y ≡ F̂ x' y ∘D F₁ C[ f , idC C {y} ]₁
    
    F̂-natural-y : (x : Obj C) → {y y' : Obj C} {f : Hom C y y'} 
                → D[ F₁ (idC C {x}) , F₁ f ]₁ ∘D F̂ x y ≡ F̂ x y' ∘D F₁ C[ idC C {x} , f ]₁
    
    coher-1 : (x : Obj C) → j D (F₀ x) ≡ F̂ x x ∘D (F₁ (j C x) ∘D F⁰)
    
    coher-2 : (x : Obj C) → i D (F₀ x) ∘D F₁ (i-inv C x) ≡ D[ F⁰ , idC D ]₁ ∘D F̂ (I C) x
    
    coher-3 : (x y z : Obj C) 
            → D[ idC D , F̂ x z ]₁ ∘D (F̂ C[ x , y ]₀ C[ x , z ]₀ ∘D F₁ (L C x y z)) 
            ≡ D[ F̂ x y , idC D ]₁ ∘D (L D (F₀ x) (F₀ y) (F₀ z) ∘D F̂ y z)
    
    ClosedCategory:

    γ-inv : {x y : Obj C} → Hom C I [ x , y ]₀ → Hom C x y

    j-extranatural-a : {a a' : Obj C} (f : Hom C a a') 
                     → [ f , id C ]₁ ∘C (j a') ≡ [ id (C op) , f ]₁ ∘C (j a)
    
    L-natural-c : (a : Obj C) → (b : Obj (C op)) → {c c' : Obj C} {f : Hom C c c'}
                → ([ [ id C {a} , id C {b} ]₁ , [ id C {a} , f ]₁ ]₁) ∘C (L a b c) ≡ (L a b c') ∘C ([ id C {b} , f ]₁)
    
    L-natural-b : (a c : Obj C) → {b b' : Obj C} {f : Hom C b b'}
                → ([ [ id C {a} , f ]₁ , [ id C {a} , id C {c} ]₁ ]₁) ∘C (L a b' c) ≡ (L a b c) ∘C ([ f , id C {c} ]₁)
    
    L-extranatural-a : (b : Obj (C op)) → (c : Obj C) → {a a' : Obj C} (f : Hom C a a') 
                     → [ id C , [ f , id C {c} ]₁ ]₁ ∘C (L a' b c) ≡ [ [ f , id (C op) {b} ]₁ , id C ]₁ ∘C (L a b c)
    
    coher-1 : (x y : Obj C) → L x y y ∘C j y ≡ j [ x , y ]₀
    
    coher-2 : (x y : Obj C) → [ j x , id C ]₁ ∘C L x x y ≡ i [ x , y ]₀
    
    coher-3 : (y z : Obj C) → [ i y , id C ]₁ ∘C L I y z ≡ [ id C , i z ]₁
    
    coher-4 : (x y u v : Obj C) → [ id C , L x y v ]₁ ∘C L y u v ≡ [ L x y u , id C ]₁ ∘C (L [ x , y ]₀ [ x , u ]₀ [ x , v ]₀ ∘C L x u v)
    
    γ-right-id : {x y : Obj C} → (f : Hom C I [ x , y ]₀) → γ (γ-inv f) ≡ f
    
    γ-left-id  : {x y : Obj C} → (f : Hom C x y) → γ-inv (γ f) ≡ f
-}
    law-homomorphism : {α β : Type} (x : α) (f : α → β) 
                     → pure f <*> pure x ≡ pure (f x)
    law-homomorphism {α} {β} x f = {!!}
    
    law-interchange : {α β : Type} → (u : F₀ (α → β)) (x : α) 
                    → u <*> pure x ≡ pure (λ f → f x) <*> u
    law-interchange {α} {β} u x = {!!}
    
    law-applicative-fmap : {α β : Type} → (f : α → β) (x : F₀ α)
                         → fmap f x ≡ pure f <*> x
    law-applicative-fmap {α} {β} f x = {!!}

LaxMonoidalFunctor→Applicative
  : (LMF : LaxMonoidalFunctor HaskMonoidal HaskMonoidal)
  → Applicative [ LaxMonoidalFunctor.F LMF ]₀
LaxMonoidalFunctor→Applicative LMF = record
  { pure = pure
  ; _<*>_ = _<*>_
  ; functor = record 
    { fmap = fmap
    ; law-id = Functor.id F
    ; law-compose = λ {α} {β} {γ} f g → Functor.compose F {α} {β} {γ} {g} {f}
    }
  ; law-id = law-id
  ; law-composition = law-composition
  ; law-homomorphism = law-homomorphism
  ; law-interchange = law-interchange
  ; law-applicative-fmap = law-applicative-fmap
  } where
    open LaxMonoidalFunctor LMF
    open MonoidalCategory HaskMonoidal hiding ( _∘_ ; unit )
    
    fmap : {α β : Type} → (α → β) → F₀ α → F₀ β
    fmap f Fa = F₁ f Fa
    
    unit : F₀ (Lift ⊤)
    unit = ε (lift tt)
    
    pure : {α : Type} → α → F₀ α
    pure a = fmap (λ _ → a) unit
    
    _**_ : {α β : Type} → F₀ α → F₀ β → F₀ (α × β)
    _**_ {α} {β} Fa Fb = μ α β (Fa ,' Fb)

    _<*>_ : {α β : Type} → F₀ (α → β) → F₀ α → F₀ β
    _<*>_ {α} {β} Ff Fa = fmap (uncurry _$_) (Ff ** Fa)
    
    law-id : {α : Type} → (v : F₀ α) 
           → pure (λ x → x) <*> v ≡ v
    law-id {α} v = begin
      (F₁ (λ x → (proj₁ x) (proj₂ x)) ∘ μ (α → α) α) (F₁ (λ _ → (λ x → x)) (ε (lift tt)) ,' v)
        ≡⟨ {!!} ⟩
      v ∎
    
    naturality : {α β γ δ : Type} → (f : α → β) → (g : γ → δ) → (u : F₀ α) → (v : F₀ γ)
               → fmap (f *** g) (u ** v) ≡ fmap f u ** fmap g v
    naturality {α} {β} {γ} {δ} f g u v = cong (λ X → X (u ,' v)) $ NaturalTransformation.natural μ-natural-transformation
    
    associativity : {a b c : Type} → (u : F₀ a) → (v : F₀ b) → (w : F₀ c)
                  → fmap (α a b c) ((u ** v) ** w) ≡ u ** (v ** w)
    associativity {a} {b} {c} u v w = cong (λ P → P ((u ,' v) ,' w)) (LaxMonoidalFunctor.assoc LMF a b c)
    
    left-identity : {a : Type} → (v : F₀ a) → fmap (λ' a) (unit ** v) ≡ v
    left-identity {a} v = cong (λ P → P (lift tt ,' v)) (sym (LaxMonoidalFunctor.left-unitality LMF a))
    
    left-identity' : {a : Type} → (v : F₀ a) → (unit ** v) ≡ fmap (λ x → lift tt ,' x) v
    left-identity' {a} v = begin
      unit ** v 
        ≡⟨ cong (λ P → P (unit ** v)) (sym $ Functor.id F) ⟩
      fmap (λ x → x) (unit ** v) 
        ≡⟨⟩
      fmap ((λ x → lift tt ,' x) ∘ λ' a) (unit ** v) 
        ≡⟨ cong (λ P → P (unit ** v)) (Functor.compose F) ⟩
      (fmap (λ x → lift tt ,' x) ∘ fmap (λ' a)) (unit ** v) 
        ≡⟨⟩
      fmap (λ x → lift tt ,' x) (fmap (λ' a) (unit ** v))
        ≡⟨ cong (fmap (λ x → lift tt ,' x)) (left-identity v) ⟩
      fmap (λ x → lift tt ,' x) v ∎
    
    right-identity : {a : Type} → (v : F₀ a) → fmap (ρ a) (v ** unit) ≡ v
    right-identity {a} v = cong (λ P → P (v ,' lift tt)) (sym (LaxMonoidalFunctor.right-unitality LMF a))
    
    law-composition : {α β γ : Type} → (u : F₀ (β → γ)) (v : F₀ (α → β)) (w : F₀ α) 
                    → ((pure _∘′_ <*> u) <*> v) <*> w ≡ u <*> (v <*> w)
    law-composition {α} {β} {γ} u v w = begin
      fmap (uncurry _$_) (fmap (uncurry _$_) (fmap (uncurry _$_) ((fmap (λ _ → _∘′_) unit) ** u) ** v) ** w) 
        ≡⟨ cong (λ X → fmap (uncurry _$_) (fmap (uncurry _$_) (fmap (uncurry _$_) (fmap (λ _ → _∘′_) unit ** X) ** v) ** w))
                (cong (λ P → P u) (sym $ Functor.id F)) ⟩
      fmap (uncurry _$_) (fmap (uncurry _$_) (fmap (uncurry _$_) ((fmap (λ _ → _∘′_) unit) ** (fmap (λ a → a) u)) ** v) ** w) 
        ≡⟨ cong (λ X → fmap (uncurry _$_) (fmap (uncurry _$_) (fmap (uncurry _$_) X ** v) ** w))
                (sym (naturality (λ _ → _∘′_) (λ z → z) unit u)) ⟩
      fmap (uncurry _$_) (fmap (uncurry _$_) (fmap (uncurry _$_) (fmap ((λ _ → _∘′_) *** (λ a → a)) (unit ** u)) ** v) ** w) 
        ≡⟨ {!!} ⟩
      fmap (uncurry _$_) (fmap (uncurry _$_) (fmap (uncurry _$_) (fmap ((λ _ → _∘′_) *** (λ a → a)) (fmap (λ x → lift tt ,' x) u)) ** v) ** w) 
        ≡⟨ {!!} ⟩
      fmap (uncurry _$_) (fmap (uncurry _$_) (fmap (uncurry _$_) (fmap (((λ _ → _∘′_) *** (λ a → a)) ∘ (λ x → lift tt ,' x)) u) ** v) ** w) 
        ≡⟨ {!!} ⟩
      fmap (uncurry _$_) (fmap (uncurry _$_) (fmap (uncurry _$_) (fmap (((λ _ f g → f ∘ g) *** (λ a → a)) ∘ (λ x → lift tt ,' x)) u) ** (fmap (λ a → a) v)) ** w) 
      --  ≡⟨ {!!} ⟩
      --fmap (uncurry _$_) (fmap (uncurry _$_) (fmap (uncurry _$_) (fmap ((((λ _ f g → f ∘ g) *** (λ a → a)) ∘ (λ x → lift tt ,' x)) *** (λ a → a)) (u ** v))) ** w) 
        ≡⟨ {!!} ⟩
      fmap (uncurry _$_ ∘ ((λ a → a) *** (uncurry _$_))) (u ** (v ** w))
        ≡⟨ {!!} ⟩
      fmap (uncurry _$_) (fmap ((λ a → a) *** (uncurry _$_)) (u ** (v ** w)))
        ≡⟨ {!!} ⟩
      fmap (uncurry _$_) (fmap (λ a → a) u ** fmap (uncurry _$_) (v ** w))
        ≡⟨ {!!} ⟩
      fmap (uncurry _$_) (u ** fmap (uncurry _$_) (v ** w)) ∎
    {-

    _<*>_ : {α β : Type} → F₀ (α → β) → F₀ α → F₀ β
    _<*>_ {α} {β} Ff Fa = fmap (uncurry _$_) (Ff ** Fa)
-}
    law-homomorphism : {α β : Type} (x : α) (f : α → β) 
                     → pure f <*> pure x ≡ pure (f x)
    law-homomorphism {α} {β} x f = {!!}
    
    law-interchange : {α β : Type} → (u : F₀ (α → β)) (x : α) 
                    → u <*> pure x ≡ pure (λ f → f x) <*> u
    law-interchange {α} {β} u x = {!!}
    
    law-applicative-fmap : {α β : Type} → (f : α → β) (x : F₀ α)
                         → fmap f x ≡ pure f <*> x
    law-applicative-fmap {α} {β} f x = {!!}
    
