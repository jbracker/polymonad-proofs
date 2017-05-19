
-- Stdlib
open import Level
open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Data.Unit
open import Data.Product renaming ( _,_ to _,'_ )
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( refl to hrefl ; sym to hsym ; trans to htrans ; cong to hcong ; subst₂ to hsubst₂ )
open ≡-Reasoning hiding ( _≅⟨_⟩_ )
open ≅-Reasoning hiding ( _≡⟨⟩_ ; _≡⟨_⟩_ ) renaming ( begin_ to hbegin_ ; _∎ to _∎h )

-- Local
open import Extensionality
open import Utilities
open import Haskell
open import Haskell.Functor hiding ( functor ) renaming ( Functor to HaskellFunctor )
open import Haskell.Parameterized.EffectMonad
open import Theory.Triple
open import Theory.Monoid
open import Theory.Category
open import Theory.Category.Examples
open import Theory.Functor hiding ( functor )
open import Theory.Functor.Composition
open import Theory.Natural.Transformation
open import Theory.Natural.Transformation.Examples
open import Theory.TwoCategory
open import Theory.TwoCategory.Examples
open import Theory.TwoCategory.ExampleProperties
open import Theory.TwoCategory.Examples.DiscreteHomCat
open import Theory.TwoFunctor.ConstZeroCell

open Category hiding ( left-id ; right-id ; assoc )
open StrictTwoCategory

module Theory.TwoFunctor.Properties.ToEffectMonad where

private
  Cat' = Cat {suc zero} {zero}
  Hask' = Hask {zero}

LaxTwoFunctor→EffectMonadTyCon 
  : {ℓ : Level}
  → {Eff : Set ℓ}
  → (mon : Monoid Eff)
  → (F : ConstLaxTwoFunctor (discreteHomCatTwoCategory (monoidCategory mon)) Cat' Hask')
  → ( Eff → TyCon )
LaxTwoFunctor→EffectMonadTyCon S F i A = [ [ ConstLaxTwoFunctor.P₁ F {lift tt} {lift tt} ]₀ i ]₀ A

LaxTwoFunctor→EffectMonad
  : {ℓ : Level}
  → {Eff : Set ℓ}
  → (mon : Monoid Eff)
  → (F : ConstLaxTwoFunctor (discreteHomCatTwoCategory (monoidCategory mon)) Cat' Hask')
  → EffectMonad mon (LaxTwoFunctor→EffectMonadTyCon mon F)
LaxTwoFunctor→EffectMonad {ℓ} {Eff} mon F = record
  { _>>=_ = _>>=_
  ; return = return
  ; functor = functor
  ; law-left-id = law-left-id
  ; law-right-id = law-right-id
  ; law-assoc = law-assoc
  ; law-monad-fmap = law-monad-fmap
  }
  where
    open ConstLaxTwoFunctor F
    open Monoid mon
    open NaturalTransformation renaming (η to nat-η)


    import Theory.TwoFunctor.Properties.ToEffectMonadProperties
    open Theory.TwoFunctor.Properties.ToEffectMonadProperties mon F
    
    _∘Eff_ = _∙_
    
    MonCat₁ : Category
    MonCat₁ = monoidCategory mon
    
    MonCat₂ = discreteHomCatTwoCategory MonCat₁
    
    Fun = λ i → [ ConstLaxTwoFunctor.P₁ F {lift tt} {lift tt} ]₀ i
    
    M : Eff → TyCon
    M = LaxTwoFunctor→EffectMonadTyCon mon F
    
    fmap : {i : Eff} {α β : Type} → (α → β) → M i α → M i β
    fmap {i} = [ [ P₁ {lift tt} {lift tt} ]₀ i ]₁
    
    functor : (i : Eff) → HaskellFunctor (M i)
    functor i = Functor.functor (fmap {i}) 
                                (Functor.id ([ P₁ {lift tt} {lift tt} ]₀ i))
                                (λ g f → Functor.compose ([ P₁ {lift tt} {lift tt} ]₀ i) {f = f} {g = g})
    
    return : {α : Type} → α → M ε α
    return {α} a = nat-η (η {lift tt}) α a

    join : {α : Type} {i j : Eff} → M i (M j α) → M (i ∘Eff j) α
    join {α} {i} {j} mma = nat-η (μ {f = j} {i}) α mma 
    
    _>>=_ : {α β : Type} {i j : Eff} → M i α → (α → M j β) → M (i ∘Eff j) β
    _>>=_ {α} {β} {i} {j} ma f = join (fmap f ma)
    
    natural-μ : {i j : Eff} → (α β : Type) → (f : α → β) 
              → (fmap f) ∘F (join {α} {j} {i}) ≡ join {β} ∘F fmap (fmap f) 
    natural-μ {i} {j} a b f = natural (μ {f = i} {j}) {a = a} {b} {f} 
    
    natural-η : {i : Eff} → (α β : Type) → (f : α → β) 
              → (fmap f) ∘F (return {α}) ≡ return {β} ∘F f 
    natural-η {i} a b f = natural (η {lift tt}) {a = a} {b} {f} 
    
    law-left-id : {α β : Type} {i : Eff} → (a : α) → (k : α → M i β) → return a >>= k ≅ k a
    law-left-id {α} {β} {i} a k = hbegin
      (M (ε ∘Eff i) β ∋ (return a >>= k) )
        ≅⟨ hrefl ⟩
      (M (ε ∘Eff i) β ∋ join (fmap k (return a)))
        ≅⟨ hcong (λ X → (join ∘F X) a) (≡-to-≅ $ natural-η {i} α (M i β) k) ⟩
      (M (ε ∘Eff i) β ∋ join (return (k a)))
        ≅⟨ join-return-id β (k a) ⟩
      (M i β ∋ k a) ∎h
    
    law-right-id : {α : Type} {i : Eff} → (m : M i α) → m >>= return ≅ m
    law-right-id {α} {i} m = hbegin
      (M (i ∘Eff ε) α ∋ m >>= return) 
        ≅⟨ hrefl ⟩ 
      (M (i ∘Eff ε) α ∋ (join ∘F fmap (return {α})) m)
        ≅⟨ hrefl ⟩ 
      (M (i ∘Eff ε) α ∋ (nat-η (Id⟨ [ P₁ ]₀ (i ∘Eff ε) ⟩) α ∘F join ∘F fmap return) m)
        ≅⟨ hsym (subst-refl-id (sym right-id) (join (fmap return m))) ⟩
      (M i α ∋ (nat-η ([ P₁ ]₁ ((λ' MonCat₂ i))) α ∘F join ∘F fmap return) m)
        ≅⟨ ≡-to-≅ $ η-lax-id₁ {i} α m ⟩ --  ⟩
      (M i α ∋ m) ∎h

    law-right-id' : {α : Type} {i : Eff} → ( (M i α → M (i ∘Eff ε) α) ∋ join ∘F fmap return ) ≅ ( (M i α → M i α) ∋ (λ (x : M i α) → x) )
    law-right-id' {α} {i} = het-fun-ext (het-fun-ext hrefl (λ _ → hsym (hcong (λ X → Functor.F₀ (Functor.F₀ P₁ X) α) (≡-to-≅ (sym right-id))))) (law-right-id {α} {i})

    law-assoc : {α β γ : Type} {i j k : Eff} 
              → (m : M i α) (f : α → M j β) (g : β → M k γ) 
              → m >>= (λ x → f x >>= g) ≅ (m >>= f) >>= g
    law-assoc {α} {β} {γ} {i} {j} {k} m f g = hbegin
      (M (i ∘Eff (j ∘Eff k)) γ ∋ join (fmap (join ∘F fmap g ∘F f) m) )
        ≅⟨ ≡-to-≅ (cong (λ X → join (X m)) (Functor.compose ([ P₁ ]₀ i))) ⟩ -- 
      (M (i ∘Eff (j ∘Eff k)) γ ∋ join (fmap join (fmap (fmap g ∘F f) m)) )
        ≅⟨ ≡-to-≅ (cong (λ X → (join ∘F fmap join ∘F X) m) (Functor.compose ([ P₁ ]₀ i))) ⟩ 
      (M (i ∘Eff (j ∘Eff k)) γ ∋ (join ∘F fmap join ∘F fmap (fmap g) ∘F fmap f) m)
        ≅⟨ join-assoc γ ((fmap (fmap g) ∘F fmap f) m) ⟩ -- cong (λ X → (X ∘F fmap (fmap g) ∘F fmap f) m) (join-assoc γ) ⟩ 
      (M ((i ∘Eff j) ∘Eff k) γ ∋ (join ∘F join ∘F fmap (fmap (λ x → x)) ∘F fmap (fmap g) ∘F fmap f) m)
        ≅⟨ ≡-to-≅ (cong (λ X → (join ∘F join ∘F fmap X ∘F fmap (fmap g) ∘F fmap f) m) (Functor.id (Fun j))) ⟩
      (M ((i ∘Eff j) ∘Eff k) γ ∋ (join ∘F join ∘F fmap (λ x → x) ∘F fmap (fmap g) ∘F fmap f) m)
        ≅⟨ ≡-to-≅ (cong (λ X → (join ∘F join ∘F X ∘F fmap (fmap g) ∘F fmap f) m) (Functor.id (Fun i))) ⟩
      (M ((i ∘Eff j) ∘Eff k) γ ∋ (join ∘F join ∘F fmap (fmap g) ∘F fmap f) m )
        ≅⟨ ≡-to-≅ (cong (λ X → (join ∘F X ∘F fmap f) m) (sym (natural-μ β (M k γ) g))) ⟩ 
      (M ((i ∘Eff j) ∘Eff k) γ ∋ join (fmap g (join (fmap f m))) ) ∎h
    
    fun-helper : {α β : Type} {i j : Eff} → i ≡ j → (ma : M i α) → (f : M i α → M j β) (g : M i α → M i β) → (f ≅ g) → f ma ≅ g ma
    fun-helper refl ma f .f hrefl = hrefl
    
    law-monad-fmap : {α β : Type} {i : Eff} → (f : α → β) (ma : M i α)
                   → ma >>= (return ∘F f) ≅ fmap f ma
    law-monad-fmap {α} {β} {i} f ma = hbegin
      (M (i ∘Eff ε) β ∋ (join ∘F fmap (return ∘F f)) ma)
        ≅⟨ ≡-to-≅ (cong (λ X → (join ∘F X) ma) (Functor.compose ([ P₁ ]₀ i))) ⟩
      (M (i ∘Eff ε) β ∋ (join ∘F fmap return ∘F fmap f) ma )
        ≅⟨ fun-helper (sym right-id) (fmap f ma) (join ∘F fmap return) (λ x → x) law-right-id' ⟩
      (M i β ∋ fmap f ma) ∎h
