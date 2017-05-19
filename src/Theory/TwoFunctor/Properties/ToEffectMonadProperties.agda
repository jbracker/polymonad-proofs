 
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
open import Theory.TwoCategory.Examples.DiscreteHomCat
open import Theory.TwoCategory.ExampleProperties
open import Theory.TwoFunctor.ConstZeroCell

module Theory.TwoFunctor.Properties.ToEffectMonadProperties 
  {ℓ : Level} 
  {Eff : Set ℓ}
  (mon : Monoid Eff)
  (F : ConstLaxTwoFunctor (discreteHomCatTwoCategory (monoidCategory mon)) (Cat {suc zero} {zero}) (Hask {zero})) 
  where

open NaturalTransformation renaming ( η to nat-η )
open StrictTwoCategory
open ConstLaxTwoFunctor F
open Monoid mon

private
  Cat' = Cat {suc zero} {zero}
  Hask' = Hask {zero}
    
  _∘Eff_ = _∙_
    
  MonCat₁ : Category
  MonCat₁ = monoidCategory mon
  
  MonCat₂ = discreteHomCatTwoCategory MonCat₁
  
  Fun = λ i → [ ConstLaxTwoFunctor.P₁ F {lift tt} {lift tt} ]₀ i
  
  M : Eff → TyCon
  M i α = [ [ ConstLaxTwoFunctor.P₁ F {lift tt} {lift tt} ]₀ i ]₀ α
  
  return : {α : Type} → α → M ε α
  return {α} a = nat-η (η {lift tt}) α a
  
  join : {α : Type} {i j : Eff} → M i (M j α) → M (i ∘Eff j) α
  join {α} {i} {j} mma = nat-η (μ {f = j} {i}) α mma 
    
  fmap : {i : Eff} {α β : Type} → (α → β) → M i α → M i β
  fmap {i} = [ [ P₁ {lift tt} {lift tt} ]₀ i ]₁

  η-extract : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}} {F G : Functor C D} 
            → (NT₀ NT₁ : NaturalTransformation F G) 
            → NT₀ ≡ NT₁ 
            → (x : Category.Obj C) 
            → nat-η NT₀ x ≡ nat-η NT₁ x
  η-extract NT₀ .NT₀ refl x = refl

η-lax-id₁ : {i : Eff} (x : Type) (ma : M i x)
          → nat-η ([ P₁ ]₁ (λ' MonCat₂ i)) x (join (fmap return ma)) ≡ ma
η-lax-id₁ {i} x ma = cong (λ X → X ma) 
                   $ η-extract ⟨ [ P₁ ]₁ (λ' MonCat₂ i) ⟩∘ᵥ⟨ ⟨ μ {f = ε} {i} ⟩∘ᵥ⟨ ⟨ Id⟨ [ P₁ ]₀ i ⟩ ⟩∘ₕ⟨ η ⟩ ⟩ ⟩ 
                               (StrictTwoCategory.λ' Cat' ([ P₁ ]₀ i)) 
                               (laxFunId₁ {f = i}) x

η-lax-id₂ : {i : Eff} (x : Type) (ma : M i x)
          → nat-η ([ P₁ ]₁ (ρ MonCat₂ i)) x (join (return ma))
          ≡ nat-η (ρ Cat' ([ P₁ ]₀ i)) x ma
η-lax-id₂ {i} x ma = cong (λ X → X ma) 
                   $ η-extract ( ⟨ [ P₁ ]₁ (ρ MonCat₂ i) ⟩∘ᵥ⟨ ⟨ μ {f = i} {id₁ MonCat₂} ⟩∘ᵥ⟨ ⟨ η ⟩∘ₕ⟨ id₂ Cat' {f = [ P₁ ]₀ i} ⟩ ⟩ ⟩ )
                               (StrictTwoCategory.ρ Cat' ([ P₁ ]₀ i)) 
                               (laxFunId₂ {f = i}) x

η-lax-assoc : {i j k : Eff} (x : Type) (ma : M i (M j (M k x)))
            → (nat-η ([ P₁ ]₁ (α MonCat₂ k j i)) x ∘F join ∘F fmap join) ma
            ≡ (join ∘F join ∘F fmap (fmap (λ x → x)) ∘F nat-η (α Cat' ([ P₁ ]₀ k) ([ P₁ ]₀ j) ([ P₁ ]₀ i)) x) ma
η-lax-assoc {i} {j} {k} x ma = cong (λ X → X ma) 
                             $ η-extract ( ⟨ [ P₁ ]₁ (α MonCat₂ k j i) ⟩∘ᵥ⟨ ⟨ μ ⟩∘ᵥ⟨ ⟨ id₂ Cat' {f = [ P₁ ]₀ i} ⟩∘ₕ⟨ μ ⟩ ⟩ ⟩ )
                                         ( ⟨ μ ⟩∘ᵥ⟨ ⟨ ⟨ μ ⟩∘ₕ⟨ id₂ Cat' {f = [ P₁ ]₀ k} ⟩ ⟩∘ᵥ⟨ α Cat' ([ P₁ ]₀ k) ([ P₁ ]₀ j) ([ P₁ ]₀ i) ⟩ ⟩) 
                                         (laxFunAssoc {f = k} {j} {i}) x

subst-refl-id : {α : Type} {i j : Eff} → (eq : i ≡ j) → (ma : M j α) → nat-η ([ P₁ ]₁ (subst₂ _≡_ eq refl (refl {ℓ} {Eff} {i}))) α ma ≅ nat-η (Id⟨ Fun j ⟩) α ma
subst-refl-id {α} {i} {.i} refl ma = hcong (λ X → nat-η X α ma) (≡-to-≅ (Functor.id P₁))

subst-refl-id' : {α : Type} {i j : Eff} → (eq : i ≡ j) → (ma : M i α) → nat-η ([ P₁ ]₁ (subst₂ _≡_ refl eq (refl {ℓ} {Eff} {i}))) α ma ≅ nat-η (Id⟨ Fun i ⟩) α ma
subst-refl-id' {α} {i} {.i} refl ma = hcong (λ X → nat-η X α ma) (≡-to-≅ (Functor.id P₁))

join-assoc : {i j k : Eff} (x : Type) (ma : M k (M j (M i x)))
           → join (fmap join ma) ≅ join (join (fmap (fmap (λ x → x)) ma))
join-assoc {i} {j} {k} x ma = hbegin
  (M (k ∘Eff (j ∘Eff i)) x ∋ join (fmap join ma) )
    ≅⟨ hsym (subst-refl-id' assoc (join (fmap join ma))) ⟩
  (M ((k ∘Eff j) ∘Eff i) x ∋ nat-η ([ P₁ ]₁ (α MonCat₂ i j k)) x (join (fmap join ma)) )
    ≅⟨ ≡-to-≅ (η-lax-assoc x ma) ⟩
  (M ((k ∘Eff j) ∘Eff i) x ∋ join (join (fmap (fmap (λ x → x)) (nat-η (α Cat' ([ P₁ ]₀ i) ([ P₁ ]₀ j) ([ P₁ ]₀ k)) x ma))) )
    ≅⟨ hcong (λ X → join (join (fmap (fmap (λ x → x)) X))) (het-cat-α-id {F = Fun i} {G = Fun j} {Fun k} x ma) ⟩
  (M ((k ∘Eff j) ∘Eff i) x ∋ join (join (fmap (fmap (λ x → x)) ma)) ) ∎h

join-return-id : {i : Eff} → (x : Type) → (ma : M i x) → join {x} {ε} {i} (return ma) ≅ ma
join-return-id {i} x ma = hbegin
  (M (ε ∘Eff i) x ∋ join {x} (return ma))
    ≅⟨ hrefl ⟩
  (M (ε ∘Eff i) x ∋ nat-η (Id⟨ [ P₁ {lift tt} {lift tt} ]₀ (ε ∘Eff i) ⟩) x (join {x} (return ma)) )
    ≅⟨ hsym (subst-refl-id (sym left-id) (join (return ma))) ⟩
  (M i x ∋ nat-η ([ P₁ ]₁ (ρ MonCat₂ i)) x (join {x} (return ma)) )
    ≅⟨ ≡-to-≅ $ η-lax-id₂ x ma ⟩ -- η-lax-id₂ x 
  (M i x ∋ nat-η (ρ Cat' ([ P₁ ]₀ i)) x ma)
    ≅⟨ het-cat-ρ-id x ma ⟩
  (M i x ∋ ma) ∎h
