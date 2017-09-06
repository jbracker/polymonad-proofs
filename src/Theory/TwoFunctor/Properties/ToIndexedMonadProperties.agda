 
-- Stdlib
open import Level
open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Data.Unit
open import Data.Product renaming ( _,_ to _,'_ )
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality 
  renaming ( refl to hrefl; sym to hsym ; trans to htrans ; cong to hcong ; cong₂ to hcong₂ ; subst to hsubst ; subst₂ to hsubst₂ ; proof-irrelevance to hproof-irrelevance )
open ≡-Reasoning hiding ( _≅⟨_⟩_ )
open ≅-Reasoning hiding ( _≡⟨_⟩_ ; _≡⟨⟩_ ) renaming ( begin_ to hbegin_ ; _∎ to _∎h)

-- Local
open import Extensionality
open import Utilities
open import Haskell
open import Haskell.Functor hiding ( functor ) renaming ( Functor to HaskellFunctor )
open import Haskell.Parameterized.Indexed.Monad
open import Theory.Triple
open import Theory.Category.Definition
open import Theory.Category.Examples.Codiscrete
open import Theory.Functor.Definition hiding ( functor )
open import Theory.Functor.Composition
open import Theory.Natural.Transformation
open import Theory.Natural.Transformation.Examples
open import Theory.TwoCategory.Definition
open import Theory.TwoCategory.Examples.Functor
open import Theory.TwoCategory.Examples.CodiscreteHomCat
open import Theory.TwoCategory.ExampleProperties
open import Theory.TwoFunctor.Definition
open import Theory.TwoFunctor.ConstZeroCell

module Theory.TwoFunctor.Properties.ToIndexedMonadProperties 
  {ℓS : Level} 
  (Ixs : Set ℓS)
  (F : ConstLaxTwoFunctor (codiscreteHomCatTwoCategory (codiscreteCategory Ixs)) (Cat {suc zero} {zero}) (Hask {zero})) 
  where

open NaturalTransformation renaming ( η to nat-η )
open StrictTwoCategory
open ConstLaxTwoFunctor F

private
  Cat' = Cat {suc zero} {zero}
  Hask' = Hask {zero}
  
  S : Category
  S = codiscreteCategory Ixs
    
  S₂ = codiscreteHomCatTwoCategory S
  
  M : Ixs → Ixs → TyCon
  M i j α = [ [ P₁ {j} {i} ]₀ (lift tt) ]₀ α

  return : {α : Type} {i : Ixs} → α → M i i α
  return {α} {i} a = nat-η (η {i}) α a

  join : {α : Type} {i j k : Ixs} → M i j (M j k α) → M i k α
  join {α} {i} {j} {k} mma = nat-η (μ {k} {j} {i}) α mma 
  
  fmap : {i j : Ixs} {α β : Type} → (α → β) → M i j α → M i j β
  fmap {i} {j} = [ [ P₁ {j} {i} ]₀ (lift tt) ]₁

abstract
  η-extract : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}} {F G : Functor C D} 
            → (NT₀ NT₁ : NaturalTransformation F G) 
            → NT₀ ≡ NT₁ 
            → (x : Category.Obj C) 
            → nat-η NT₀ x ≡ nat-η NT₁ x
  η-extract NT₀ .NT₀ refl x = refl

abstract
  η-lax-id₁ : {i j : Ixs} → (x : Type)
            → nat-η ([ P₁ {i} {j} ]₁ (lift tt)) x ∘F join {x} {j} {i} {i} ∘F fmap {j} {i} (return {x}) 
            ≡ nat-η (λ' Cat' ([ P₁ {i} {j} ]₀ (lift tt))) x
  η-lax-id₁ {i} {j} x = η-extract ⟨ [ P₁ {i} {j} ]₁ (lift tt) ⟩∘ᵥ⟨ ⟨ μ {i} {i} {j} ⟩∘ᵥ⟨ ⟨ Id⟨ [ P₁ {i} {j} ]₀ (lift tt) ⟩ ⟩∘ₕ⟨ η {i} ⟩ ⟩ ⟩ 
                                  (StrictTwoCategory.λ' Cat' ([ P₁ {i} {j} ]₀ (lift tt))) 
                                  (LaxTwoFunctor.laxFunId-λ' laxTwoFunctor {i} {j} {lift tt}) x

abstract
  η-lax-id₂ : {i j : Ixs} → (x : Type)
            → nat-η ([ P₁ {i} {j} ]₁ (lift tt)) x ∘F join {x} {j} {j} {i} ∘F return {M j i x}
            ≡ nat-η (ρ Cat' ([ P₁ {i} {j} ]₀ (lift tt))) x
  η-lax-id₂ {i} {j} x = η-extract ( ⟨ [ P₁ {i} {j} ]₁ (lift tt) ⟩∘ᵥ⟨ ⟨ μ {i} {j} {j} {lift tt} {id₁ S₂ {j}} ⟩∘ᵥ⟨ ⟨ η {j} ⟩∘ₕ⟨ id₂ Cat' {f = [ P₁ {i} {j} ]₀ (lift tt)} ⟩ ⟩ ⟩ )
                                  (StrictTwoCategory.ρ Cat' ([ P₁ {i} {j} ]₀ (lift tt))) 
                                  (LaxTwoFunctor.laxFunId-ρ laxTwoFunctor {i} {j} {lift tt}) x
    
--_∘Dᵥ_ = StrictTwoCategory._∘ᵥ_ Cat'
--_∘Dₕ₂_ = StrictTwoCategory._∘ₕ₂_ Cat' -- l k  (k j )
    
abstract
  η-lax-assoc : {i j k l : Ixs} (x : Type)
              → nat-η ([ P₁ {i} {l} ]₁ (lift tt)) x ∘F join {x} {l} {k} {i} ∘F fmap {l} {k} (join {x} {k} {j} {i})
              ≡ join {x} {l} {j} {i} ∘F join {M j i x} {l} {k} {j} ∘F fmap {l} {k} (fmap {k} {j} (λ x → x)) ∘F nat-η (α Cat' ([ P₁ {i} {j} ]₀ (lift tt)) ([ P₁ {j} {k} ]₀ (lift tt)) ([ P₁ {k} {l} ]₀ (lift tt))) x
  η-lax-assoc {i} {j} {k} {l} x = η-extract ( ⟨ [ P₁ {i} {l} ]₁ (lift tt) ⟩∘ᵥ⟨ ⟨ μ {i} {k} {l} {lift tt} {lift tt} ⟩∘ᵥ⟨ ⟨ id₂ Cat' {Hask} {Hask} {[ P₁ {k} {l} ]₀ (lift tt)} ⟩∘ₕ⟨ μ {i} {j} {k} {lift tt} {lift tt} ⟩ ⟩ ⟩ )
                                            ( ⟨ μ {i} {j} {l} {lift tt} {lift tt} 
                                              ⟩∘ᵥ⟨ ⟨ ⟨ μ {j} {k} {l} {lift tt} {lift tt} ⟩∘ₕ⟨ id₂ Cat' {Hask} {Hask} {[ P₁ {i} {j} ]₀ (lift tt)} ⟩ 
                                                   ⟩∘ᵥ⟨ α Cat' ([ P₁ {i} {j} ]₀ (lift tt)) ([ P₁ {j} {k} ]₀ (lift tt)) ([ P₁ {k} {l} ]₀ (lift tt)) ⟩ 
                                              ⟩) 
                                              (LaxTwoFunctor.laxFunAssoc-α laxTwoFunctor {i} {j} {k} {l} {lift tt}) x

abstract
  join-assoc : {i j k l : Ixs} (x : Type) 
             → join {x} {l} {k} {i} ∘F fmap {l} {k} (join {x} {k} {j} {i}) 
             ≡ join {x} {l} {j} {i} ∘F join {M j i x} {l} {k} {j} ∘F fmap {l} {k} (fmap {k} {j} (λ x → x))
  join-assoc {i} {j} {k} {l} x = begin
    join {x} {l} {k} {i} ∘F fmap {l} {k} (join {x} {k} {j} {i}) 
      ≡⟨ cong (λ X → nat-η X x ∘F join {x} {l} {k} {i} ∘F fmap {l} {k} (join {x} {k} {j} {i})) (sym (Functor.id (P₁ {i} {l}))) ⟩
    nat-η ([ P₁ {i} {l} ]₁ (lift tt)) x ∘F join {x} {l} {k} {i} ∘F fmap {l} {k} (join {x} {k} {j} {i})
      ≡⟨ η-lax-assoc {i} {j} {k} {l} x ⟩
    join {x} {l} {j} {i} ∘F join {M j i x} {l} {k} {j} ∘F fmap {l} {k} (fmap {k} {j} (λ x → x)) ∘F nat-η (α Cat' ([ P₁ {i} {j} ]₀ (lift tt)) ([ P₁ {j} {k} ]₀ (lift tt)) ([ P₁ {k} {l} ]₀ (lift tt))) x
      ≡⟨ cong (λ X → join {x} {l} {j} {i} ∘F join {M j i x} {l} {k} {j} ∘F fmap {l} {k} (fmap {k} {j} (λ x → x)) ∘F X) 
              (fun-ext $ λ y → ≅-to-≡ (het-cat-α-id {F = [ P₁ {i} {j} ]₀ (lift tt)} {[ P₁ {j} {k} ]₀ (lift tt)} {[ P₁ {k} {l} ]₀ (lift tt)} x y)) ⟩
    join {x} {l} {j} {i} ∘F join {M j i x} {l} {k} {j} ∘F fmap {l} {k} (fmap {k} {j} (λ x → x) ∘F (λ (y : M k j (M j i x)) → y)) ∎

abstract
  join-return-id : {i j : Ixs} → (x : Type) → join {x} {j} {j} {i} ∘F return {M j i x} ≡ (λ (y : M j i x) → y)
  join-return-id {i} {j} x = begin
    join {x} {j} {j} {i} ∘F return {M j i x} 
      ≡⟨ refl ⟩
    nat-η (Id⟨ [ P₁ {i} {j} ]₀ (lift tt) ⟩) x ∘F join {x} {j} {j} {i} ∘F return {M j i x} 
      ≡⟨ cong (λ X → nat-η X x ∘F join {x} {j} {j} {i} ∘F return {M j i x} ) (sym (Functor.id (P₁ {i} {j}))) ⟩
    nat-η ([ P₁ {i} {j} ]₁ (ρ S₂ {i} {j} (lift tt))) x ∘F join {x} {j} {j} {i} ∘F return {M j i x} 
      ≡⟨ η-lax-id₂ {i} {j} x ⟩
    nat-η (ρ Cat' ([ P₁ {i} {j} ]₀ (lift tt))) x
      ≡⟨ fun-ext (λ y → ≅-to-≡ (het-cat-ρ-id {F = [ P₁ {i} {j} ]₀ (lift tt)} x y)) ⟩
    (λ (y : M j i x) → y) ∎
