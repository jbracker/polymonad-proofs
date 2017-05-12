 
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
open import Haskell.Parameterized.IndexedMonad
open import Theory.Triple
open import Theory.Category
open import Theory.Category.Examples
open import Theory.Functor hiding ( functor )
open import Theory.Functor.Composition
open import Theory.Natural.Transformation
open import Theory.Natural.Transformation.Examples
open import Theory.TwoCategory
open import Theory.TwoCategory.Examples
open import Theory.TwoCategory.ExampleProperties
open import Theory.TwoFunctor.Examples.ConstZeroCell

module Theory.TwoFunctor.Examples.ToIndexedMonadProperties 
  {ℓS : Level} 
  (Ixs : Set ℓS)
  (F : ConstLaxTwoFunctor (Category→StrictTwoCategory (codiscreteCategory Ixs)) (Cat {suc zero} {zero}) (Hask {zero})) 
  where

open NaturalTransformation renaming ( η to nat-η )
open StrictTwoCategory
open ConstLaxTwoFunctor F

private
  Cat' = Cat {suc zero} {zero}
  Hask' = Hask {zero}
  
  S : Category
  S = codiscreteCategory Ixs
    
  S₂ = Category→StrictTwoCategory S
  
  M : Ixs → Ixs → TyCon
  M i j α = [ [ P₁ {j} {i} ]₀ (lift tt) ]₀ α

  return : {α : Type} {i : Ixs} → α → M i i α
  return {α} {i} a = nat-η (η {i}) α a

  join : {α : Type} {i j k : Ixs} → M i j (M j k α) → M i k α
  join {α} {i} {j} {k} mma = nat-η (μ {k} {j} {i}) α mma 
  
  fmap : {i j : Ixs} {α β : Type} → (α → β) → M i j α → M i j β
  fmap {i} {j} = [ [ P₁ {j} {i} ]₀ (lift tt) ]₁

helper : {F G : Functor Hask' Hask'} → (p : F ≡ G) → (α : Type) → (x : [ G ]₀ α) → nat-η (subst₂ NaturalTransformation p refl Id⟨ F ⟩) α x ≅ x
helper {F} {.F} refl α x = hrefl

helper' : {F G : Functor Hask' Hask'} → (p : G ≡ F) → (α : Type) → (x : [ G ]₀ α) → nat-η (subst₂ NaturalTransformation (sym p) refl Id⟨ F ⟩) α x ≡ subst (λ X → [ X ]₀ α) p x
helper' {F} {.F} refl α x = refl

helper2 : {F G : Functor Hask' Hask'} → (p : F ≡ G) → (α : Type) → (x : [ F ]₀ α) → nat-η (subst₂ NaturalTransformation refl p Id⟨ F ⟩) α x ≅ x
helper2 {F} {.F} refl α x = hrefl

--helper2 : {F G : Functor Hask' Hask'} → (p : F ≡ G) → subst₂ NaturalTransformation p refl Id⟨ F ⟩ ≅ Id⟨ F ⟩
--helper2 {F} {.F} refl = hrefl

--p2 : {i j : Ixs} → (α : Type) → (x : M j i α) → nat-η (ρ Cat' ([ P₁ {i} {j} ]₀ (lift tt))) α x ≡ subst (λ X → [ X ]₀ α) (hIdR₁ Cat' {Hask} {Hask} {[ P₁ {i} {j} ]₀ (lift tt)}) x
--p2 {i} {j} α x = helper' (hIdR₁ Cat' {Hask} {Hask} {[ P₁ {i} {j} ]₀ (lift tt)}) α x

ρ-id : {i j : Ixs} → (α : Type) → nat-η (ρ Cat' ([ P₁ {i} {j} ]₀ (lift tt))) α ≅ (λ (x : M j i α) → x)
ρ-id {i} {j} α = het-fun-ext hrefl $ λ x → hbegin
  nat-η (ρ Cat' ([ P₁ ]₀ (lift tt))) α x 
    ≅⟨ hrefl ⟩
  nat-η (subst₂ NaturalTransformation (sym $ hIdR₁ Cat' {Hask} {Hask} {[ P₁ {i} {j} ]₀ (lift tt)}) refl (Id⟨ [ P₁ {i} {j} ]₀ (lift tt) ⟩)) α x
    ≅⟨ helper (sym $ hIdR₁ Cat' {Hask} {Hask} {[ P₁ {i} {j} ]₀ (lift tt)}) α x ⟩
  x ∎h 

α-id : {i j k l : Ixs} → (x : Type) 
     → nat-η (α Cat' ([ P₁ {i} {j} ]₀ (lift tt)) ([ P₁ {j} {k} ]₀ (lift tt)) ([ P₁ {k} {l} ]₀ (lift tt))) x ≅ (λ (y : M l k (M k j (M j i x))) → y)
α-id {i} {j} {k} {l} x = hbegin
  nat-η (α Cat' {Hask} {Hask} {Hask} {Hask} ([ P₁ {i} {j} ]₀ (lift tt)) ([ P₁ {j} {k} ]₀ (lift tt)) ([ P₁ {k} {l} ]₀ (lift tt))) x 
    ≅⟨ hrefl ⟩ 
  --nat-η (associator Cat' {Hask} {Hask} {Hask} {Hask} {f = [ P₁ {i} {j} ]₀ (lift tt)} {[ P₁ {j} {k} ]₀ (lift tt)} {[ P₁ {k} {l} ]₀ (lift tt)}) x
  nat-η (subst₂ NaturalTransformation refl (hAssoc₁ Cat' {Hask} {Hask} {Hask} {Hask} {[ P₁ {i} {j} ]₀ (lift tt)} {[ P₁ {j} {k} ]₀ (lift tt)} {[ P₁ {k} {l} ]₀ (lift tt)}) 
                (Id⟨ [ [ P₁ {k} {l} ]₀ (lift tt) ]∘[ ([ [ P₁ {j} {k} ]₀ (lift tt) ]∘[ [ P₁ {i} {j} ]₀ (lift tt) ] ) ] ⟩) ) x
    ≅⟨ het-fun-ext hrefl (λ (y : M l k (M k j (M j i x))) → helper2 (hAssoc₁ Cat' {Hask} {Hask} {Hask} {Hask} {[ P₁ {i} {j} ]₀ (lift tt)} {[ P₁ {j} {k} ]₀ (lift tt)} {[ P₁ {k} {l} ]₀ (lift tt)}) x y) ⟩
  (λ (y : M l k (M k j (M j i x))) → y) ∎h
--  associator {a} {b} {c} {d} {f} {g} {h} = subst₂ Cell₂ refl (hAssoc₁ {a} {b} {c} {d} {f} {g} {h}) (id₂ {a} {d} {h ∘ₕ (g ∘ₕ f)})
-- α {a} {b} {c} {d} f g h = associator {a} {b} {c} {d} {f = f} {g} {h}
{-
p4 : {F G : Functor Hask' Hask'} → (N₀ : NaturalTransformation F F) → (N₁ : NaturalTransformation G F) → (eqF : G ≡ F) → (eqN : N₀ ≅ N₁)  → N₀ ≡ subst₂ NaturalTransformation eqF refl N₁
p4 N₀ N₁ refl eqN = ≅-to-≡ eqN

p3 : {i j : Ixs} {α : Type} → (x : M j i α) → ([ P₁ {i} {j} ]₁ (ρ S₂ {i} {j} (lift tt))) ≡ subst₂ NaturalTransformation (hIdR₁ Cat') refl (ρ Cat' ([ P₁ {i} {j} ]₀ (lift tt)))
p3 {i} {j} {α} x = p4 ([ P₁ {i} {j} ]₁ (ρ S₂ {i} {j} (lift tt))) (ρ Cat' ([ P₁ {i} {j} ]₀ (lift tt))) (hIdR₁ Cat') $ hbegin
  [ P₁ {i} {j} ]₁ (ρ S₂ {i} {j} (lift tt)) 
    ≅⟨ ≡-to-≅ (Functor.id (P₁ {i} {j})) ⟩
  Id⟨ [ P₁ {i} {j} ]₀ (lift tt) ⟩
    ≅⟨ hsym $ helper2 (sym $ hIdR₁ Cat' {Hask} {Hask} {[ P₁ {i} {j} ]₀ (lift tt)}) ⟩
  ρ Cat' ([ P₁ {i} {j} ]₀ (lift tt)) ∎h
-}

η-extract : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}} {F G : Functor C D} 
          → (NT₀ NT₁ : NaturalTransformation F G) 
          → NT₀ ≡ NT₁ 
          → (x : Category.Obj C) 
          → nat-η NT₀ x ≡ nat-η NT₁ x
η-extract NT₀ .NT₀ refl x = refl

η-lax-id₁ : {i j : Ixs} → (x : Type)
          → nat-η ([ P₁ {i} {j} ]₁ tt) x ∘F join {x} {j} {i} {i} ∘F fmap {j} {i} (return {x}) 
          ≡ (λ x → x)
η-lax-id₁ {i} {j} x = η-extract ⟨ [ P₁ {i} {j} ]₁ tt ⟩∘ᵥ⟨ ⟨ μ {i} {i} {j} ⟩∘ᵥ⟨ ⟨ Id⟨ [ P₁ {i} {j} ]₀ (lift tt) ⟩ ⟩∘ₕ⟨ η {i} ⟩ ⟩ ⟩ 
                                (StrictTwoCategory.λ' Cat' ([ P₁ {i} {j} ]₀ (lift tt))) 
                                (laxFunId₁ {i} {j} {lift tt}) x

η-lax-id₂ : {i j : Ixs} → (x : Type)
          → nat-η ([ P₁ {i} {j} ]₁ tt) x ∘F join {x} {j} {j} {i} ∘F return {M j i x}
          ≡ nat-η (ρ Cat' ([ P₁ {i} {j} ]₀ (lift tt))) x
η-lax-id₂ {i} {j} x = η-extract ( ⟨ [ P₁ {i} {j} ]₁ tt ⟩∘ᵥ⟨ ⟨ μ {i} {j} {j} {lift tt} {id₁ S₂ {j}} ⟩∘ᵥ⟨ ⟨ η {j} ⟩∘ₕ⟨ id₂ Cat' {f = [ P₁ {i} {j} ]₀ (lift tt)} ⟩ ⟩ ⟩ )
                                (StrictTwoCategory.ρ Cat' ([ P₁ {i} {j} ]₀ (lift tt))) 
                                (laxFunId₂ {i} {j} {lift tt}) x
    
--_∘Dᵥ_ = StrictTwoCategory._∘ᵥ_ Cat'
--_∘Dₕ₂_ = StrictTwoCategory._∘ₕ₂_ Cat' -- l k  (k j )
    
    
η-lax-assoc : {i j k l : Ixs} (x : Type)
            → nat-η ([ P₁ {i} {l} ]₁ tt) x ∘F join {x} {l} {k} {i} ∘F fmap {l} {k} (join {x} {k} {j} {i})
            ≡ join {x} {l} {j} {i} ∘F join {M j i x} {l} {k} {j} ∘F fmap {l} {k} (fmap {k} {j} (λ x → x)) ∘F nat-η (α Cat' ([ P₁ {i} {j} ]₀ (lift tt)) ([ P₁ {j} {k} ]₀ (lift tt)) ([ P₁ {k} {l} ]₀ (lift tt))) x
η-lax-assoc {i} {j} {k} {l} x = η-extract ( ⟨ [ P₁ {i} {l} ]₁ tt ⟩∘ᵥ⟨ ⟨ μ {i} {k} {l} {lift tt} {lift tt} ⟩∘ᵥ⟨ ⟨ id₂ Cat' {Hask} {Hask} {[ P₁ {k} {l} ]₀ (lift tt)} ⟩∘ₕ⟨ μ {i} {j} {k} {lift tt} {lift tt} ⟩ ⟩ ⟩ )
                                          ( ⟨ μ {i} {j} {l} {lift tt} {lift tt} 
                                            ⟩∘ᵥ⟨ ⟨ ⟨ μ {j} {k} {l} {lift tt} {lift tt} ⟩∘ₕ⟨ id₂ Cat' {Hask} {Hask} {[ P₁ {i} {j} ]₀ (lift tt)} ⟩ 
                                                 ⟩∘ᵥ⟨ α Cat' ([ P₁ {i} {j} ]₀ (lift tt)) ([ P₁ {j} {k} ]₀ (lift tt)) ([ P₁ {k} {l} ]₀ (lift tt)) ⟩ 
                                            ⟩) 
                                            (laxFunAssoc {i} {j} {k} {l} {lift tt}) x


join-assoc : {i j k l : Ixs} (x : Type) 
           → join {x} {l} {k} {i} ∘F fmap {l} {k} (join {x} {k} {j} {i}) 
           ≡ join {x} {l} {j} {i} ∘F join {M j i x} {l} {k} {j} ∘F fmap {l} {k} (fmap {k} {j} (λ x → x))
join-assoc {i} {j} {k} {l} x = begin
  join {x} {l} {k} {i} ∘F fmap {l} {k} (join {x} {k} {j} {i}) 
    ≡⟨ cong (λ X → nat-η X x ∘F join {x} {l} {k} {i} ∘F fmap {l} {k} (join {x} {k} {j} {i})) (sym (Functor.id (P₁ {i} {l}))) ⟩
  nat-η ([ P₁ {i} {l} ]₁ tt) x ∘F join {x} {l} {k} {i} ∘F fmap {l} {k} (join {x} {k} {j} {i})
    ≡⟨ η-lax-assoc {i} {j} {k} {l} x ⟩
  join {x} {l} {j} {i} ∘F join {M j i x} {l} {k} {j} ∘F fmap {l} {k} (fmap {k} {j} (λ x → x)) ∘F nat-η (α Cat' ([ P₁ {i} {j} ]₀ (lift tt)) ([ P₁ {j} {k} ]₀ (lift tt)) ([ P₁ {k} {l} ]₀ (lift tt))) x
    ≡⟨ cong (λ X → join {x} {l} {j} {i} ∘F join {M j i x} {l} {k} {j} ∘F fmap {l} {k} (fmap {k} {j} (λ x → x)) ∘F X) (≅-to-≡ (α-id {i} {j} {k} {l} x)) ⟩
  join {x} {l} {j} {i} ∘F join {M j i x} {l} {k} {j} ∘F fmap {l} {k} (fmap {k} {j} (λ x → x) ∘F (λ (y : M k j (M j i x)) → y)) ∎

join-return-id : {i j : Ixs} → (x : Type) → join {x} {j} {j} {i} ∘F return {M j i x} ≡ (λ (y : M j i x) → y)
join-return-id {i} {j} x = begin
  join {x} {j} {j} {i} ∘F return {M j i x} 
    ≡⟨ refl ⟩
  nat-η (Id⟨ [ P₁ {i} {j} ]₀ (lift tt) ⟩) x ∘F join {x} {j} {j} {i} ∘F return {M j i x} 
    ≡⟨ cong (λ X → nat-η X x ∘F join {x} {j} {j} {i} ∘F return {M j i x} ) (sym (Functor.id (P₁ {i} {j}))) ⟩
  nat-η ([ P₁ {i} {j} ]₁ (ρ S₂ {i} {j} (lift tt))) x ∘F join {x} {j} {j} {i} ∘F return {M j i x} 
    ≡⟨ η-lax-id₂ {i} {j} x ⟩
  nat-η (ρ Cat' ([ P₁ {i} {j} ]₀ (lift tt))) x
    ≡⟨ ≅-to-≡ (ρ-id {i} {j} x) ⟩
  (λ (y : M j i x) → y) ∎
