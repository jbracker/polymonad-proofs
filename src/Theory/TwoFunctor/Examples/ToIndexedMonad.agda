
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
-- open ≅-Reasoning hiding ( _≡⟨_⟩_ ) renaming ( begin_ to hbegin_ ; _∎ to _∎h)

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

open Category
open StrictTwoCategory

module Theory.TwoFunctor.Examples.ToIndexedMonad where

LaxTwoFunctor→IxMonadTyCon : {ℓS : Level}
  → (S : Set ℓS)
  → (F : ConstLaxTwoFunctor (Category→StrictTwoCategory (codiscreteCategory S)) (Cat {suc zero} {zero}) (Hask {zero}))
  → ( S → S → TyCon )
LaxTwoFunctor→IxMonadTyCon S F i j A = [ [ ConstLaxTwoFunctor.P₁ F {j} {i} ]₀ (lift tt) ]₀ A


LaxTwoFunctor→IndexedMonad
  : {ℓS : Level}
  → (S : Set ℓS)
  → (F : ConstLaxTwoFunctor (Category→StrictTwoCategory (codiscreteCategory S)) (Cat {suc zero} {zero}) (Hask {zero}))
  → IxMonad S (LaxTwoFunctor→IxMonadTyCon S F)
LaxTwoFunctor→IndexedMonad ObjS F 
  = indexed-monad _>>=_ return functor law-left-id law-right-id law-assoc law-monad-fmap
  where
    open ConstLaxTwoFunctor F
    open NaturalTransformation renaming (η to nat-η)
    
    S : Category
    S = codiscreteCategory ObjS
    
    S₂ = Category→StrictTwoCategory S
    Cat' = Cat {suc zero} {zero}

    Ixs = Obj S
    
    M : Ixs → Ixs → TyCon
    M = LaxTwoFunctor→IxMonadTyCon ObjS F
    
    fmap : {i j : Ixs} {α β : Type} → (α → β) → M i j α → M i j β
    fmap {i} {j} = [ [ P₁ {j} {i} ]₀ (lift tt) ]₁
    
    functor : (i j : Ixs) → HaskellFunctor (LaxTwoFunctor→IxMonadTyCon ObjS F i j)
    functor i j = Functor.functor (fmap {i} {j}) 
                                  (Functor.id ([ P₁ {j} {i} ]₀ (lift tt)))
                                  (λ g f → Functor.compose ([ P₁ {j} {i} ]₀ (lift tt)) {f = f} {g = g})
    
    return : {α : Type} {i : Ixs} → α → M i i α
    return {α} {i} a = nat-η (η {i}) α a

    join : {α : Type} {i j k : Ixs} → M i j (M j k α) → M i k α
    join {α} {i} {j} {k} mma = nat-η (μ {k} {j} {i}) α mma 
     
    _>>=_ : {α β : Type} {i j k : Ixs} → M i j α → (α → M j k β) → M i k β
    _>>=_ {α} {β} {i} {j} {k} ma f = join (fmap f ma)
    
    natural-μ : {i j k : Ixs} → (α β : Type) → (f : α → β) 
              → (fmap {i} {k} f) ∘F (join {α} {i} {j} {k}) 
              ≡ join {β} {i} {j} {k} ∘F fmap {i} {j} (fmap {j} {k} f) 
              {-
              → ([ [ P₁ {i} {k} ]₀ (lift tt) ]₁ f) ∘F (nat-η (μ {i} {j} {k}) a) 
              ≡ (nat-η (μ {i} {j} {k}) b) ∘F ([ [ P₁ {j} {k} ]₀ (lift tt) ]₁ ([ [ P₁ {i} {j} ]₀ (lift tt) ]₁ f)) 
              -}
    natural-μ {i} {j} {k} a b f = natural (μ {k} {j} {i}) {a = a} {b} {f} 
    
    natural-η : {i : Ixs} → (α β : Type) → (f : α → β) 
              → (fmap {i} {i} f) ∘F (return {α} {i}) 
              ≡ return {β} {i} ∘F f 
    natural-η {i} a b f = natural (η {i}) {a = a} {b} {f} 
    
    law-left-id : {α β : Type} {i j : ObjS} → (a : α) → (k : α → M i j β) → return a >>= k ≡ k a
    law-left-id {α} {β} {i} {j} a k = begin
      return a >>= k 
        ≡⟨⟩
      (join ∘F fmap k ∘F return) a
        ≡⟨ cong (λ X → (join ∘F X) a) (natural-η α (M i j β) k) ⟩
      (join ∘F return ∘F k) a
        ≡⟨⟩
      (join ∘F return) (k a)
      --  ≡⟨⟩
      --(nat-η (μ {j} {i} {i}) β ∘F [ [ P₁ {i} {i} ]₀ (lift tt) ]₁ k ∘F nat-η (η {i}) α) a 
        ≡⟨ {!!} ⟩
      k a ∎

{-
natural : {a b : Obj C} {f : Hom C a b} 
            → ([ G ]₁ f) ∘D (η a) ≡ (η b) ∘D ([ F ]₁ f)
            -- G₁ f ∘ η ≡ η ∘ F₁ f
-}
    
    law-right-id : {α : Type} {i j : ObjS} → (m : M i j α) → m >>= return ≡ m
    law-right-id m = {!!}
    
    law-assoc : {α β γ : Type} {i j k l : ObjS} 
              → (m : M i j α) (f : α → M j k β) (g : β → M k l γ) 
              → m >>= (λ x → f x >>= g) ≡ (m >>= f) >>= g
    law-assoc ma f g = {!!}
    
    law-monad-fmap : {α β : Type} {i j : ObjS} → (f : α → β) (ma : M i j α)
                   → ma >>= (return ∘F f) ≡ fmap {i} {j} f ma
    law-monad-fmap f ma = {!!}
    
    _∘Dᵥ_ = StrictTwoCategory._∘ᵥ_ Cat'
    _∘Dₕ₂_ = StrictTwoCategory._∘ₕ₂_ Cat'
    

    lax-id₁ : {i j : Ixs} 
            → ⟨ [ P₁ {i} {j} ]₁ tt ⟩∘ᵥ⟨ ⟨ μ {i} {i} {j} ⟩∘ᵥ⟨ ⟨ Id⟨ [ P₁ {i} {j} ]₀ (lift tt) ⟩ ⟩∘ₕ⟨ η {i} ⟩ ⟩ ⟩
            ≡ StrictTwoCategory.λ' Cat' ([ P₁ {i} {j} ]₀ (lift tt))
    lax-id₁ {i} {j} = laxFunId₁ {i} {j} {lift tt}
    
    η-extract : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}} {F G : Functor C D} 
              → (NT₀ NT₁ : NaturalTransformation F G) 
              → NT₀ ≡ NT₁ 
              → (x : Category.Obj C) 
              → nat-η NT₀ x ≡ nat-η NT₁ x
    η-extract NT₀ .NT₀ refl x = refl
    {-
η : (c : Obj C) → Hom E ([ [ G ]∘[ F ] ]₀ c) ([ [ G' ]∘[ F' ] ]₀ c)
    η c = ηα ([ F' ]₀ c) ∘E [ G ]₁ (ηβ c)
-}
-- nat-η (⟨ Id⟨ [ P₁ {i} {j} ]₀ (lift tt) ⟩ ⟩∘ₕ⟨ η {i} ⟩) x
-- nat-η (Id⟨ [ P₁ {i} {j} ]₀ (lift tt) ⟩) ([ ? ]₀ x) ∘F [ ? ]₀ (nat-η (η {i}) x)

    η-lax-id₁ : {i j : Ixs} → (x : Type)
            → nat-η ([ P₁ {i} {j} ]₁ tt) x ∘F join {x} {j} {i} {i} ∘F fmap {j} {i} (return {x}) ≡ (λ x → x)
    η-lax-id₁ {i} {j} x = η-extract ⟨ [ P₁ {i} {j} ]₁ tt ⟩∘ᵥ⟨ ⟨ μ {i} {i} {j} ⟩∘ᵥ⟨ ⟨ Id⟨ [ P₁ {i} {j} ]₀ (lift tt) ⟩ ⟩∘ₕ⟨ η {i} ⟩ ⟩ ⟩ 
                                    (StrictTwoCategory.λ' Cat' ([ P₁ {i} {j} ]₀ (lift tt))) 
                                    (laxFunId₁ {i} {j} {lift tt}) x
    {-
    laxFunId₁ : {x y : Cell₀ C} {f : Cell₁ C x y} 
              → ([ P₁ {x} {y} ]₁ (λ' C f)) 
            ∘Dᵥ ( (μ {x} {x} {y} {id₁ C {x}} {f}) 
            ∘Dᵥ   (id₂ D {f = [ P₁ {x} {y} ]₀ f} ∘Dₕ₂ η {x}) )
              ≡ λ' D ([ P₁ {x} {y} ]₀ f)
    
    laxFunId₂ : {x y : Cell₀ C} {f : Cell₁ C x y} 
              → ([ P₁ {x} {y} ]₁ (ρ C f)) 
            ∘Dᵥ ( (μ {x} {y} {y} {f} {id₁ C {y}}) 
            ∘Dᵥ   (η {y} ∘Dₕ₂ id₂ D {f = [ P₁ {x} {y} ]₀ f}) ) 
              ≡ ρ D ([ P₁ {x} {y} ]₀ f)

    laxFunAssoc : {w x y z : Cell₀ C} {f : Cell₁ C w x} {g : Cell₁ C x y} {h : Cell₁ C y z}
               → ([ P₁ {w} {z} ]₁ (α C f g h)) 
             ∘Dᵥ ( (μ {w} {y} {z} {g ∘Cₕ f} {h}) 
             ∘Dᵥ   (id₂ D {P₀ y} {P₀ z} {[ P₁ {y} {z} ]₀ h} ∘Dₕ₂ μ {w} {x} {y} {f} {g}) ) 
               ≡ μ {w} {x} {z} {f} {h ∘Cₕ g} 
             ∘Dᵥ ( (μ {x} {y} {z} {g} {h} ∘Dₕ₂ id₂ D {P₀ w} {P₀ x} {[ P₁ {w} {x} ]₀ f}) 
             ∘Dᵥ   (α D ([ P₁ {w} {x} ]₀ f) ([ P₁ {x} {y} ]₀ g) ([ P₁ {y} {z} ]₀ h)) )
-}
