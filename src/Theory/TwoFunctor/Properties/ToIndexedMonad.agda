
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
open import Theory.Functor.Properties.IsomorphicHaskellFunctor
open import Theory.Natural.Transformation
open import Theory.Natural.Transformation.Examples
open import Theory.TwoCategory.Definition
open import Theory.TwoCategory.Examples.Functor
open import Theory.TwoCategory.Examples.CodiscreteHomCat
open import Theory.TwoCategory.ExampleProperties
open import Theory.TwoFunctor.ConstZeroCell

open Category
open StrictTwoCategory

module Theory.TwoFunctor.Properties.ToIndexedMonad where

LaxTwoFunctor→IxMonadTyCon : {ℓS : Level}
  → (S : Set ℓS)
  → (F : ConstLaxTwoFunctor (codiscreteHomCatTwoCategory (codiscreteCategory S)) (Cat {suc zero} {zero}) (Hask {zero}))
  → ( S → S → TyCon )
LaxTwoFunctor→IxMonadTyCon S F i j A = [ [ ConstLaxTwoFunctor.P₁ F {j} {i} ]₀ (lift tt) ]₀ A

LaxTwoFunctor→IndexedMonad
  : {ℓS : Level}
  → (S : Set ℓS)
  → (F : ConstLaxTwoFunctor (codiscreteHomCatTwoCategory (codiscreteCategory S)) (Cat {suc zero} {zero}) (Hask {zero}))
  → IxMonad S (LaxTwoFunctor→IxMonadTyCon S F)
LaxTwoFunctor→IndexedMonad {ℓS} ObjS F 
  = indexed-monad _>>=_ return functor law-left-id law-right-id law-assoc law-monad-fmap
  where
    open ConstLaxTwoFunctor F
    open NaturalTransformation renaming (η to nat-η)
    
    import Theory.TwoFunctor.Properties.ToIndexedMonadProperties
    open Theory.TwoFunctor.Properties.ToIndexedMonadProperties {ℓS} ObjS F
    
    S : Category
    S = codiscreteCategory ObjS
    
    S₂ = codiscreteHomCatTwoCategory S
    Cat' = Cat {suc zero} {zero}

    Ixs = Obj S
    
    M : Ixs → Ixs → TyCon
    M = LaxTwoFunctor→IxMonadTyCon ObjS F
    
    fmap : {i j : Ixs} {α β : Type} → (α → β) → M i j α → M i j β
    fmap {i} {j} = [ [ P₁ {j} {i} ]₀ (lift tt) ]₁
    
    functor : (i j : Ixs) → HaskellFunctor (LaxTwoFunctor→IxMonadTyCon ObjS F i j)
    functor i j = Functor→HaskellFunctor ([ P₁ {j} {i} ]₀ (lift tt))
    
    return : {α : Type} {i : Ixs} → α → M i i α
    return {α} {i} a = nat-η (η {i}) α a

    join : {α : Type} {i j k : Ixs} → M i j (M j k α) → M i k α
    join {α} {i} {j} {k} mma = nat-η (μ {k} {j} {i}) α mma 
     
    _>>=_ : {α β : Type} {i j k : Ixs} → M i j α → (α → M j k β) → M i k β
    _>>=_ {α} {β} {i} {j} {k} ma f = join (fmap f ma)
    
    abstract
      natural-μ : {i j k : Ixs} → (α β : Type) → (f : α → β) 
                → (fmap {i} {k} f) ∘F (join {α} {i} {j} {k}) ≡ join {β} {i} {j} {k} ∘F fmap {i} {j} (fmap {j} {k} f) 
      natural-μ {i} {j} {k} a b f = natural (μ {k} {j} {i}) {a = a} {b} {f} 
    
    abstract
      natural-η : {i : Ixs} → (α β : Type) → (f : α → β) 
                → (fmap {i} {i} f) ∘F (return {α} {i}) ≡ return {β} {i} ∘F f 
      natural-η {i} a b f = natural (η {i}) {a = a} {b} {f} 
    
    abstract
      law-left-id : {α β : Type} {i j : ObjS} → (a : α) → (k : α → M i j β) → return a >>= k ≡ k a
      law-left-id {α} {β} {i} {j} a k = begin
        return a >>= k 
          ≡⟨⟩
        (join ∘F fmap k ∘F return) a
          ≡⟨ cong (λ X → (join ∘F X) a) (natural-η α (M i j β) k) ⟩
        (join ∘F return ∘F k) a
          ≡⟨⟩
        (join ∘F return) (k a)
          ≡⟨ cong (λ X → X (k a)) (join-return-id {j} {i} β) ⟩
        k a ∎
    
    abstract
      law-right-id : {α : Type} {i j : Ixs} → (m : M i j α) → m >>= return ≡ m
      law-right-id {α} {i} {j} m = begin
        m >>= return 
          ≡⟨ refl ⟩ 
        (join {α} {i} {j} {j} ∘F fmap {i} {j} (return {α})) m 
          ≡⟨ refl ⟩ 
        (nat-η (Id⟨ [ P₁ {j} {i} ]₀ (lift tt) ⟩) α ∘F join {α} {i} {j} {j} ∘F fmap {i} {j} (return {α})) m
          ≡⟨ cong (λ X → (nat-η X α ∘F join {α} {i} {j} {j} ∘F fmap {i} {j} (return {α})) m) (sym (Functor.id (P₁ {j} {i}))) ⟩ 
        (nat-η ([ P₁ {j} {i} ]₁ (lift tt)) α ∘F join {α} {i} {j} {j} ∘F fmap {i} {j} (return {α})) m
          ≡⟨ cong (λ X → X m) (η-lax-id₁ {j} {i} α) ⟩ 
        nat-η (λ' Cat' ([ P₁ {j} {i} ]₀ (lift tt))) α m
          ≡⟨ ≅-to-≡ (het-cat-λ-id α m) ⟩ 
        m ∎
    
    abstract
      law-right-id' : {α : Type} {i j : Ixs} → join {α} {i} {j} {j} ∘F fmap {i} {j} (return {α}) ≡ (λ (x : M i j α) → x)
      law-right-id' {α} {i} {j} = fun-ext $ λ m → law-right-id {α} {i} {j} m
    
    abstract
      law-assoc : {α β γ : Type} {i j k l : ObjS} 
                → (m : M i j α) (f : α → M j k β) (g : β → M k l γ) 
                → m >>= (λ x → f x >>= g) ≡ (m >>= f) >>= g
      law-assoc {α} {β} {γ} {i} {j} {k} {l} m f g = begin
        (join ∘F fmap (join ∘F fmap g ∘F f)) m
          ≡⟨ cong (λ X → (join ∘F X) m) (Functor.compose ([ P₁ {j} {i} ]₀ (lift tt))) ⟩ 
        (join ∘F fmap join ∘F fmap (fmap g ∘F f)) m
          ≡⟨ cong (λ X → (join ∘F fmap join ∘F X) m) (Functor.compose ([ P₁ {j} {i} ]₀ (lift tt))) ⟩ 
        (join ∘F fmap join ∘F fmap (fmap g) ∘F fmap f) m
          ≡⟨ cong (λ X → (X ∘F fmap (fmap g) ∘F fmap f) m) (join-assoc γ) ⟩ 
        (join ∘F join ∘F fmap (fmap (λ x → x)) ∘F fmap (fmap g) ∘F fmap f) m
          ≡⟨ cong (λ X → (join ∘F join ∘F fmap X ∘F fmap (fmap g) ∘F fmap f) m) (Functor.id ([ P₁ {k} {j} ]₀ (lift tt))) ⟩
        (join ∘F join ∘F fmap (λ x → x) ∘F fmap (fmap g) ∘F fmap f) m
          ≡⟨ cong (λ X → (join ∘F join ∘F X ∘F fmap f) m) (sym (Functor.compose ([ P₁ {j} {i} ]₀ (lift tt)))) ⟩
        (join ∘F join ∘F fmap (fmap g) ∘F fmap f) m
          ≡⟨ cong (λ X → (join ∘F X ∘F fmap f) m) (sym (natural-μ β (M k l γ) g)) ⟩ 
        (join ∘F fmap g ∘F join ∘F fmap f) m ∎
    
    abstract
      law-monad-fmap : {α β : Type} {i j : ObjS} → (f : α → β) (ma : M i j α)
                     → ma >>= (return ∘F f) ≡ fmap {i} {j} f ma
      law-monad-fmap {α} {β} {i} {j} f ma = begin
        (join ∘F fmap (return ∘F f)) ma 
          ≡⟨ cong (λ X → (join ∘F X) ma) (Functor.compose ([ P₁ {j} {i} ]₀ (lift tt))) ⟩
        (join ∘F fmap return ∘F fmap f) ma 
          ≡⟨ cong (λ X → (X ∘F fmap f) ma) law-right-id' ⟩
        fmap {i} {j} f ma ∎

    
  
