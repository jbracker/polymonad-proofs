
module Polymonad where

-- Stdlib
open import Agda.Primitive
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Local
open import Utilities
open import Haskell
open import Identity
    
--------------------------------------------------------------------------------
-- Polymonad Definition
--------------------------------------------------------------------------------

record Polymonad {l : Level} (TyCons : Set l) (Id : TyCons) : Set (lsuc l) where
  field
    -- Set of bind-operation names for each combination of type constructors.
    B[_,_]▷_ : (M N P : TyCons) → Set l

    -- Interpretation of type constructor names into actual type constructors.
    ⟨_⟩ : TyCons → TyCon
    
    -- Interpretation of bind-operation names into actual bind-operations.
    bind : {M N P : TyCons} → B[ M , N ]▷ P → [ ⟨ M ⟩ , ⟨ N ⟩ ]▷ ⟨ P ⟩
    
    -- Law of the Id type constructor: Id τ = τ
    lawId : ⟨ Id ⟩ ≡ Identity
    
    -- Functor law from the definition:
    -- There exists a functor bind-operation for each type constructor:
    lawFunctor1 : ∀ (M : TyCons) → B[ M , Id ]▷ M 
    -- Every bind-operation in shape of a functor needs to be an identity:
    lawFunctor2 : ∀ (M : TyCons) → ∀ (b : B[ M , Id ]▷ M)
                → ∀ {α : Type} (m : ⟨ M ⟩ α) → (bind b) m (id lawId) ≡ m
    
    -- Paired morphism law from the definition:
    -- ∃ b₁:(M,Id)▷N ∈ Σ ⇔ ∃ b₂:(Id,M)▷N ∈ Σ
    -- and ∀ b₁:(M,Id)▷N, b₂:(Id,M)▷N . b₁ (f v) (λy.y) = b₂ v f

    -- Left to right direction of the paired morphism law equivalancy:
    lawMorph1 : ∀ (M N : TyCons) 
              → (B[ M , Id ]▷ N → B[ Id , M ]▷ N)
    -- Right to left direction of the paired morphism law equivalancy:
    lawMorph2 : ∀ (M N : TyCons) 
              → (B[ Id , M ]▷ N → B[ M , Id ]▷ N)
    -- Equation of the paired morphism law:
    lawMorph3 : ∀ (M N : TyCons) (b₁ : B[ M , Id ]▷ N) (b₂ : B[ Id , M ]▷ N)
              → ∀ {α β : Type} (v : α) (f : α → ⟨ M ⟩ β) 
              → (bind b₁) (f v) (id lawId) ≡ (bind b₂) ((id lawId) v) f
    
    -- Diamond law from the definition:
    -- ( ∃ P, b₁, b₂ . { b₁:(M,N)▷P, b₂:(P,R)▷T } ⊆ Σ ) ⇔
    -- ( ∃ S, b₃, b₄ . { b₃:(N,R)▷S, b₄:(M,S)▷T } ⊆ Σ )
    
    -- Left to right direction of the diamond law equivalancy:
    lawDiamond1 : ∀ (M N R T : TyCons)
                → (∃ λ(P : TyCons) → B[ M , N ]▷ P × B[ P , R ]▷ T)
                → (∃ λ(S : TyCons) → B[ N , R ]▷ S × B[ M , S ]▷ T)
    -- Right to left direction of the diamond law equivalancy:
    lawDiamond2 : ∀ (M N R T : TyCons)
                → (∃ λ(S : TyCons) → B[ N , R ]▷ S × B[ M , S ]▷ T)
                → (∃ λ(P : TyCons) → B[ M , N ]▷ P × B[ P , R ]▷ T)
    
    -- Associativity law from the definition:
    -- ∀ b₁, b₂, b₃, b₄ . 
    -- "If" { b₁:(M,N)▷P, b₂:(P,R)▷T, b₃:(N,R)▷S, b₄:(M,S)▷T } ⊆ Σ
    -- "then" b₂ (b₁ m f) g = b₄ m (λ x . b₃ (f x) g)
    lawAssoc : ∀ (M N P R T S : TyCons) 
             → (b₁ : B[ M , N ]▷ P) → (b₂ : B[ P , R ]▷ T) 
             → (b₃ : B[ N , R ]▷ S) → (b₄ : B[ M , S ]▷ T)
             → ∀ {α β γ : Type} (m : ⟨ M ⟩ α) (f : α → ⟨ N ⟩ β) (g : β → ⟨ R ⟩ γ)
             → (bind b₂) ((bind b₁) m f) g ≡ (bind b₄) m (λ x → (bind b₃) (f x) g)
    
    -- Closure law from the definition:
    -- "If" ∃ b₁, b₂, b₃, b₄ .
    -- { b₁:(M,N)▷P, b₂:(S,Id)▷M, b₃:(T,Id)▷N, b₄:(P,Id)▷U } ⊆ Σ
    -- "then" ∃ b . b:(S,T)▷U ∈ Σ
    lawClosure : ∀ (M N P S T U : TyCons)
               → ( B[ M , N ]▷ P × B[ S , Id ]▷ M × B[ T , Id ]▷ N × B[ P , Id ]▷ U )
               → B[ S , T ]▷ U

  pmId : TyCons
  pmId = Id

--------------------------------------------------------------------------------
-- Polymonad Accessor/Utility Functions
--------------------------------------------------------------------------------

-- Access to Id TyCon of a polymonad
pmId = Polymonad.pmId

-- Interpretation of a type constructor name for a specific polymonad.
⟨_▷_⟩ : ∀ {l} {TyCons : Set l} {Id : TyCons} → Polymonad TyCons Id → TyCons → TyCon
⟨ pm ▷ tyCon ⟩ = (Polymonad.⟨_⟩ pm) tyCon

-- Set of bind-operation names for a combination of type constructors in a specific polymonad.
B[_,_]_▷_ : ∀ {l} {TyCons : Set l} {Id : TyCons} 
          → (M N : TyCons) → Polymonad TyCons Id → (P : TyCons) → Set l
B[ M , N ] pm ▷ P = Polymonad.B[_,_]▷_ pm M N P

-- Actuall bind operator for a bind identifier.
pmBind = Polymonad.bind

-- Access to the identity law.
pmLawId = Polymonad.lawId

-- Access to the functor law.
pmLawFunctor1 = Polymonad.lawFunctor1
pmLawFunctor2 = Polymonad.lawFunctor2

pmGetFunctor = pmLawFunctor1

pmLawMorph1 = Polymonad.lawMorph1
pmLawMorph2 = Polymonad.lawMorph2
pmLawMorph3 = Polymonad.lawMorph3

pmLawDiamond1 = Polymonad.lawDiamond1
pmLawDiamond2 = Polymonad.lawDiamond2

pmLawAssoc = Polymonad.lawAssoc

pmLawClosure = Polymonad.lawClosure

--------------------------------------------------------------------------------
-- Polymonad General Lemmas
--------------------------------------------------------------------------------

-- We can always lift a value into the identity tycon of a polymonad.
pmIdLift : ∀ {ℓ} {TyCons : Set ℓ} {Id : TyCons}
         → (pm : Polymonad TyCons Id)
         → ∀ {α : Type}
         → α → ⟨ pm ▷ Id ⟩ α
pmIdLift pm {α = α} a = subst (λ X → X) (sym (cong (λ M → M α) (pmLawId pm))) a

-- There always is at least one identity bind operator.
pmIdBind∃ : {TyCons : Set} {Id : TyCons}
          → (pm : Polymonad TyCons Id)
          → B[ Id , Id ] pm ▷ Id
pmIdBind∃ {Id = Id} pm = pmLawFunctor1 pm Id

