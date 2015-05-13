
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
    -- Enumerations/Names of bind operators
    B[_,_]▷_ : (M N P : TyCons) → Set l

    -- Interpretation of unary type constructors
    ⟨_⟩ : TyCons → TyCon
    
    -- Interpretation of bind operators
    bind : {M N P : TyCons} → B[ M , N ]▷ P → [ ⟨ M ⟩ , ⟨ N ⟩ ]▷ ⟨ P ⟩
    
    -- Law of the Id type constructor: Id τ = τ
    lawId : ⟨ Id ⟩ ≡ Identity
    
    -- Functor law from the paper
    lawFunctor : ∀ (M : TyCons) → ∃ λ(b : B[ M , Id ]▷ M) 
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
    -- Equation from the paired morphism law:
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
               (b₁ : B[ M , N ]▷ P) (b₂ : B[ P , R ]▷ T) 
               (b₃ : B[ N , R ]▷ S) (b₄ : B[ M , S ]▷ T)
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

-- Access to id function of a polymonad
--pmId→ = Polymonad.id

-- Interpretation of a type constructor for a specific polymonad.
⟨_▷_⟩ : ∀ {l} {TyCons : Set l} {Id : TyCons} → Polymonad TyCons Id → TyCons → TyCon
⟨ pm ▷ tyCon ⟩ = (Polymonad.⟨_⟩ pm) tyCon

-- Bind identifier set for a combination of type constructors in a specific polymonad. 
B[_,_]_▷_ : ∀ {TyCons} {Id : TyCons} → (M N : TyCons) → Polymonad TyCons Id → (P : TyCons) → Set
B[ M , N ] pm ▷ P = Polymonad.B[_,_]▷_ pm M N P

-- Actuall bind operator for a bind identifier.
pmBind = Polymonad.bind

-- Access to the identity law.
pmLawId = Polymonad.lawId

-- Access to the functor law.
pmLawFunctor = Polymonad.lawFunctor

pmGetFunctor : ∀ {TyCons : Set} {Id : TyCons} → (pm : Polymonad TyCons Id) → (M : TyCons) → B[ M , Id ] pm ▷ M
pmGetFunctor pm M = let b , p = pmLawFunctor pm M in b

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

-- There always is at least one identity bind operator.
pmIdBind∃ : {TyCons : Set} {Id : TyCons}
          → (pm : Polymonad TyCons Id)
          → B[ Id , Id ] pm ▷ Id
pmIdBind∃ {Id = Id} pm = proj₁ (pmLawFunctor pm Id)

{-
pmReturn∃ : {TyCons : Set} → (pm : Polymonad (IdTyCons ⊎ TyCons) idTC) → (M : TyCons) → B[ idTC , idTC ] pm ▷ (inj₂ M)
pmReturn∃ = ?
-}
{-
pmReturn∃ : {TyCons : Set} {Id : TyCons} → (pm : Polymonad TyCons Id) → (M : TyCons) → B[ Id , Id ] pm ▷ M
pmReturn∃ {Id = Id} pm M with pmLawDiamond1 pm M Id Id M (M , (proj₁ (pmLawFunctor pm M)) , (proj₁ (pmLawFunctor pm M)))
pmReturn∃ pm M | S , retS , morphS = {!!}
-}
