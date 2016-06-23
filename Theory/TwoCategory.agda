
module Theory.TwoCategory where

-- Stdlib
open import Level renaming ( suc to lsuc ; zero to lzero )
open import Function hiding ( id ) renaming ( _∘_ to _∘F_ )
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Local
open import Theory.Category
open import Theory.Functor
open import Theory.NaturalTransformation
open import Theory.Examples.Functor

-------------------------------------------------------------------------------
-- Definition of 2-Categories
-------------------------------------------------------------------------------
open Category hiding ( idL ; idR ; assoc ) renaming ( id to idC )

record StrictTwoCategory {ℓ₀ ℓ₁ ℓ₂ : Level} : Set (lsuc (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    Cell₀ : Set ℓ₀
    HomCat : Cell₀ → Cell₀ → Category {ℓ₁} {ℓ₂}

    --                       (b c × a b ↦ a c)
    comp : {a b c : Cell₀} → Functor (HomCat b c ×C HomCat a b) (HomCat a c) 
    id₁  : {a : Cell₀} → Obj (HomCat a a)
    
    idL : {a b : Cell₀} 
        -- (a b × a a ↦ a b)  ∘  (a b ↦ a b × a a)
        → [ comp {a} {a} {b} ]∘[ [ Id[ HomCat a b ] ◁ HomCat a a , id₁ {a} ] ]
        -- (a b ↦ a b) 
        ≡ Id[ HomCat a b ]
    idR : {a b : Cell₀}
        -- (b b × a b ↦ a b)  ∘  (a b ↦ b b × a b)
        → [ comp {a} {b} {b} ]∘[ [ HomCat b b , id₁ {b} ▷ Id[ HomCat a b ] ] ] 
        -- (a b ↦ a b)
        ≡ Id[ HomCat a b ]
    
    assoc : {a b c d : Cell₀}
          -- (c d × a c → a d)  ∘  (c d × (b c × a c) ↦ c d × a c)             ∘ (c d × b c × a b ↦ c d × (b c × a b))
          → [ comp {a} {c} {d} ]∘[ [ [ Id[ HomCat c d ] ]×[ comp {a} {b} {c} ] ]∘[ A×B×C→A×[B×C] ] ] 
          -- (b d × a b ↦ a d)  ∘  ((c d × b c) × a b ↦ b d × a b)             ∘ (c d × b c × a b ↦ (c d × b c) × a b)
          ≡ [ comp {a} {b} {d} ]∘[ [ [ comp {b} {c} {d} ]×[ Id[ HomCat a b ] ] ]∘[ A×B×C→[A×B]×C ] ]

  Cell₁ : Cell₀ → Cell₀ → Set ℓ₁
  Cell₁ a b = Obj (HomCat a b)
  
  Cell₂ : {a b : Cell₀} → (f g : Cell₁ a b) → Set ℓ₂
  Cell₂ {a} {b} f g = Hom (HomCat a b) f g
  
  -- Horizontal composition
  _∘ₕ_ : {a b c : Cell₀} → Cell₁ b c → Cell₁ a b → Cell₁ a c
  _∘ₕ_ f g = [ comp ]₀ (f , g)

  -- Vertical composition
  _∘ᵥ_ : {a b : Cell₀} {f g h : Cell₁ a b} → Cell₂ g h → Cell₂ f g → Cell₂ f h
  _∘ᵥ_ {a = a} {b = b} η θ = Category._∘_ (HomCat a b) η θ
  
  -- Right whiskering
  _▷_ : {a b c : Cell₀} {f g : Cell₁ a b} 
      → (h : Cell₁ b c) → Cell₂ f g → Cell₂ (h ∘ₕ f) (h ∘ₕ g)
  _▷_ {b = b} {c = c} h η = [ comp ]₁ (Category.id (HomCat b c) , η)

  -- Left whiskering
  _◁_ : {a b c : Cell₀} {f g : Cell₁ b c} 
      → (h : Cell₁ a b) → Cell₂ f g → Cell₂ (f ∘ₕ h) (g ∘ₕ h)
  _◁_ {a = a} {b = b} h η = [ comp ]₁ (η , Category.id (HomCat a b))
  
  -- The functor designated by id
  id→functor : {a : Cell₀} → Functor ⊤-Cat (HomCat a a)
  id→functor {a} = constFunctor (HomCat a a) (id₁ {a})
  
  id₂ : {a b : Cell₀} {f : Cell₁ a b} → Cell₂ f f
  id₂ {a} {b} = Category.id (HomCat a b)
