
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

open import Theory.Category
open import Theory.Functor
open import Theory.NaturalTransformation
open import Theory.Examples.Functor

-------------------------------------------------------------------------------
-- Definition of 2-Categories
-------------------------------------------------------------------------------
open Category hiding ( idL ; idR ; assoc ) renaming ( id to idC )

record TwoCategory {ℓ₀ ℓ₁ ℓ₂ : Level} : Set (lsuc (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    Cell₀ : Set ℓ₀
    Cell₁ : Cell₀ → Cell₀ → Category {ℓ₁} {ℓ₂}

    --                       (b c × a b ↦ a c)
    comp : {a b c : Cell₀} → Functor (Cell₁ b c ×C Cell₁ a b) (Cell₁ a c) 
    id   : {a : Cell₀} → Obj (Cell₁ a a)
    
    idL : {a b : Cell₀} 
        -- (a b × a a ↦ a b)  ∘  (a b ↦ a b × a a)
        → [ comp {a} {a} {b} ]∘[ [ Id[ Cell₁ a b ] ◁ Cell₁ a a , id {a} ] ]
        -- (a b ↦ a b) 
        ≡ Id[ Cell₁ a b ]
    idR : {a b : Cell₀}
        -- (b b × a b ↦ a b)  ∘  (a b ↦ b b × a b)
        → [ comp {a} {b} {b} ]∘[ [ Cell₁ b b , id {b} ▷ Id[ Cell₁ a b ] ] ] 
        -- (a b ↦ a b)
        ≡ Id[ Cell₁ a b ]
    
    assoc : {a b c d : Cell₀}
          -- (c d × a c → a d)  ∘  (c d × (b c × a c) ↦ c d × a c)             ∘ (c d × b c × a b ↦ c d × (b c × a b))
          → [ comp {a} {c} {d} ]∘[ [ [ Id[ Cell₁ c d ] ]×[ comp {a} {b} {c} ] ]∘[ A×B×C→A×[B×C] ] ] 
          -- (b d × a b ↦ a d)  ∘  ((c d × b c) × a b ↦ b d × a b)             ∘ (c d × b c × a b ↦ (c d × b c) × a b)
          ≡ [ comp {a} {b} {d} ]∘[ [ [ comp {b} {c} {d} ]×[ Id[ Cell₁ a b ] ] ]∘[ A×B×C→[A×B]×C ] ]
