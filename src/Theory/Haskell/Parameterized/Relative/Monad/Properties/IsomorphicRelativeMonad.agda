
-- Stdlib
open import Level
open import Function hiding ( id ) renaming ( _∘_ to _∘F_ )
open import Data.Unit
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( refl to hrefl ; sym to hsym ; trans to htrans ; subst to hsubst ; cong to hcong ; cong₂ to hcong₂ )
open ≅-Reasoning 

-- Local
open import Bijection renaming ( refl to brefl ; sym to bsym ; trans to btrans )
open import Congruence
open import Extensionality

open import Theory.Category.Definition
open import Theory.Functor.Definition
open import Theory.Natural.Transformation
open import Theory.Monad.Relative
open import Theory.Monad.Relative.Equality

open import Theory.Haskell.Parameterized.Relative.Monad
open import Theory.Haskell.Parameterized.Relative.Monad.Equality

open Category renaming ( right-id to cat-right-id ; left-id to cat-left-id ; id to cat-id )

module Theory.Haskell.Parameterized.Relative.Monad.Properties.IsomorphicRelativeMonad 
  {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} 
  {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}} 
  (T : Obj C → Obj D) (J : Functor C D) where 


ParameterizedRelativeMonad→RelativeMonad : ParameterizedRelativeMonad ⊤-Cat (λ {i} {j} f → T) J → RelativeMonad T J
ParameterizedRelativeMonad→RelativeMonad PRM = 
  relative-monad (λ {a} → η tt {a}) 
                 (λ {a b} k → kext tt tt k) 
                 (λ {a b} {k} → ≅-to-≡ (right-id tt)) 
                 (λ {a} → ≅-to-≡ (left-id tt)) 
                 (λ {a b c} {k} {l} → ≅-to-≡ (coher tt tt tt))
  where
    open ParameterizedRelativeMonad PRM

RelativeMonad→ParameterizedRelativeMonad : RelativeMonad T J → ParameterizedRelativeMonad ⊤-Cat (λ {i} {j} f → T) J
RelativeMonad→ParameterizedRelativeMonad RM = 
  parameterized-relative-monad (λ i {a} → η {a}) 
                               (λ {i j k} f g {a b} → kext {a} {b}) 
                               (λ {i j} f {a b} {k} → ≡-to-≅ $ right-id {a} {b} {k}) 
                               (λ {i j} f {a} → ≡-to-≅ $ left-id {a}) 
                               (λ {i j v w} f g h {a b c} {k} {l} → ≡-to-≅ $ coher {a} {b} {c} {k} {l})
  where
    open RelativeMonad RM

ParameterizedRelativeMonad↔RelativeMonad : ParameterizedRelativeMonad ⊤-Cat (λ {i j} f → T) J ↔ RelativeMonad T J
ParameterizedRelativeMonad↔RelativeMonad = bijection ParameterizedRelativeMonad→RelativeMonad RelativeMonad→ParameterizedRelativeMonad RM→PRM→RM PRM→RM→PRM
  where
    PRM→RM→PRM : (PRM : ParameterizedRelativeMonad ⊤-Cat (λ {i} {j} f → T) J)
               → RelativeMonad→ParameterizedRelativeMonad (ParameterizedRelativeMonad→RelativeMonad PRM) ≡ PRM
    PRM→RM→PRM PRM = parameterized-relative-monad-eq (fun-ext $ λ i → refl) 
                   $ implicit-fun-ext 
                   $ λ i → implicit-fun-ext
                   $ λ j → implicit-fun-ext 
                   $ λ k → fun-ext 
                   $ λ f → fun-ext 
                   $ λ g → refl
    
    RM→PRM→RM : (RM : RelativeMonad T J) 
              → ParameterizedRelativeMonad→RelativeMonad (RelativeMonad→ParameterizedRelativeMonad RM) ≡ RM
    RM→PRM→RM RM = relative-monad-eq refl refl
