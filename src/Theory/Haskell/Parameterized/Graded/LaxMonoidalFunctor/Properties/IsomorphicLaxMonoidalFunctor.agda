
open import Level
open import Function hiding ( id )

open import Data.Product

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( refl to hrefl ; sym to hsym ; trans to htrans )

open import Bijection hiding ( refl ; trans ) renaming ( sym to bsym )
open import Extensionality

open import Theory.Monoid
open import Theory.Category.Definition
open import Theory.Category.Monoidal
open import Theory.Category.Monoidal.Product
open import Theory.Category.Monoidal.Examples.Monoid renaming ( monoidMonoidalCategory to MonCat )
open import Theory.Functor.Definition
open import Theory.Functor.Monoidal
open import Theory.Natural.Transformation

open import Theory.Haskell.Parameterized.Graded.LaxMonoidalFunctor
open import Theory.Haskell.Parameterized.Graded.LaxMonoidalFunctor.Equality
open import Theory.Haskell.Parameterized.Graded.LaxMonoidalFunctor.Properties.ToLaxMonoidalFunctor
open import Theory.Haskell.Parameterized.Graded.LaxMonoidalFunctor.Properties.FromLaxMonoidalFunctor

module Theory.Haskell.Parameterized.Graded.LaxMonoidalFunctor.Properties.IsomorphicLaxMonoidalFunctor where 


GradedLaxMonoidalFunctor↔LaxMonoidalFunctor : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ ℓMon : Level} {M : Set ℓMon} (Mon : Monoid M)
                                            → {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}}
                                            → {CM : MonoidalCategory C} {DM : MonoidalCategory D}
                                            → GradedLaxMonoidalFunctor Mon CM DM ↔ LaxMonoidalFunctor (MonCat Mon ×CMon CM) DM
GradedLaxMonoidalFunctor↔LaxMonoidalFunctor {ℓC₀} {ℓC₁} {ℓD₀} {ℓD₁} {ℓMon} {M} Mon {C} {D} {CM} {DM} = 
  bijection (GradedLaxMonoidalFunctor→LaxMonoidalFunctor Mon) (LaxMonoidalFunctor→GradedLaxMonoidalFunctor Mon) r→l→r l→r→l
  where
    r→l→r : (LMF : LaxMonoidalFunctor (MonCat Mon ×CMon CM) DM)
          → GradedLaxMonoidalFunctor→LaxMonoidalFunctor Mon (LaxMonoidalFunctor→GradedLaxMonoidalFunctor Mon LMF) ≡ LMF
    r→l→r LMF = lax-monoidal-functor-eq F-eq hrefl μ-eq
      where
        F-eq : LaxMonoidalFunctor.F (GradedLaxMonoidalFunctor→LaxMonoidalFunctor Mon (LaxMonoidalFunctor→GradedLaxMonoidalFunctor Mon LMF)) ≡ LaxMonoidalFunctor.F LMF
        F-eq = functor-eq refl (het-implicit-fun-ext hrefl $ λ {(i , a) → het-implicit-fun-ext hrefl λ {(j , b) → het-fun-ext hrefl λ {(refl , f) → hrefl}}})
        
        μ-eq : LaxMonoidalFunctor.μ-natural-transformation (GradedLaxMonoidalFunctor→LaxMonoidalFunctor Mon (LaxMonoidalFunctor→GradedLaxMonoidalFunctor Mon LMF)) ≅ LaxMonoidalFunctor.μ-natural-transformation LMF
        μ-eq = het-natural-transformation-eq 
                 (functor-eq refl (het-implicit-fun-ext hrefl $ λ {((i , a) , (j , b)) → het-implicit-fun-ext hrefl $ λ {((i' , a') , (j' , b')) → het-fun-ext hrefl $ λ {((refl , f) , (refl , g)) → hrefl}}})) 
                 (functor-eq refl (het-implicit-fun-ext hrefl $ λ {((i , a) , (j , b)) → het-implicit-fun-ext hrefl $ λ {((i' , a') , (j' , b')) → het-fun-ext hrefl $ λ {((refl , f) , (refl , g)) → hrefl}}}))
                 hrefl
    
    l→r→l : (GLMF : GradedLaxMonoidalFunctor Mon CM DM) 
          → LaxMonoidalFunctor→GradedLaxMonoidalFunctor Mon (GradedLaxMonoidalFunctor→LaxMonoidalFunctor Mon GLMF) ≡ GLMF
    l→r→l GLMF = graded-lax-monoidal-functor-eq refl hrefl hrefl

LaxMonoidalFunctor↔GradedLaxMonoidalFunctor : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ ℓMon : Level} {M : Set ℓMon} (Mon : Monoid M)
                                            → {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}}
                                            → {CM : MonoidalCategory C} {DM : MonoidalCategory D}
                                            → LaxMonoidalFunctor (MonCat Mon ×CMon CM) DM ↔ GradedLaxMonoidalFunctor Mon CM DM
LaxMonoidalFunctor↔GradedLaxMonoidalFunctor {ℓC₀} {ℓC₁} {ℓD₀} {ℓD₁} {ℓMon} {M} Mon {C} {D} {CM} {DM} = bsym (GradedLaxMonoidalFunctor↔LaxMonoidalFunctor Mon)
