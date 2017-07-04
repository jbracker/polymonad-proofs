
open import Level
open import Function renaming ( _∘_ to _∘F_ ; id to idF )

open import Data.Unit
open import Data.Product

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Extensionality

open import Haskell
open import Haskell.Functor hiding ( functor ) renaming ( Functor to HaskellFunctor )
open import Haskell.Applicative

open import Theory.Category.Definition
open import Theory.Category.Examples
open import Theory.Category.Monoidal
open import Theory.Category.Monoidal.Examples.SetCat
open import Theory.Functor.Definition hiding ( functor )
open import Theory.Functor.Composition
open import Theory.Functor.Monoidal
open import Theory.Functor.Properties.IsomorphicHaskellFunctor
open import Theory.Natural.Transformation

module Theory.Functor.Monoidal.Properties.ToHaskellApplicative where

-- open Category hiding ( Obj ; Hom )
open MonoidalCategory hiding ( id )

LaxMonoidalFunctor→HaskellApplicative
  : (FMon : LaxMonoidalFunctor (setMonoidalCategory {zero}) (setMonoidalCategory {zero}))
  → Applicative (LaxMonoidalFunctor.F₀ FMon)
LaxMonoidalFunctor→HaskellApplicative FMon = applicative pure _<*>_ haskFunctor law-id law-composition law-homomorphism law-interchange law-applicative-fmap
  where
    Hask' = setCategory {zero}
    MonHask = setMonoidalCategory {zero}
    
    open LaxMonoidalFunctor FMon
    open NaturalTransformation renaming ( η to nat-η )
    
    fmap : {α β : Type} → (α → β) → F₀ α → F₀ β
    fmap {α} {β} f Fα = F₁ f Fα
    
    unit' : F₀ (Lift ⊤)
    unit' = ε (lift tt)
    
    pure : {α : Type} → α → F₀ α
    pure {α} a = fmap (λ _ → a) unit'
    
    _**_ : {α β : Type} → F₀ α → F₀ β → F₀ (α × β)
    _**_ {α} {β} Fα Fβ = μ α β (Fα , Fβ)
    
    _<*>_ : {α β : Type} → F₀ (α → β) → F₀ α → F₀ β
    _<*>_ {α} {β} Fα→β Fα = fmap (λ {(f , a) → f a}) (Fα→β ** Fα)
    
    haskFunctor : HaskellFunctor F₀
    haskFunctor = Functor→HaskellFunctor F
    
    monNatTrans : NaturalTransformation ([ tensor MonHask ]∘[ [ F ]×[ F ] ]) ([ F ]∘[ tensor MonHask ]) 
    monNatTrans = μ-natural-transformation
    
    abstract
      nat :  {a b : Category.Obj (Hask' ×C Hask')}
          → {f : Category.Hom (Hask' ×C Hask') a b}
          → (F₁ (proj₁ f *** proj₂ f)) ∘F (nat-η monNatTrans a)
          ≡ (nat-η monNatTrans b) ∘F (F₁ (proj₁ f) *** F₁ (proj₂ f))
      nat {a} {b} {f} = natural monNatTrans {a} {b} {f}
    
    abstract
      law-naturality : {α β γ δ : Type} → (f : α → β) (g : γ → δ) (u : F₀ α) (v : F₀ γ) 
                     → fmap (f *** g) (u ** v) ≡ fmap f u ** fmap g v
      law-naturality {α} {β} {γ} {δ} f g u v = begin
        ( F₁ (f *** g) ∘F (nat-η monNatTrans (α , γ)) ) (u , v)
          ≡⟨ cong (λ X → X (u , v)) (nat {f = (f , g)}) ⟩
        nat-η monNatTrans (β , δ) (F₁ f u , F₁ g v) ∎
    
    abstract
      law-left-identity' : {α : Type} → (v : F₀ α) 
                         → fmap proj₂ (unit' ** v) ≡ v
      law-left-identity' {α} v = begin
        (F₁ proj₂ ∘F nat-η monNatTrans (Lift ⊤ , α) ∘F (ε *** (λ x → x)) ) (lift tt , v) 
          ≡⟨ cong (λ X → X (lift tt , v)) (sym (left-unitality α)) ⟩
        proj₂ {a = zero} (lift tt , v) 
          ≡⟨⟩
        v ∎
    
    abstract
      law-left-identity : {α : Type} → (v : F₀ α) 
                        → (unit' ** v) ≡ fmap (λ a → (lift tt , a)) v
      law-left-identity {α} v = begin
        (nat-η monNatTrans (Lift ⊤ , α) ∘F (ε *** (λ x → x))) (lift tt , v)
          ≡⟨ cong (λ X → (X ∘F nat-η monNatTrans (Lift ⊤ , α) ∘F (ε *** (λ x → x))) (lift tt , v)) (sym (Functor.id F)) ⟩
        (F₁ (λ x → x) ∘F nat-η monNatTrans (Lift ⊤ , α) ∘F (ε *** (λ x → x))) (lift tt , v)
          ≡⟨ refl ⟩
        (F₁ ((λ a → (lift tt , a)) ∘F proj₂) ∘F nat-η monNatTrans (Lift ⊤ , α) ∘F (ε *** (λ x → x))) (lift tt , v)
          ≡⟨ cong (λ X → (X ∘F nat-η monNatTrans (Lift ⊤ , α) ∘F (ε *** (λ x → x))) (lift tt , v)) (Functor.compose F) ⟩
        (F₁ (λ a → (lift tt , a)) ∘F F₁ proj₂ ∘F nat-η monNatTrans (Lift ⊤ , α) ∘F (ε *** (λ x → x))) (lift tt , v)
          ≡⟨ cong (fmap (λ a → (lift tt , a))) (law-left-identity' v) ⟩
        fmap (λ a → (lift tt , a)) v ∎
    
    abstract
      law-right-identity' : {α : Type} → (v : F₀ α) 
                          → fmap proj₁ (v ** unit') ≡ v
      law-right-identity' {α} v = cong (λ X → X (v , lift tt)) (sym (right-unitality α))
    
    abstract
      law-right-identity : {α : Type} → (v : F₀ α) 
                          → (v ** unit') ≡ fmap (λ a → (a , lift tt)) v
      law-right-identity {α} v = begin
        (nat-η monNatTrans (α , Lift ⊤) ∘F ((λ x → x) *** ε)) (v , lift tt)
          ≡⟨ cong (λ X → (X ∘F nat-η monNatTrans (α , Lift ⊤) ∘F ((λ x → x) *** ε)) (v , lift tt)) (sym $ Functor.id F) ⟩
        (F₁ (λ x → x) ∘F nat-η monNatTrans (α , Lift ⊤) ∘F ((λ x → x) *** ε)) (v , lift tt)
          ≡⟨ refl ⟩
        (F₁ ((λ a → (a , lift tt)) ∘F proj₁) ∘F nat-η monNatTrans (α , Lift ⊤) ∘F ((λ x → x) *** ε)) (v , lift tt)
          ≡⟨ cong (λ X → (X ∘F nat-η monNatTrans (α , Lift ⊤) ∘F ((λ x → x) *** ε)) (v , lift tt)) (Functor.compose F) ⟩
        (F₁ (λ a → (a , lift tt)) ∘F F₁ proj₁ ∘F nat-η monNatTrans (α , Lift ⊤) ∘F ((λ x → x) *** ε)) (v , lift tt)
          ≡⟨ cong (fmap (λ a → (a , lift tt))) (law-right-identity' v) ⟩
        fmap (λ a → (a , lift tt)) v ∎
    
    abstract
      law-applicative-fmap : {α β : Type} 
                           → (f : α → β) → (x : F₀ α) 
                           → fmap f x ≡ pure f <*> x
      law-applicative-fmap {α} {β} f x = begin
        fmap f x 
          ≡⟨ refl ⟩
        fmap ((λ x → f (proj₂ {a = zero} x)) ∘F (λ a → (lift tt , a))) x
          ≡⟨ cong (λ X → X x) (Functor.compose F) ⟩
        fmap (λ x → f (proj₂ x)) (fmap (λ a → (lift tt , a)) x)
          ≡⟨ cong (fmap (λ x₁ → f (proj₂ x₁))) (sym $ law-left-identity x) ⟩
        fmap (λ x → f (proj₂ x)) (unit' ** x)
          ≡⟨ refl ⟩
        fmap ( (λ {(f , a) → f a}) ∘F ((λ _ → f) *** (λ x → x)) ) (ε (lift tt) ** x)
          ≡⟨ cong (λ X → X (ε (lift tt) ** x)) (Functor.compose F) ⟩
        fmap (λ {(f , a) → f a}) (fmap ((λ _ → f) *** (λ x → x)) (ε (lift tt) ** x))
          ≡⟨ cong (λ X → fmap (λ {(f , a) → f a }) X) (law-naturality (λ _ → f) (λ z → z) (ε (lift tt)) x) ⟩
        fmap (λ {(f , a) → f a}) ((fmap (λ _ → f) (ε (lift tt))) ** fmap (λ x → x) x)
          ≡⟨ cong (λ X → fmap (λ {(f , a) → f a}) ((fmap (λ _ → f) (ε (lift tt))) ** X)) (cong (λ X → X x) (Functor.id F)) ⟩
        fmap (λ {(f , a) → f a}) ((fmap (λ _ → f) (ε (lift tt))) ** x) ∎
    
    abstract
      law-id : {α : Type} 
             → (v : F₀ α) 
             → (pure (λ x → x) <*> v) ≡ v
      law-id {α} v = begin
        (pure (λ x → x) <*> v)
          ≡⟨ sym $ law-applicative-fmap (λ x → x) v ⟩
        fmap (λ x → x) v
          ≡⟨ cong (λ X → X v) (Functor.id F) ⟩
        v ∎
    
    abstract
      law-associativity : {α β γ : Type} → (u : F₀ α) (v : F₀ β) (w : F₀ γ) 
                        → u ** (v ** w) ≡ fmap (λ {((a , b) , c) → (a , (b , c))}) ( (u ** v) ** w ) 
      law-associativity {α} {β} {γ} u v w = 
        (nat-η monNatTrans (α , (β × γ)) ∘F (idF *** nat-η monNatTrans (β , γ))) (u , (v , w)) 
          ≡⟨ cong (λ X → X ((u , v) , w)) (sym $ assoc FMon α β γ) ⟩
        (F₁ (λ {((a , b) , c) → (a , (b , c))}) ∘F nat-η monNatTrans ((α × β) , γ) ∘F (nat-η monNatTrans (α , β) *** idF)) ((u , v) , w) ∎
    
    abstract
      law-composition : {α β γ : Type} 
                      → (u : F₀ (β → γ)) (v : F₀ (α → β)) (w : F₀ α)
                      → (((pure _∘′_ <*> u) <*> v) <*> w) ≡ (u <*> (v <*> w))
      law-composition {α} {β} {γ} u v w = begin
        fmap (λ {(f , a) → f a}) (fmap (λ {(f , a) → f a}) ((fmap (λ {(f , a) → f a}) (fmap (λ _ → _∘′_) unit' ** u)) ** v) ** w) 
          ≡⟨ cong (λ X → fmap (λ {(f , a) → f a}) (fmap (λ {(f , a) → f a}) ((fmap (λ {(f , a) → f a}) (fmap (λ _ → _∘′_) unit' ** X u)) ** v) ** w)) (sym $ Functor.id F) ⟩
        fmap (λ {(f , a) → f a}) (fmap (λ {(f , a) → f a}) ((fmap (λ {(f , a) → f a}) (fmap (λ _ → _∘′_) unit' ** fmap idF u)) ** v) ** w) 
          ≡⟨ cong (λ X → fmap (λ { (f , a) → f a }) (fmap (λ { (f , a) → f a }) (fmap (λ { (f , a) → f a }) X ** v) ** w))
                  (sym $ law-naturality (λ _ → _∘′_) idF unit' u) ⟩
        fmap (λ {(f , a) → f a}) (fmap (λ {(f , a) → f a}) ((fmap (λ {(f , a) → f a}) (fmap ((λ _ → _∘′_) *** idF) (unit' ** u))) ** v) ** w) 
          ≡⟨ cong (λ X → fmap (λ {(f , a) → f a}) (fmap (λ {(f , a) → f a}) ((fmap (λ {(f , a) → f a}) (fmap ((λ _ → _∘′_) *** idF) X)) ** v) ** w) ) 
                  (law-left-identity u) ⟩
        fmap (λ {(f , a) → f a}) (fmap (λ {(f , a) → f a}) ((fmap (λ {(f , a) → f a}) (fmap ((λ _ → _∘′_) *** idF) (fmap (λ a → (lift tt , a)) u))) ** v) ** w) 
          ≡⟨ cong (λ X → fmap (λ {(f , a) → f a}) (fmap (λ {(f , a) → f a}) ((X (fmap (λ a → (lift tt , a)) u)) ** v) ** w)) (sym $ Functor.compose F) ⟩
        fmap (λ {(f , a) → f a}) (fmap (λ {(f , a) → f a}) ((fmap ((λ {(f , a) → f a}) ∘F ((λ _ → _∘′_) *** idF)) (fmap (λ a → (lift tt , a)) u)) ** v) ** w)
          ≡⟨ cong (λ X → fmap (λ {(f , a) → f a}) (fmap (λ {(f , a) → f a}) ((X u) ** v) ** w)) (sym $ Functor.compose F) ⟩
        fmap (λ {(f , a) → f a}) (fmap (λ {(f , a) → f a}) ((fmap g u) ** v) ** w)
          ≡⟨ cong (λ X → fmap (λ {(f , a) → f a}) (fmap (λ {(f , a) → f a}) ((fmap g u) ** X v) ** w)) (sym $ Functor.id F) ⟩
        fmap (λ {(f , a) → f a}) (fmap (λ {(f , a) → f a}) ((fmap g u) ** fmap idF v) ** w)
          ≡⟨ cong (λ X → fmap (λ {(f , a) → f a}) (fmap (λ {(f , a) → f a}) X ** w)) (sym $ law-naturality g idF u v) ⟩
        fmap (λ {(f , a) → f a}) (fmap (λ {(f , a) → f a}) (fmap (g *** idF) (u ** v)) ** w)
          ≡⟨ cong (λ X → fmap (λ {(f , a) → f a}) (X (u ** v) ** w)) (sym $ Functor.compose F) ⟩
        fmap (λ {(f , a) → f a}) (fmap ((λ {(f , a) → f a}) ∘F (g *** idF)) (u ** v) ** w)
          ≡⟨ cong (λ X → fmap (λ {(f , a) → f a}) (fmap ((λ {(f , a) → f a}) ∘F (g *** idF)) (u ** v) ** X w)) (sym $ Functor.id F) ⟩
        fmap (λ {(f , a) → f a}) (fmap ((λ {(f , a) → f a}) ∘F (g *** idF)) (u ** v) ** fmap idF w)
          ≡⟨ cong (fmap (λ {(f , a) → f a})) (sym $ law-naturality ((λ {(f , a) → f a}) ∘F (g *** idF)) idF (u ** v) w) ⟩
        fmap (λ {(f , a) → f a}) (fmap (((λ {(f , a) → f a}) ∘F (g *** idF)) *** idF) ((u ** v) ** w))
          ≡⟨ cong (λ X → X ((u ** v) ** w)) (sym $ Functor.compose F) ⟩
        fmap h ((u ** v) ** w)
          ≡⟨ refl ⟩
        fmap (h' ∘F (λ {((a , b) , c) → (a , (b , c))})) ( (u ** v) ** w )
          ≡⟨ cong (λ X → X ( (u ** v) ** w )) (Functor.compose F) ⟩
        fmap h' (fmap (λ {((a , b) , c) → (a , (b , c))}) ( (u ** v) ** w ) )
          ≡⟨ cong (fmap h') (sym $ law-associativity u v w) ⟩
        fmap h' (u ** (v ** w))
          ≡⟨ cong (λ X → X (u ** (v ** w))) (Functor.compose F) ⟩
        fmap (λ {(f , a) → f a}) (fmap (idF *** (λ {(f , a) → f a})) (u ** (v ** w)))
          ≡⟨ cong (fmap (λ { (f , a) → f a })) (law-naturality idF (λ {(f , a) → f a}) u (v ** w)) ⟩
        fmap (λ {(f , a) → f a}) (fmap idF u ** fmap (λ {(f , a) → f a}) (v ** w))
          ≡⟨ cong (λ X → fmap (λ { (f , a) → f a }) (X u ** fmap (λ { (f , a) → f a }) (v ** w))) (Functor.id F) ⟩
        fmap (λ {(f , a) → f a}) (u ** fmap (λ {(f , a) → f a}) (v ** w)) ∎
        where
          g = (((λ {(f , a) → f a}) ∘F ((λ _ → _∘′_) *** idF)) ∘F (λ a → (lift tt , a)))
          h = ((λ {(f , a) → f a}) ∘F (((λ {(f , a) → f a}) ∘F (g *** idF)) *** idF))
          h' = ((λ {(f , a) → f a}) ∘F (idF *** (λ {(f , a) → f a})))
    
    abstract
      law-homomorphism : {α β : Type} 
                       → (x : α) → (f : α → β) 
                       → pure f <*> pure x ≡ pure (f x)
      law-homomorphism {α} {β} x f = begin
        fmap (λ {(f , a) → f a}) (fmap (λ _ → f) unit' ** fmap (λ _ → x) unit')
          ≡⟨ cong (fmap (λ {(f , a) → f a})) (sym $ law-naturality (λ _ → f) (λ _ → x) unit' unit') ⟩
        fmap (λ {(f , a) → f a}) (fmap ((λ _ → f) *** (λ _ → x)) (unit' ** unit'))
          ≡⟨ cong (λ X → X (unit' ** unit')) (sym $ Functor.compose F) ⟩
        fmap ((λ {(f , a) → f a}) ∘F ((λ _ → f) *** (λ _ → x))) (unit' ** unit')
          ≡⟨ cong (fmap ((λ {(f , a) → f a}) ∘F ((λ _ → f) *** (λ _ → x)))) (law-left-identity unit') ⟩
        fmap ((λ {(f , a) → f a}) ∘F ((λ _ → f) *** (λ _ → x))) (fmap (λ a → (lift tt , a)) unit')
          ≡⟨ cong (λ X → X unit') (sym $ Functor.compose F) ⟩
        fmap (λ _ → f x) unit' ∎
    
    abstract
      law-interchange : {α β : Type} 
                      → (u : F₀ (α → β)) → (x : α) 
                      → u <*> pure x ≡ pure (λ f → f x) <*> u
      law-interchange {α} {β} u x = begin
        fmap (λ {(f , a) → f a}) (u ** fmap (λ _ → x) unit')
          ≡⟨ cong (λ X → fmap (λ {(f , a) → f a}) (X u ** fmap (λ _ → x) unit')) (sym $ Functor.id F) ⟩
        fmap (λ {(f , a) → f a}) (fmap idF u ** fmap (λ _ → x) unit')
          ≡⟨ cong (fmap (λ {(f , a) → f a})) (sym $ law-naturality idF (λ _ → x) u unit') ⟩
        fmap (λ {(f , a) → f a}) (fmap (idF *** (λ _ → x)) (u ** unit'))
          ≡⟨ cong (λ X → X (u ** unit')) (sym $ Functor.compose F) ⟩
        fmap ((λ {(f , a) → f a}) ∘F (idF *** (λ _ → x))) (u ** unit')
          ≡⟨ cong (fmap ((λ {(f , a) → f a}) ∘F (idF *** (λ _ → x)))) (law-right-identity u) ⟩
        fmap ((λ {(f , a) → f a}) ∘F (idF *** (λ _ → x))) (fmap (λ a → (a , lift tt)) u)
          ≡⟨ cong (λ X → X u) (sym $ Functor.compose F) ⟩
        fmap ((λ {(f , a) → f a}) ∘F ((λ _ → (λ f → f x)) *** idF) ∘F (λ a → (lift tt , a))) u
          ≡⟨ cong (λ X → X u) (Functor.compose F) ⟩
        fmap ((λ {(f , a) → f a}) ∘F ((λ _ → (λ f → f x)) *** idF)) (fmap (λ a → (lift tt , a)) u)
          ≡⟨ cong (fmap ((λ {(f , a) → f a}) ∘F ((λ _ → (λ f → f x)) *** idF))) (sym $ law-left-identity u) ⟩
        fmap ((λ {(f , a) → f a}) ∘F ((λ _ → (λ f → f x)) *** idF)) (unit' ** u)
          ≡⟨ cong (λ X → X (unit' ** u)) (Functor.compose F) ⟩
        fmap (λ {(f , a) → f a}) (fmap ((λ _ → (λ f → f x)) *** idF) (unit' ** u))
          ≡⟨ cong (fmap (λ {(f , a) → f a})) (law-naturality (λ _ f → f x) idF unit' u) ⟩
        fmap (λ {(f , a) → f a}) (fmap (λ _ → (λ f → f x)) unit' ** fmap idF u)
          ≡⟨ cong (λ X → fmap (λ {(f , a) → f a}) (fmap (λ _ → (λ f → f x)) unit' ** X u)) (Functor.id F) ⟩
        fmap (λ {(f , a) → f a}) (fmap (λ _ → (λ f → f x)) unit' ** u) ∎

