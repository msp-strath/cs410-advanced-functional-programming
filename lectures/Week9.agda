{-# OPTIONS --type-in-type #-}

module Week9 where

open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; refl; sym; cong; cong₂)
open Eq.≡-Reasoning

open import Data.List.Base
open import Data.List.Properties

postulate
  funext : {S T : Set} → {f g : S → T} → ((x : S) → f x ≡ g x) → f ≡ g

---------------------------------------------------------------------------
-- Category
---------------------------------------------------------------------------

record Category : Set₁ where
  field
  -- Types and operations
    Object : Set
    Morphism : (source target : Object) → Set
    _then_   : ∀ {s m t} → Morphism s m → Morphism m t → Morphism s t
    identity : ∀ {s} → Morphism s s

  field
    then-assoc  : ∀ {s m₁ m₂ t} (x : Morphism s m₁) (y : Morphism m₁ m₂) (z : Morphism m₂ t)
                → ((x then y) then z) ≡ (x then (y then z))

    then-identity : ∀ {s t} (x : Morphism s t) → (x then identity) ≡ x
    identity-then : ∀ {s t} (x : Morphism s t) → (identity then x) ≡ x


---------------------------------------------------------------------------
-- Functor
---------------------------------------------------------------------------

record Functor (C D : Category) : Set where
  module C = Category C
  module D = Category D
  field
    -- operations
    onObject   : C.Object → D.Object
    onMorphism : ∀ {s t} →
      C.Morphism           s            t →
      D.Morphism (onObject s) (onObject t)

    -- properties
    onIdentity : ∀ {s} → onMorphism (C.identity {s})
                       ≡ D.identity {onObject s}

    onThen : ∀ {s m t} (f : C.Morphism s m) (g : C.Morphism m t) →
             onMorphism (f C.then g) ≡ onMorphism f D.then onMorphism g

-- example

SET : Category
SET .Category.Object = Set
SET .Category.Morphism S T = S -> T
SET .Category._then_ f g = λ x → g (f x)
SET .Category.identity = λ x → x
SET .Category.then-assoc f g h = refl
SET .Category.then-identity f = refl
SET .Category.identity-then f = refl

List-functor : Functor SET SET
List-functor .Functor.onObject X = List X
List-functor .Functor.onMorphism f xs = map f xs
List-functor .Functor.onIdentity = funext foo
  where
   foo : ∀ xs → map (λ x → x) xs ≡ xs
   foo [] = refl
   foo (x ∷ xs) = cong (x ∷_) (foo xs)
List-functor .Functor.onThen f g = funext map-∘

-- e.g. Vec≤


open import Data.Nat.Base using (ℕ; _≤_)
import Data.Nat.Properties as ℕ

ℕ≤-cat : Category
ℕ≤-cat .Category.Object = ℕ
ℕ≤-cat .Category.Morphism = _≤_
ℕ≤-cat .Category._then_ = ℕ.≤-trans
ℕ≤-cat .Category.identity = ℕ.≤-refl
ℕ≤-cat .Category.then-assoc = λ _ _ _ → ℕ.≤-irrelevant _ _
ℕ≤-cat .Category.then-identity = λ _ → ℕ.≤-irrelevant _ _
ℕ≤-cat .Category.identity-then = λ _ → ℕ.≤-irrelevant _ _

open import Data.Vec.Base as Vec using (Vec)
import Data.Vec.Properties as Vec

{-
Vec-Functor : (n : ℕ) → Functor SET SET
Vec-Functor n .Functor.onObject = λ A → Vec A n
Vec-Functor n .Functor.onMorphism = {!!}
Vec-Functor n .Functor.onIdentity = {!!}
Vec-Functor n .Functor.onThen = {!!}
-}

OP : Category → Category
OP cat .Category.Object = Category.Object cat
OP cat .Category.Morphism = λ s t → Category.Morphism cat t s
OP cat .Category._then_ = λ g f → Category._then_ cat f g
OP cat .Category.identity = Category.identity cat
OP cat .Category.then-assoc = λ f g h → sym (Category.then-assoc cat h g f)
OP cat .Category.then-identity = Category.identity-then cat
OP cat .Category.identity-then = Category.then-identity cat

Vec≤-Functor : (A : Set) → Functor (OP ℕ≤-cat) SET
Vec≤-Functor A .Functor.onObject n = Vec A n
Vec≤-Functor A .Functor.onMorphism = Vec.truncate
Vec≤-Functor A .Functor.onIdentity = funext Vec.truncate-refl
Vec≤-Functor A .Functor.onThen =
  λ n≤p m≤n → funext (Vec.truncate-trans m≤n n≤p)



-- Forget & free


---------------------------------------------------------------------------
-- Revisiting syntax & semantics
---------------------------------------------------------------------------
