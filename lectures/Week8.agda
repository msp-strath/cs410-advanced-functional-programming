{-# OPTIONS --type-in-type #-}
module Week8 where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; module ≡-Reasoning)

open import Function using (_∘′_; id)

open import Week7 hiding (Category; _++_)


-- Remember categories? A category is a fancy monoid:
--   - It has a type of objects
--   - It has a type of morphisms with a source & target object
--   - For each object, it has a unit morphism from the object to itself
--   - It has a way to combine two morphisms
--      (provided the target of the first is the source of the second)
--   - Combining morphisms is associative

---------------------------------------------------------------------------
-- Category
---------------------------------------------------------------------------

record Category : Set₁ where
  field
  -- Type and operations
    Object : Set
    Morphism : (source target : Object) → Set
    _then_   : ∀ {s m t} → Morphism s m → Morphism m t → Morphism s t
    identity : ∀ {s} → Morphism s s

  field
    then-assoc  : ∀ {s m₁ m₂ t} (x : Morphism s m₁) (y : Morphism m₁ m₂) (z : Morphism m₂ t)
                → ((x then y) then z) ≡ (x then (y then z))

    then-identity : ∀ {s t} (x : Morphism s t) → (x then identity) ≡ x
    identity-then : ∀ {s t} (x : Morphism s t) → (identity then x) ≡ x

open Category

-- Our favourite categories

open import Data.Nat.Base using (ℕ; _≤_)
import Data.Nat.Properties as ℕ

ℕ≤-cat : Category
ℕ≤-cat .Object = ℕ
ℕ≤-cat .Morphism = _≤_
ℕ≤-cat ._then_ = ℕ.≤-trans
ℕ≤-cat .identity = ℕ.≤-refl
ℕ≤-cat .then-assoc = λ _ _ _ → ℕ.≤-irrelevant _ _
ℕ≤-cat .then-identity = λ _ → ℕ.≤-irrelevant _ _
ℕ≤-cat .identity-then = λ _ → ℕ.≤-irrelevant _ _

-- Category of monoids

-- When are monoid homomorphisms equal?

postulate
  monHomEq : {M N : Monoid} → (f g : HomoMorphism M N)
         → HomoMorphism.function f ≡ HomoMorphism.function g
         → f ≡ g
{-
monHomEq record { function = f ; mempty-resp = f-mempty ; <>-resp = f-<> }
         record { function = .f ; mempty-resp = g-mempty ; <>-resp = g-<> } refl
           = {!!}
-}

monoid-cat : Category
monoid-cat .Object = Monoid
monoid-cat .Morphism M N = HomoMorphism M N
(monoid-cat ._then_ f g) .HomoMorphism.function
  = HomoMorphism.function g ∘′ HomoMorphism.function f
(monoid-cat then f) g .HomoMorphism.mempty-resp rewrite HomoMorphism.mempty-resp f | HomoMorphism.mempty-resp g = refl
(monoid-cat then f) g .HomoMorphism.<>-resp x y rewrite HomoMorphism.<>-resp f x y = HomoMorphism.<>-resp g _ _
monoid-cat .identity .HomoMorphism.function = id
monoid-cat .identity .HomoMorphism.mempty-resp = refl
monoid-cat .identity .HomoMorphism.<>-resp x y = refl
monoid-cat .then-assoc f g h = monHomEq _ _ refl
monoid-cat .then-identity f = monHomEq _ _ refl
monoid-cat .identity-then f = monHomEq _ _ refl


open import Data.Unit.Base using (⊤)
{-

fancier : Monoid → Category
fancier M .Object = ⊤
fancier M .Morphism = λ _ _ → Monoid.Carrier M
fancier M ._then_ = {!!}
fancier M .identity = {!!}
fancier M .then-assoc = {!!}
fancier M .then-identity = {!!}
fancier M .identity-then = {!!}
-}

-- Squish but for categories!

data Path {O : Set} (M : O → O → Set) (s : O) : O → Set where
  []  : Path M s s
  _∷_ : ∀ {m t} → M s m → Path M m t → Path M s t

_++_ : ∀ {O M} {s m t : O} → Path M s m → Path M m t → Path M s t
[]         ++ q = q
(step ∷ p) ++ q = step ∷ (p ++ q)

module _ (C : Category) where

  module C = Category C
  open C renaming (Object to O; Morphism to M)

  squish : ∀ {s t} → Path M s t → M s t
  squish []            = C.identity
  squish (step ∷ path) = step C.then squish path

  squish-++ : ∀ {s m t} (p : Path M s m) (q : Path M m t) →
     squish (p ++ q) ≡ squish p C.then squish q
  squish-++ = {!!}

-- Proof by reflection
