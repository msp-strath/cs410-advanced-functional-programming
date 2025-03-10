module Week8 where

---------------------------------------------------------------------------
-- Monoids
---------------------------------------------------------------------------

-- Remember categories? A category is a fancy monoid:
--   - It has a type of objects
--   - It has a type of morphism with a source & target object
--   - For each object, it has a unit morphism from the object to itself
--   - It has a way to combine two morphisms
--      (provided the target of one is the source of the other)
--   - Combining morphisms is associative


open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; module ≡-Reasoning)

open import Week7 hiding (Category)

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

-- Squish but for categories!

-- Proof by reflection
