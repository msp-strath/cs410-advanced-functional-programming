module Week09 where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; module ≡-Reasoning)

open import Function using (_∘′_; id)

open import Week08 using (Monoid; _=Monoid>_)


-- A category is a fancy monoid:
--  - It has a type of objects
--  - It has a type of morphisms with a source & target object
--  - For each object, it has a unit morphism from the object to itself
--  - It has a way to combine two morphisms
--    (provided the target of the first is the source of the second)
--  - Combining morphisms is associative
--  - Combining morphisms has left & right unit laws

---------------------------------------------------------------------------
-- Category
---------------------------------------------------------------------------


open import Level using (Level; _⊔_)
variable c ℓ : Level

-- DEFINE
record Category c ℓ : Set (Level.suc (c ⊔ ℓ)) where


open Category























open import Data.Nat.Base using (ℕ; _≤_)
open import Data.Nat.Properties using (≤-refl; ≤-trans)


-- EXAMPLES: (Set, Nat (discrete & ≤))

























-- EXAMPLES:
-- Categories are fancy monoids
-- or... every Monoid gives rise to a boring category


---------------------------------------------------------------------------
-- Category of monoids












---------------------------------------------------------------------------
-- Squish but for categories!



---------------------------------------------------------------------------
-- Proof by reflection


-- DEFINE syntactic representation of lumps of compositions

-- DEFINE semantics via composition
-- DEFINE semantics equivalence

-- DEFINE evaluation
-- DEFINE normalisation

-- DEFINE normalisation equivalence


-- PROVE normalisation preserves semantics



-- PROVE normalisation equivalence implies semantics equivalence



-- USE for proof
