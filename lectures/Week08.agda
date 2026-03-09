module Week08 where

---------------------------------------------------------------------------
-- Monoids
---------------------------------------------------------------------------

-- Remember monoids? A monoid is a set, together with a binary
-- operation on it, which has a unit, and which satisfies the axiom of
-- associativity -- that is, "brackets are not needed".

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; module ≡-Reasoning)

-- DEFINE Monoid as a record






-- EXAMPLES: your favourite monoids

open import Data.List.Base using (List; []; _∷_)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Function.Base using (id; _∘′_)


---------------------------------------------------------------------------
-- Generic programs
-- Parametric vs. ad-hoc polymorphism


-- foldr as a monoid homomorphism


---------------------------------------------------------------------------
-- Parametrised proofs
---------------------------------------------------------------------------

-- DEFINE squish/crush/ whatever you want to call it





-- PROVE it is a monoid homomorphism



-- DEFINE the acc-based version, prove it is equivalent

---------------------------------------------------------------------------
-- Homomorphisms
---------------------------------------------------------------------------

-- DEFINE Monoid Homomorphisms

-- PROVE they commute with squishing

---------------------------------------------------------------------------
-- Category
---------------------------------------------------------------------------

-- It's just a fancy monoid
-- DEFINE it

-- EXAMPLES
