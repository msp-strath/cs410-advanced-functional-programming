module Week7 where

---------------------------------------------------------------------------
-- Monoids
---------------------------------------------------------------------------

-- Remember monoids? A monoid is a set, together with a binary
-- operation on it, which has a unit, and which satisfies the axiom of
-- associativity -- that is, "brackets are not needed".

-- define monoid as a record
record Monoid : Set₁ where


-- Your favourite example of a monoid












---------------------------------------------------------------------------
-- Parametrised proofs
---------------------------------------------------------------------------

-- Parametrised module
module MonProofs (Mon : Monoid) where

  -- puts the operations and axioms in scope
  --  open Monoid Mon renaming (Carrier to M)


  -- We can "squish together" all the elements in a list
  open import Data.List.Base using (List; []; _∷_; _++_)
  -- squish : List M → M
  -- squish = {!!}










  -- And squishing works in any left-right respecting order
  -- For instance:

  -- squish-++ : ∀ {xs ys} → squish (xs ++ ys) ≡ ?
  -- squish-++ = ?





---------------------------------------------------------------------------
-- Homomorphisms
---------------------------------------------------------------------------


  -- define Monoid Homomorphisms
  -- prove they commute with squishing
