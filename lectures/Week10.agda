module Week10 where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; cong; cong₂; sym; module ≡-Reasoning)

open import Function using (_∘′_; id)

open import Week08 using (Monoid; _=Monoid>_; monHomEq)
open import Week09 using
  ( Category; Agda; ℕ≤; monoids
  ; Path; reflexive; transitive
  ; crush; crush-reflexive; crush-transitive
  )

---------------------------------------------------------------------------
-- Functors






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
