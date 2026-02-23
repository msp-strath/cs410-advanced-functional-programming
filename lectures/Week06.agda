module Week06 where

open import Data.Empty using (⊥)
open import Data.Nat.Base using (ℕ; _+_; _≤_; z≤n)
open import Data.Bool.Base using (Bool; true; false;  if_then_else_)
open import Data.Product.Base using (_,_; ∃)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Food for thoughts wrt last week

-- CHECKING
-- What if we have overloaded constructs e.g. `_+_` for all the
-- numerical types? Inference vs. checking, information propagation

-- UNIQUE TYPES
-- We could have proven that if two typed terms erase to the same
-- raw term then their respective types are equal. Is that always
-- the case? Can we always produce a most general type?

-- _ : {!!}
-- _ = 2 , z≤n


-- CLOSED TERMS
-- How computationally interesting is the language we saw last
-- week?












------------------------------------------------------------------------
-- Adding scoped-and-typed variables to the syntax

data Ty : Set where
  bool nat : Ty

-- DEFINE contexts Ctx
-- and give examples



-- DEFINE membership
-- and give examples





-- DEFINE typed-and-scoped expressions



-- DEFINE boolToNat

-- DEFINE double



------------------------------------------------------------------------
-- Extending the semantics


-- DEFINE TVal
-- DEFine CVal

-- Examples of CVal



-- DEFINE teval


-- Examples



------------------------------------------------------------------------
-- Transformations


-- Transformation : Set
-- Transformation = ∀ {Γ T} → TExpr Γ T → TExpr Γ T


-- DEFINE a constant folding operation



-- DEFINE a semantic equivalence _≋_ over typed terms
-- DEFINE Correctness of a transformation


-- PROVE your constant folding operation correct


-- SUGGEST more optimisations
