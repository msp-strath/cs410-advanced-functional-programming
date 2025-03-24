open import Data.Nat.Base using (ℕ; suc)
open import Data.Product.Base as Prod using (_×_; _,_)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤)

open import Function.Base using (id)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

variable
  X Y : Set

------------------------------------------------------------------------------
-- Universe of descriptions

-- Desc

-- Example: Maybe

-- Meaning

-- Examples: nothing, just


-- Meaning is functorial


-- Example: mapping over just


------------------------------------------------------------------------------
-- Fixpoints of functors

-- Example: Nat as nested Maybes, zeros, and suc


-- Algebras

-- example: addAlg replacing 0 with n

-- Folds over fixpoints

-- example: add as a fold


-- example: run add (fromℕ/toℕ for readability?)
