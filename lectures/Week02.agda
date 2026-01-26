module Week02 where

---------------------------------------------------------
-- CW1 released

-- https://gitlab.cis.strath.ac.uk/clb11207/cs410-2026-coursework

-- Fork a *private* copy
-- Invite me as Developer so that I can see it.

---------------------------------------------------------
-- Look back at unAppending / splitN


---------------------------------------------------------
-- Today: Equality & Proofs




---------------------------------------------------------
-- Propositional equality



-- DEFINE equality


-- DEFINE unit tests:
-- 5 ≡ (3 + 2) has an element
-- 17 ≡ 42 does not have an element

open import Data.Nat.Base using (ℕ; zero; suc; _+_)




-- PROVE cong(ruence)




---------------------------------------------------------
-- Proof by induction on the natural numbers



-- PROVE that 1 is the neutral element for (ℕ, _+_)
-- Pro-tip: to know how to type the unicode character under
-- your cursor in emacs, use `C-u C-x =`.

-- +-identityʳ : (n : ℕ) → (n + 1) ≡ (1 + n)



---------------------------------------------------------
-- Proof by structural induction on a list


open import Function.Base using (id; _∘′_)
open import Data.Vec.Base using (Vec; []; _∷_; zipWith; replicate)


{-

    ----------------------------------------
    |   a₁       ⋯     aᵢ    ⋯       aₙ    |
    ----------------------------------------
 f
    ----------------------------------------
    |       b₁   ⋯        bᵢ    ⋯       bₙ |
    ----------------------------------------

    ----------------------------------------
 =  | f a₁  b₁   ⋯   f aᵢ bᵢ    ⋯  f aₙ bₙ |
    ----------------------------------------

-}


-- PROVE that zipWith over constant vector gives
-- a constant vector


-- zipWith-replicate : ...



---------------------------------------------------------
-- Annoying type errors

open import Data.Vec.Base using (_++_)


-- associativity of _++_

-- vecAppendAssoc : ...




---------------------------------------------------------
-- The equational reasoning kit

-- PROVE symmetry of _≡_
-- PROVE transitivity of _≡_


{-
-- PROVE transitivity using ≡-Reasoning
-}

-- PROVE substitution / Leibniz' Law / the indiscernibility of identicals
-- subst


-- DEFINE cast, the function transporting vectors
-- along identity proofs
