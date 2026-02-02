------------------------------------------------------------------------
-- WEEK 3
------------------------------------------------------------------------


------------------------------------------------------------------------
-- Coursework
--
-- Y'all have hopefully already started having a look and maybe even
-- proven a couple of simple properties.

-- Target deadline Week 5 - Thu 19th February 5pm as indicated on
-- myplace






------------------------------------------------------------------------
-- Cliffhanger


open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong)

-- DEFINE sym, trans in terms of subst

sym : {X : Set} -> {x y : X} -> x ≡ y -> y ≡ x
sym = {!!}

trans : {X : Set} -> {x y z : X} -> x ≡ y -> y ≡ z → x ≡ z
trans = {!!}

-- More generally:
-- PROVE prop eq & Leibniz eq are equivalent


------------------------------------------------------------------------
-- This week: Curry Howard correspondence
--
-- The observation that computing and proving are quite similar.
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_)

-- Going back to 1+n ≡ n+1; 17 ≡ 42

{-
_ : 17 ≡ 42
_ = refl -- wrong
-}


------------------------------------------------------------------------
-- Empty type

-- DEFINE ⊥

-- DISCUSS explosion principle

-- REVISIT ¬ (17 ≡ 42)

-- PROVE by diagonalisation
-- 0≢1 : 0 ≡ 1 → ⊥


-- What about _+_ ≡ _*_ ?
-- +≢* : _+_ ≡ _*_ → ⊥




------------------------------------------------------------------------
-- Negation

-- DEFINE Not

-- Prove Not ⊥

-- PROVE double negation introduction


-- DISCUSS double negation elimination

{-
-- We cannot hope to implement this:
dne : {X : Set} -> Not (Not X) -> X
dne notnotx = {!!}
-}



------------------------------------------------------------------------
-- Implication

-- DEFINE Implies

-- PROVE Not (Implies (0 ≡ 0) ⊥)

-- DISCUSS Not (Implies A B) vs. a more constructive formulation





------------------------------------------------------------------------
-- Conjunction
--    A         B
-- -----------------
--       A ∧ B

-- DEFINE And

-- DEFINE diagonal : A → A ∧ A

-- DEFINE swap : A ∧ B → B ∧ A


-- Refutations
-- DEFINE NotImplies

-- PROVE NotImplies (0 ≡ 0) ⊥



------------------------------------------------------------------------
-- Disjunction

-- DEFINE Or

-- PROVE distribute : A ∧ (B ∨ C) → (A ∧ B) ∨ (A ∧ C)



------------------------------------------------------------------------
-- Truth

-- DEFINE ⊤

-- eta equality?




------------------------------------------------------------------------
-- Excluded middle (?)

-- DEFINE LEM

-- DISCUSS LEM & ¬¬LEM


open import Function.Base using (case_of_)

-- PROVE LEM → DNE
-- PROVE dne⇒lem


------------------------------------------------------------------------
-- De Morgan's laws

-- ∀ b c → not (b ∧ c) ≡ not b ∨ not c




------------------------------------------------------------------------
-- A DSL where classical reasoning applies: Decidable types

-- DEFINE Dec

-- PROVE dne-dec

-- PROVE nat-eq-dec
