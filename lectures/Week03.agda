------------------------------------------------------------------------
-- WEEK 3
------------------------------------------------------------------------


------------------------------------------------------------------------
-- Coursework
--
-- Y'all have hopefully already started having a look and maybe even
-- proven a couple of simple properties.

-- Deadline Week 5 - Thu 19th February 5pm as indicated on myplace


------------------------------------------------------------------------
-- Cliffhanger


open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong)

{-
subst : {A : Set} {x y : A} →
  -- x equals y
  x ≡ y →
  -- meaning any property of x is also a property of y
  (P : A → Set) → P x → P y
-}

-- DEFINE sym, trans in terms of subst

sym : {X : Set} -> {x y : X} -> x ≡ y -> y ≡ x
sym {x = x} x≡y = subst (λ tgt → tgt ≡ x) x≡y refl

trans : {X : Set} -> {x y z : X} -> x ≡ y -> y ≡ z → x ≡ z
trans {x = x} {y = y} {z = z} x≡y =
  subst (λ tgt → tgt ≡ z → x ≡ z) x≡y (λ z → z)

trans' : {X : Set} -> {x y z : X} -> x ≡ y -> y ≡ z → x ≡ z
trans' x≡y y≡z = subst (_ ≡_) y≡z x≡y

-- More generally:
-- PROVE prop eq & Leibniz eq are equivalent

open import Level using (Level)

infix 1 _≡ᴸ_
_≡ᴸ_ : {ℓ : Level} {A : Set ℓ} (x y : A) → Set (Level.suc ℓ)
_≡ᴸ_ {ℓ = ℓ} {A = A} x y = (P : A → Set ℓ) → P x → P y

variable
  ℓ : Level
  A : Set ℓ
  x y : A

toLeibniz : x ≡ y → x ≡ᴸ y
toLeibniz = λ x≡y P → subst P x≡y

fromLeibniz : x ≡ᴸ y → x ≡ y
fromLeibniz x≡ᴸy = x≡ᴸy (_ ≡_) refl


------------------------------------------------------------------------
-- This week: Curry Howard correspondence
--
-- The observation that computing and proving are quite similar.
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_)

-- Going back to 1+n ≡ n+1; 17 ≡ 42

open import Relation.Nullary using (¬_)

_ : ¬ (17 ≡ 42)
_ = λ ()


------------------------------------------------------------------------
-- Empty type

-- DEFINE ⊥
data ⊥ : Set where


-- DISCUSS explosion principle
_ : ⊥ → A
_ = λ ()


-- PROVE by diagonalisation
0≢1 : 0 ≡ 1 → ⊥
0≢1 0≡1 = subst P 0≡1 0 where

  P : ℕ → Set
  P zero = ℕ -- something inhabited
  P (suc _) = ⊥ -- the target goal

-- What about _+_ ≡ _*_ ?
+≢* : _+_ ≡ _*_ → ⊥
+≢* +≡* = 0≢1 (sym (cong (λ f → f 0 1) +≡*))


------------------------------------------------------------------------
-- Negation

-- DEFINE Not
Not : Set → Set
Not A = A → ⊥

-- Prove Not ⊥
_ : Not ⊥
_ = λ z → z

-- PROVE double negation introduction
dni : A -> Not (Not A)
dni a na = na a

-- DISCUSS double negation elimination

{-
-- We cannot hope to implement this:
dne : {X : Set} -> Not (Not X) -> X
dne notnotx = {!!}
-}

dne' : {X : Set} -> Not (Not (Not X)) -> Not X
dne' notnotnotx x = notnotnotx (dni x)



------------------------------------------------------------------------
-- Implication

-- DEFINE Implies
Implies : Set → Set → Set
Implies A B = A → B

-- PROVE Not (Implies (0 ≡ 0) ⊥)
_ : Not (Implies (0 ≡ 0) ⊥)
_ = dni refl

-- DISCUSS Not (Implies A B) vs. a more constructive formulation
-- NotImplies A B = {!A ∧ (Not B)!}




















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
