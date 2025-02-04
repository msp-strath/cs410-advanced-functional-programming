------------------------------------------------------------------------
-- WEEK 3
------------------------------------------------------------------------


------------------------------------------------------------------------
-- Coursework
--
-- Y'all have hopefully already started having a look and maybe even
-- proven a couple of simple properties.

-- Target deadline Week 5 (Thu 20 Feb [all mentions of Sat 15 Feb are false])






------------------------------------------------------------------------
-- Cliffhanger


open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong)

-- Fred?
-- sym, trans in terms of subst

sym : {X : Set} -> {x y : X} -> x ≡ y -> y ≡ x
sym {x = x} p = subst (λ z → z ≡ x) p refl

trans : {X : Set} -> {x y z : X} -> x ≡ y -> y ≡ z → x ≡ z
trans {x = x} {y} {z} p = subst (λ y → y ≡ z → x ≡ z) p (λ r → r)

-- More generally: prop eq & Leibniz eq are equivalent

infix 4 _≡ᴸ_

_≡ᴸ_ : {X : Set} (x y : X) → Set₁
x ≡ᴸ y = (P : _ → Set) → P x → P y

toLeibniz : ∀ {X : Set} {x y : X} → x ≡ y → x ≡ᴸ y
toLeibniz eq P px = subst P eq px

fromLeibniz : ∀ {X : Set} {x y : X} → x ≡ᴸ y → x ≡ y
fromLeibniz {x = x} lbz = lbz (\ y -> x ≡ y) refl


------------------------------------------------------------------------
-- Curry Howard

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_)

-- Guillaume?
-- Going back to 1+n ≡ n+1; 17 ≡ 42

{-
_ : 17 ≡ 42
_ = refl -- wrong
-}

data ⊥ : Set where

_ : 17 ≡ 42 → ⊥
_ = λ ()

0≢1 : 0 ≡ 1 → ⊥
0≢1 = λ p → subst P p 7
 where
  P : ℕ → Set
  P 0 = ℕ -- something inhabited
  P 1 = ⊥ -- something empty
  P n = ℕ -- anything

-- in Haskell: \ x -> case x of {}

explosion : ⊥ → {A : Set} → A
explosion ()



-- Empty type
-- Negation

-- What about _+_ ≡ _*_ ?

broken : _+_ ≡ _*_ → ⊥
broken eq = 0≢1 (sym (cong (λ f → f 1 0) eq))


-- Double negation?
Not : Set -> Set
Not X = X -> ⊥

_ : Not ⊥
_ = \ x -> x

dni : {X : Set} -> X -> Not (Not X)
dni x notx = notx x

DNE : Set₁
DNE = (B : Set) → Not (Not B) → B

{-
-- We cannot hope to implement this:
dne : {X : Set} -> Not (Not X) -> X
dne notnotx = {!!}
-}

-- Implication

Implies : Set → Set → Set
Implies A B = A → B

_ : Not (Implies (0 ≡ 0) ⊥)
_ = dni refl

-- Not (Implies A B)
-- A × Not B

-- Conjunction
--    A         B
-- -----------------
--       A ∧ B

record And (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B
open And

diagonal : ∀ {A} → A → And A A
diagonal prfA = prfA , prfA

swap : ∀ {A B} → And A B → And B A
-- swap (prfA , prfB) = prfB , prfA
swap prfAB = snd prfAB , fst prfAB

-- Refutations
NotImplies : Set → Set → Set
NotImplies A B = And A (Not B)

_ : NotImplies (0 ≡ 0) ⊥
_ = refl , λ x → x

-- Disjunction
data Or (A B : Set) : Set where
  inl : A -> Or A B
  inr : B -> Or A B

distribute : forall {A B C} -> And A (Or B C) -> Or (And A B) (And A C)
distribute (a , inl b) = inl (a , b)
distribute (a , inr c) = inr (a , c)

record ⊤ : Set where
  constructor tt

_ : ℕ
_ = 42

_ : ⊤
_ = _

_ : (x : ⊤) → x ≡ tt
_ = λ x → refl

-- Excluded middle?

LEM : Set₁
LEM = (B : Set) → Or B (Not B)

{-
-- We cannot hope to prove this either (if we could, we could solve the unsolvable Halting Problem)
lem : LEM
lem B = {!!}
-}

-- ¬¬LEM : (LEM → ⊥) → ⊥

open import Function.Base using (case_of_)

lem⇒dne : LEM → DNE
lem⇒dne lem B ¬¬b = case lem B of λ where
  (inl b)  → b
  (inr ¬b) → explosion (¬¬b ¬b)

dne⇒lem : DNE → LEM
dne⇒lem dne B = dne (Or B (Not B)) f
 where
  f : (Or B (B → ⊥) → ⊥) → ⊥
  f not-[b-or-not-b] = not-[b-or-not-b] (inr (λ b → not-[b-or-not-b] (inl b)))

------------------------------------------------------------------------
-- De Morgan's laws

-- ∀ b c → not (b ∧ c) ≡ not b ∨ not c




------------------------------------------------------------------------
-- A DSL where classical reasoning applies: Decidable types


Dec : Set → Set
Dec B = Or B (Not B)

dne-dec : ∀ {B} → Dec B → Not (Not B) → B
dne-dec dec = {!!}


nat-dec : (m n : ℕ) → Dec (m ≡ n)
nat-dec = ?
