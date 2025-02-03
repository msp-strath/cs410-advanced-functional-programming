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

-- More generally: prop eq & Leibnitz eq are equivalent

infix 4 _≡ᴸ_

_≡ᴸ_ : {X : Set} (x y : X) → Set₁
x ≡ᴸ y = (P : _ → Set) → P x → P y

toLeibnitz : ∀ {X : Set} {x y : X} → x ≡ y → x ≡ᴸ y
toLeibnitz eq P px = subst P eq px

fromLeibnitz : ∀ {X : Set} {x y : X} → x ≡ᴸ y → x ≡ y
fromLeibnitz {x = x} lbz = lbz (\ y -> x ≡ y) refl


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

{-
-- We cannot hope to implement this:
dne : {X : Set} -> Not (Not X) -> X
dne notnotx = {!!}
-}

-- Conor?
-- Implication


-- Conjunction


-- Disjunction


-- De Morgan's laws?
