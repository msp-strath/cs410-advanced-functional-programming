------------------------------------------------------------------------
-- WEEK 3
------------------------------------------------------------------------


------------------------------------------------------------------------
-- Coursework
--
-- Y'all have hopefully already started having a look and maybe even
-- proven a couple of simple properties.








------------------------------------------------------------------------
-- Cliffhanger


open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

-- Fred?
-- sym, trans in terms of subst



-- More generally: prop eq & Leibnitz eq are equivalent

infix 4 _≡ᴸ_

_≡ᴸ_ : {X : Set} (x y : X) → Set₁
x ≡ᴸ y = (P : _ → Set) → P x → P y

toLeibnitz : ∀ {X : Set} {x y : X} → x ≡ y → x ≡ᴸ y
toLeibnitz eq = {!!}

fromLeibnitz : ∀ {X : Set} {x y : X} → x ≡ᴸ y → x ≡ y
fromLeibnitz lbz = {!!}


------------------------------------------------------------------------
-- Curry Howard

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_)

-- Guillaume?
-- Going back to 1+n ≡ n+1; 17 ≡ 42


-- Empty type
-- Negation

-- What about _+_ ≡ _*_ ?


-- Double negation?


-- Conor?
-- Implication


-- Conjunction


-- Disjunction


-- De Morgan's laws?
