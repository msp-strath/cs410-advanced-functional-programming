module Week04 where

open import Data.Empty using (⊥)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)

-----------------------------------------------------------------------
-- Decidability

-- ¬ is written \neg
-- Definition of Dec

-----------------------------------------------------------------------
-- De Morgan's "laws": conjunction and disjunction are dual

variable
  A B C : Set

-- ⊎ is written \u+
-- ⇒ is written \r=
-- × is written \x

-- PROVE
-- ¬-⊎-⇒ : ¬ (A ⊎ B) → ¬ A × ¬ B


-- ⇐ is written \l=


-- PROVE
-- ¬-⊎-⇐ : ¬ A × ¬ B → ¬ (A ⊎ B)


-- PROVE
-- ¬-×-⇒ : ¬ (A × B) → ¬ A ⊎ ¬ B


-- PROVE
-- ¬-×-⇐ : ¬ A ⊎ ¬ B → ¬ (A × B)







-----------------------------------------------------------------------
-- Deciding Equality: computing a boolean, with a proof it is meaningful

open import Data.Nat.Base using (ℕ; zero; suc; pred)
open import Function.Base using (_∘′_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)


-- DEFINE
-- nat-eq-dec : (m n : ℕ) → Dec (m ≡ n)











-----------------------------------------------------------------------
-- Beyond equality: arbitrary relations

variable m n p : ℕ

-- Odd and Even

-- EXAMPLE

-- even? : ∀ n → Dec (Even n)
-- odd?  : ∀ n → Dec (Odd n)



-- What would be a more useful statement?







-----------------------------------------------------------------------
-- Finding a witness
-- Computing a natural number, with a proof it is meaningful

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Product.Base using (∃)
open import Function.Base using (_$_)

-- DISCUSS Markov's Principle




-----------------------------------------------------------------------
-- Finding a witness
-- Building a gadget to build a proof for you!

open import Data.Unit


{-
isYes : Dec A → Set
-}


-- magic : (d : Dec A) {_ : isYes d} → A
-- magic (yes p) = p

{-
isEven : (n : ℕ) → {_ : isYes (even? n)} → Even n
isEven n {constraint} with even? n
... | yes evenn = evenn
-}

-- _ : Even 100
-- _ = magic (even? 100)


{-
_ : Even 101
_ = isEven 101
-}






-----------------------------------------------------------------------
-- Building proofs compositionally with predicate transformers

-----------------------------------------------------------------------
-- All vs. Any


-- DEFINE All

-- EXAMPLES All IsEven / All (Vec ℕ)



open import Data.Vec using (Vec; []; _∷_)


-- DEFINE Any


-- DISCUSS search
{-
search : {P : A → Set} →
         (∀ n → Dec (P n)) →   -- we can decide the predicate P
         (xs : List A) →
         ¬ (All (¬_ ∘′ P) xs) → -- we know it's not untrue of all the values in the list
         -- ¬ (¬ Any P xs) →
         Any P xs              -- so it must be true of at least one of them
search = {!!}
-}
