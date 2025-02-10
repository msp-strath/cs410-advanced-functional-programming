module Week4 where

open import Data.Empty using (⊥)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)

-- ¬ is written \neg
-- Definition of Dec

-----------------------------------------------------------------------
-- De Morgan's "laws"

variable
  A B C : Set

-- ⊎ is written \u+
-- ⇒ is written \r=
-- ¬-⊎-⇒ : ¬ (A ⊎ B) → ¬ A × ¬ B


-- × is written \x
-- ⇐ is written \l=
-- ¬-⊎-⇐ : ¬ A × ¬ B → ¬ (A ⊎ B)

-- ¬-×-⇒ : ¬ (A × B) → ¬ A ⊎ ¬ B

-- ¬-×-⇐ : ¬ A ⊎ ¬ B → ¬ (A × B)










-----------------------------------------------------------------------
-- Deciding Equality: computing a boolean, with a proof it is meaningful

open import Data.Nat.Base using (ℕ; zero; suc; pred)
open import Function.Base using (_∘′_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

-- nat-eq-dec : (m n : ℕ) → Dec (m ≡ n)












-----------------------------------------------------------------------
-- Deciding evenness

variable m n p : ℕ

data Odd  : ℕ → Set
data Even : ℕ → Set


-- even? : ∀ n → Dec (Even n)
-- odd?  : ∀ n → Dec (Odd n)












-- What would be a more useful statement?







-----------------------------------------------------------------------
-- Finding a witness
-- Computing a natural number, with a proof it is meaningful

open import Data.Nat.Base using (_≤_; z≤n; s≤s)
open import Data.Product.Base using (∃)
open import Function.Base using (_$_)

{-
markov : {P : ℕ → Set} →
         (∀ n → Dec (P n)) →  -- we can decide the predicate P
         ¬ (∀ n → ¬ (P n)) →  -- we know it's not untrue of all naturals
         ∃ P                  -- so surely we can find a good one?
-}

-- https://en.wikipedia.org/wiki/Markov%27s_principle


-- anOdd : ∃ Odd
















-----------------------------------------------------------------------
-- All vs. Any

open import Data.List.Base using (List; []; _∷_)

variable
  x : A
  xs : List A

-- Define All, Any

{-
search : {P : ℕ → Set} →
         (∀ n → Dec (P n)) →   -- we can decide the predicate P
         (xs : List ℕ) →
         ¬ (All (¬_ ∘′ P) xs) → -- we know it's not untrue of all naturals in the list
         Any P xs              -- so it must be true of at least one of them
-}
