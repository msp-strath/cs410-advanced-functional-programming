module Week4 where

open import Data.Empty using (⊥)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)

-- ¬ is written \neg
-- Definition of Dec

data Dec (A : Set) : Set where
  yes : A → Dec A
  no  : ¬ A → Dec A

-----------------------------------------------------------------------
-- De Morgan's "laws"

variable
  A B C : Set

-- ⊎ is written \u+
-- ⇒ is written \r=
¬-⊎-⇒ : ¬ (A ⊎ B) → ¬ A × ¬ B
¬-⊎-⇒ ¬[a⊎b] = (λ z → ¬[a⊎b] (inj₁ z)) , (λ z → ¬[a⊎b] (inj₂ z))

-- × is written \x
-- ⇐ is written \l=
¬-⊎-⇐ : ¬ A × ¬ B → ¬ (A ⊎ B)
¬-⊎-⇐ (¬a , ¬b) (inj₁ a) = ¬a a
¬-⊎-⇐ (¬a , ¬b) (inj₂ b) = ¬b b


¬-×-⇒ : Dec A → ¬ (A × B) → ¬ A ⊎ ¬ B
¬-×-⇒ (yes a) ¬[a×b] = inj₂ (λ b → ¬[a×b] (a , b))
¬-×-⇒ (no ¬a) ¬[a×b] = inj₁ ¬a

¬-×-⇐ : ¬ A ⊎ ¬ B → ¬ (A × B)
¬-×-⇐ (inj₁ ¬a) (a , b) = ¬a a
¬-×-⇐ (inj₂ ¬b) (a , b) = ¬b b









-----------------------------------------------------------------------
-- Deciding Equality: computing a boolean, with a proof it is meaningful

open import Data.Nat.Base using (ℕ; zero; suc; pred)
open import Function.Base using (_∘′_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

nat-eq-dec : (m n : ℕ) → Dec (m ≡ n)
nat-eq-dec zero zero = yes refl
nat-eq-dec zero (suc n) = no λ ()
nat-eq-dec (suc m) zero = no λ ()
nat-eq-dec (suc m) (suc n) with nat-eq-dec m n
nat-eq-dec (suc m) (suc m) | yes refl = yes refl
nat-eq-dec (suc m) (suc n) | no m≢n = no (m≢n ∘′ cong pred)











-----------------------------------------------------------------------
-- Deciding evenness

variable m n p : ℕ

data Odd  : ℕ → Set
data Even : ℕ → Set


data Even where
  zero : Even zero
  suc : Odd n → Even (suc n)

data Odd where
  suc : Even n → Odd (suc n)

_ : Odd (suc (suc (suc (suc (suc zero)))))
_ = suc (suc (suc (suc (suc zero))))

even? : ∀ n → Dec (Even n)
odd?  : ∀ n → Dec (Odd n)


even? zero = yes zero
even? (suc n) with odd? n
... | yes oddn = yes (suc oddn)
... | no ¬oddn = no λ where (suc oddn) → ¬oddn oddn

odd? zero = no λ ()
odd? (suc n) with even? n
... | yes evenn = yes (suc evenn)
... | no ¬evenn = no λ where (suc evenn) → ¬evenn evenn



-- What would be a more useful statement?
-- evenOrOdd : ∀ n → Even n ⊎ Odd n
-- evenOrOdd = {!!}






-----------------------------------------------------------------------
-- Finding a witness
-- Computing a natural number, with a proof it is meaningful

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Product.Base using (∃)
open import Function.Base using (_$_)

{-# TERMINATING #-}
markov : {P : ℕ → Set} →
         (∀ n → Dec (P n)) →  -- we can decide the predicate P
         ¬ (¬ (∃ P)) →
         -- ¬ (∀ n → ¬ (P n)) →  -- we know it's not untrue of all naturals
         ∃ (λ n → P n)           -- so surely we can find a good one?
markov {P} p? ¬∀¬ = loop 0 where

  loop : ℕ → ∃ P
  loop i with p? i
  ... | yes pi = i , pi
  ... | no ¬pi = loop (suc i)

-- https://en.wikipedia.org/wiki/Markov%27s_principle


anOdd : ∃ Odd
anOdd = markov odd? (λ noOdds → noOdds (5 , suc (suc (suc (suc (suc zero))))))



-----------------------------------------------------------------------
-- Detour: equational proofs

-- This may be useful for the coursework so here we go.


open import Data.List.Base using (List; []; _∷_; _++_)

variable
  x : A
  xs : List A

postulate

  foldr : (A → B → B) → B → List A → B
  foldr-++ : ∀ (c : A → B → B) n xs ys → foldr c (foldr c n ys) xs ≡ foldr c n (xs ++ ys)

  length : List A → ℕ
  length-as-foldr : ∀ m (xs : List A) → m + length xs ≡ foldr (λ _ → suc) m xs


open import Relation.Binary.PropositionalEquality
  using (refl; sym; trans)

length-++ : (xs ys : List A) → length (xs ++ ys) ≡ length xs + length ys
length-++ xs ys = {!!}




-----------------------------------------------------------------------
-- Finding a witness
-- Building a gadget to build a proof for you!

_ : Even 100
_ = {!!}



-- isEven : (n : ℕ) → Even n











-----------------------------------------------------------------------
-- All vs. Any

-- Define All, Any

-- _ : All Even ?


open import Data.Vec using (Vec; []; _∷_)

--



{-
search : {P : A → Set} →
         (∀ n → Dec (P n)) →   -- we can decide the predicate P
         (xs : List A) →
         ¬ (All (¬_ ∘′ P) xs) → -- we know it's not untrue of all the values in the list
         Any P xs              -- so it must be true of at least one of them
-}
