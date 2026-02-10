module Week04 where

open import Data.Empty using (⊥)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; ∃; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)

-----------------------------------------------------------------------
-- Decidability

-- ¬ is written \neg
-- Definition of Dec
data Dec (A : Set) : Set where
  yes :  A → Dec A
  no : ¬ A → Dec A


-----------------------------------------------------------------------
-- De Morgan's "laws": conjunction and disjunction are dual

variable
  A B C : Set

-- ⊎ is written \u+
-- ⇒ is written \r=
-- × is written \x

-- PROVE
¬-⊎-⇒ : ¬ (A ⊎ B) → ¬ A × ¬ B
¬-⊎-⇒ ¬A⊎B = (λ a → ¬A⊎B (inj₁ a))
           , (λ b → ¬A⊎B (inj₂ b))

-- ⇐ is written \l=


-- PROVE
¬-⊎-⇐ : ¬ A × ¬ B → ¬ (A ⊎ B)
¬-⊎-⇐ (na , nb) (inj₁ a) = na a
¬-⊎-⇐ (na , nb) (inj₂ b) = nb b

-- PROVE
¬-×-⇒ : Dec A → ¬ (A × B) → ¬ A ⊎ ¬ B
¬-×-⇒ (yes a) ¬[A×B] = inj₂ (λ b → ¬[A×B] (a , b))
¬-×-⇒ (no na) ¬[A×B] = inj₁ na

-- PROVE
¬-×-⇐ : ¬ A ⊎ ¬ B → ¬ (A × B)
¬-×-⇐ (inj₁ na) (a , b) = na a
¬-×-⇐ (inj₂ nb) (a , b) = nb b



-----------------------------------------------------------------------
-- Deciding Equality: computing a boolean, with a proof it is meaningful

open import Data.Nat.Base using (ℕ; zero; suc; pred)
open import Function.Base using (_∘′_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)


-- DEFINE
nat-eq-dec : (m n : ℕ) → Dec (m ≡ n)
-- base case
nat-eq-dec zero    zero    = yes refl
nat-eq-dec zero    (suc n) = no (λ ())
-- inductive case
nat-eq-dec (suc m) zero    = no (λ ())
nat-eq-dec (suc m) (suc n) with nat-eq-dec m n
nat-eq-dec (suc m) (suc .m) | yes refl = yes refl
nat-eq-dec (suc m) (suc n) | no m≢n = no (m≢n ∘′ cong pred)








-----------------------------------------------------------------------
-- Beyond equality: arbitrary relations

open import Data.Bool.Base using (Bool; true; false)

variable m n p : ℕ

-- Odd and Even

data Parity : Bool -> ℕ -> Set where
  even0 :                   Parity false zero
  oddS  : Parity false n -> Parity true  (suc n)
  evenS : Parity true  n -> Parity false (suc n)

Even Odd : ℕ -> Set
Even = Parity false
Odd = Parity true

-- EXAMPLE

_ : Even 6
_ = evenS (oddS (evenS (oddS (evenS (oddS even0)))))

_ : Odd 1
_ = oddS even0

even? : ∀ n → Dec (Even n)
odd?  : ∀ n → Dec (Odd n)

even? zero    = yes even0
even? (suc n) with odd? n
... | yes oddn = yes (evenS oddn)
... | no noddn = no λ where (evenS oddn) → noddn oddn

odd? zero    = no (λ ())
odd? (suc n) with even? n
... | yes evenn = yes (oddS evenn)
... | no nevenn = no λ where (oddS evenn) → nevenn evenn

_ : even? 10 ≡ yes _
_ = refl


-- What would be a more useful statement?


parity? : (m : ℕ) → ∃ (λ (b : Bool) → Parity b m)
parity? = {!!}



-----------------------------------------------------------------------
-- Announcement: interesting online seminar
-- The Cognitive and Human Factors of Formal Methods
-- by Shriram Krishnamurthi from Brown University
-- (zoom link on Teams)
-- https://informatics.ed.ac.uk/lfcs/lfcs-seminar-tuesday-10-february-shriram-krishnamurthi




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
