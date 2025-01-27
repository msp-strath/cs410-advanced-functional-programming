module Week2 where

-- Looked back at splitN





---------------------------------------------------------
-- Propositional equality

data _≡_ {X : Set}(a : X) : X -> Set where -- \==
  refl : a ≡ a

-- 5 ≡ (3 + 2) has an element

-- 17 ≡ 42 does not have an element

-- unit tests
open import Data.Nat.Base using (ℕ; zero; suc; _+_)

test1 : 5 ≡ (3 + 2)
test1 = refl

-- test2 : 17 ≡ 42
-- test2 = refl

cong : {X Y : Set} → (f : X → Y) → {x x' : X} → x ≡ x' → f x ≡ f x'
cong f {x = x} refl = refl {a = f x}

---------------------------------------------------------
-- Proofs by induction

test3 : (n : ℕ) → (n + 1) ≡ (1 + n)
test3 zero = refl
test3 (suc n) = cong suc (test3 n)


open import Function.Base using (id; _∘′_)
open import Data.Vec.Base using (Vec; []; _∷_; zipWith; replicate)

zipWith-replicate :
  ∀ {X Y Z : Set} (f : X → Y → Z) x y n →
  zipWith f (replicate n x) (replicate n y)
  ≡ replicate n (f x y)
zipWith-replicate = {!!}



---------------------------------------------------------
-- Annoying type errors

open import Data.Vec.Base using (_++_)
-- associativity of _++_
