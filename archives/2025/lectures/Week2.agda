module Week2 where

-- Looked back at splitN


---------------------------------------------------------
-- Propositional equality

data _≡_ {X : Set}(a : X) : X -> Set where
-- relaxed definition of equality
-- data _≡_ {X : Set}(a : X) : {Y : Set} → Y -> Set where -- \==
  refl : a ≡ a

-- 5 ≡ (3 + 2) has an element

-- 17 ≡ 42 does not have an element

-- unit tests
open import Data.Nat.Base using (ℕ; zero; suc; _+_)

test1 : 5 ≡ (3 + 2)
test1 = refl

-- test2 : 17 ≡ 42
-- test2 = refl

cong : {X Y : Set} →
  (f : X → Y) →
  {x x' : X} → x ≡ x' →
  f x ≡ f x'
cong f {x = x} refl = refl {a = f x}

---------------------------------------------------------
-- Proofs by induction

test3 : (n : ℕ) → (n + 1) ≡ (1 + n)
test3 zero = refl
test3 (suc n) = cong suc (test3 n)


open import Function.Base using (id; _∘′_)
open import Data.Vec.Base using (Vec; []; _∷_; zipWith; replicate)


{-

    ----------------------------------------
    |   a₁       ⋯     aᵢ    ⋯       aₙ    |
    ----------------------------------------
 f
    ----------------------------------------
    |       b₁   ⋯        bᵢ    ⋯       bₙ |
    ----------------------------------------

    ----------------------------------------
 =  | f a₁  b₁   ⋯   f aᵢ bᵢ    ⋯  f aₙ bₙ |
    ----------------------------------------

-}



zipWith-replicate :
  ∀ {X Y Z : Set} (f : X → Y → Z) x y n →
  zipWith f (replicate n x) (replicate n y)
  ≡ replicate n (f x y)
zipWith-replicate f x y zero = refl
zipWith-replicate f x y (suc n)
  = cong (_ ∷_) (zipWith-replicate f x y n)

  -- _∷_   : unapplied constructor
  -- _ ∷_  : constructor with first arg
  -- _∷ _  : constructor with second arg
  -- _ ∷ _ : fully applied constructor



-- Not true in e.g. OCaml!


---------------------------------------------------------
-- Annoying type errors

open import Data.Vec.Base using (_++_)
-- associativity of _++_


vecAppendAssoc : {X : Set}{l n m : ℕ}
  (xs : Vec X l)(ys : Vec X n)(zs : Vec X m)
  -> ((xs ++ ys) ++ zs) ≡ {!(xs ++ (ys ++ zs))!}
vecAppendAssoc xs ys zs = {!!}



-- symmetry

sym : ∀ {X} {x y : X} → x ≡ y → y ≡ x
sym {x = x} {y = y} refl = refl

trans : ∀ {X} {x y z : X} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl


{-
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; module ≡-Reasoning)
open ≡-Reasoning

trans : {X : Set} {x y z : X} → x ≡ y → z ≡ y → x ≡ z
trans {x = x} {y = y} {z = z} x≡y z≡y = begin
  x ≡⟨ x≡y ⟩
  y ≡⟨ z≡y ⟨
  z ∎

-}
--------------------------------

subst :
  ∀ {X} (P : X → Set) →
  ∀ {x y : X} → x ≡ y →
  P x → P y
subst P refl px = px


cast : ∀ {A m n} → m ≡ n → Vec A m → Vec A n
cast {A} = subst (Vec A)
