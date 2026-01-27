module Week02 where

---------------------------------------------------------
-- CW1 released

-- https://gitlab.cis.strath.ac.uk/clb11207/cs410-2026-coursework

-- Fork a *private* copy
-- Invite me as Developer so that I can see it.

---------------------------------------------------------
-- Look back at unAppending / splitN
-- open import Week01

---------------------------------------------------------
-- Today: Equality & Proofs




---------------------------------------------------------
-- Propositional equality


-- DEFINE propositional equality
data _≡_ {A : Set} (a : A) : A → Set where
  refl : a ≡ a


-- DEFINE unit tests:
-- 5 ≡ (3 + 2) has an element
-- 17 ≡ 42 does not have an element

open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.String.Base using (String)

_ : 5 ≡ (3 + 2)
_ = refl

open import Relation.Nullary using (¬_)
_ : ¬ (17 ≡ 42)
_ = λ ()

{-
data _≅_ {A : Set} (a : A) : {B : Set} → B → Set where
  refl : a ≅ a

_ : ¬ (17 ≅ "hello")
_ = λ ()
-}

-- PROVE cong(ruence)
cong : {S T : Set}(f : S -> T){x y : S} -> x ≡ y -> f x ≡ f y
cong f {x} {.x} refl = refl

cong2 : {S T U : Set}(f : S -> T → U)
  {x y : S} -> x ≡ y ->
  {a b : T} -> a ≡ b ->
  f x a ≡ f y b
cong2 f refl refl = refl



---------------------------------------------------------
-- Proof by induction on the natural numbers



-- PROVE that 1 + n ≡ n + 1
-- Pro-tip: to know how to type the unicode character under
-- your cursor in emacs, use `C-u C-x =`.

+-1 : (n : ℕ) → (n + 1) ≡ (1 + n)
+-1 zero    = refl
+-1 (suc n) = cong suc (+-1 n)
{-  let ih = +-1 n in
  cong suc ih
-}

---------------------------------------------------------
-- Proof by structural induction on a list


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


-- PROVE that zipWith over constant vector gives
-- a constant vector


zipWith-replicate : {A B C : Set}(f : A -> B -> C)(a : A) (b : B) ->
  {n : ℕ} -> zipWith f (replicate n a) (replicate n b) ≡ replicate n (f a b)
zipWith-replicate f a b {zero} = refl
zipWith-replicate f a b {suc n} = cong (_ ∷_) (zipWith-replicate f a b {n})

open import Data.Vec.Base using (map)
open import Function.Base using (_∘_)

map-compose : ∀ {A B C : Set} {n} (g : B → C) (f : A → B)
  (as : Vec A n) → map g (map f as) ≡ map (g ∘ f) as
map-compose g f []       = refl
map-compose g f (a ∷ as) = cong (_ ∷_) (map-compose g f as)

-- _∷_ : constructor
-- _∷ _ : giving the second argument
-- _ ∷_ : giving the first argument
-- _ ∷ _ : fully applied



map-compose' : ∀ {A B C : Set} {n} (g : B → C) (f : A → B)(h : A → C)
  (q : (a : A) -> g (f a) ≡ h a) ->
  (as : Vec A n) → map g (map f as) ≡ map h       as
map-compose' g f h q []       = refl
map-compose' g f h q (a ∷ as) = cong2 _∷_ (q a) (map-compose' g f h q as) -- cong (_ ∷_) (map-compose' g f as)

open import Relation.Binary.PropositionalEquality
  renaming (_≡_ to _≡′_; cong to cong′)
  using (refl; module ≡-Reasoning)

map-compose'' : ∀ {A B C : Set} {n} (g : B → C) (f : A → B)(h : A → C)
  (q : (a : A) -> g (f a) ≡′ h a) ->
  (as : Vec A n) → map g (map f as) ≡′ map h       as
map-compose'' g f h q []       = refl
map-compose'' g f h q (a ∷ as) = let open ≡-Reasoning in
  begin
    map g (map f (a ∷ as))
  ≡⟨⟩
    g (f a) ∷ map g (map f as)
  ≡⟨ cong′ (_∷ _) (q a) ⟩
    h a ∷ map g (map f as)
  ≡⟨ cong′ (_ ∷_) (map-compose'' g f h q as) ⟩
    h a ∷ map h as
  ≡⟨⟩
    map h (a ∷ as)
  ∎


---------------------------------------------------------
-- Annoying type errors

open import Data.Vec.Base using (_++_)


-- associativity of _++_

-- vecAppendAssoc : ...




---------------------------------------------------------
-- The equational reasoning kit

-- PROVE symmetry of _≡_
-- PROVE transitivity of _≡_


{-
-- PROVE transitivity using ≡-Reasoning
-}

-- PROVE substitution / Leibniz' Law / the indiscernibility of identicals
subst : {A : Set} {x y : A} →
  -- x equals y
  x ≡ y →
  -- meaning any property of x is also a property of y
  (P : A → Set) → P x → P y
subst refl P px = px

-- Use subst to prove symmetry, transitivity, cong of _≡_

-- DEFINE cast, the function transporting vectors
-- along identity proofs
