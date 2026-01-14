------------------------------------------------------------------------
-- Coursework 2: Genetic algorithms (100 marks)
--
-- The goal of this coursework is to define a syntax for polynomials,
-- give its semantics in an arbitrary ring and prove some its properties.
-- We then use these polynomials as approximation of (Float → Float)
-- function, using a genetic algorithm to find a good fit through e.g.
-- crossovers, mutations, and selection.
--
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Submission
--
-- Remember that this is submitted by pushing the work to a *private*
-- repository on either github or the departmental gitlab. Ideally, reuse
-- the one you set up for the first coursework.
--
-- Deadline: Thursday 10 April at 5pm
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Life advice
--
-- 0. Workflow
--
-- If you find below some concepts or syntax we have not yet seen, don't
-- hesitate to skip the questions and complete other problems further
-- down the file.
-- You can come back to the questions you skipped once we have covered
-- the related material in the lectures.
--
-- 1. Difficulty
--
-- It is not the case that the hard marks are all at the end of the
-- file, and the easy marks are at the beginning. Consequently, it
-- might be strategic to skip ahead if you get stuck.
--
-- 2. Compositionality
--
-- It is also often the case that prior definitions are useful.
-- If you get stuck, do look back up to see whether something
-- is exactly what you are missing.
--
-- 3. Hints
--
-- We are being very explicit in the import lists of the modules
-- included at the top of this file. This should give you an idea
-- of the lemmas you will need to deploy.
------------------------------------------------------------------------


{-# OPTIONS --erasure --guardedness #-}

module 2-Genetic-completed where

-- We get the natural numbers but because we are going to have
-- different types of numbers, we don't import much explicitly.
-- If you want to use operations, you can prefix them e.g. 2 ℕ.+ 3

open import Data.Nat.Base as ℕ using (ℕ; zero; suc; z≤n; s≤s)
import Data.Nat.Properties as ℕ
import Data.Nat.Show as ℕ

-- We get the integers, similarly not importing very much.
-- Note however all the properties we're importing. These will
-- definitely be useful!
open import Data.Integer as ℤ using (ℤ; +_; -[1+_]; pred)
import Data.Integer.Properties as ℤₚ
  using ( +-identityˡ
        ; +-identityʳ
        ; +-assoc
        ; +-comm
        ; +-inverseʳ
        ; *-identityˡ
        ; *-assoc
        )
import Data.Integer.Show as ℤₛ


-- Some basic datatypes you should be familiar with
open import Data.Bool.Base using (Bool; true; false; T; if_then_else_; _∨_)
open import Data.Bool.Properties using (T?)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Char.Base as Char using (Char)
open import Data.String as String using (String)
open import Data.Maybe.Base as Maybe using (Maybe; just; nothing; fromMaybe; maybe′)
open import Data.Fin.Base as Fin using (Fin; zero; suc)

-- We import the very basics for vectors so as not to clash
-- with lists. Once again note the useful properties being
-- imported.
open import Data.Vec.Base as Vec using (Vec; []; _∷_; _++_)
open import Data.Vec.Properties
  using ( map-id
        ; map-∘
        ; map-cong
        ; ≡-dec
        ; lookup-map
        )

-- We import the very basics for lists so as not to clash with Vec.
-- Again, you can use qualified names for the other functions
open import Data.List.Base as List using (List; []; _∷_)


-- Some basic function combinators
open import Function.Base using (id; _$_; _∘_; case_of_; const)


-- We will talk both about raw rings (carrier and operations of
-- a ring but without any proofs that they respect the correct
-- equations) and rings (that come with proofs).
open import Algebra.Bundles.Raw using (RawRing)
open import Algebra.Bundles using (Ring)


-- We'll prove a few things using equalities too
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; refl; cong; cong₂; module ≡-Reasoning)

-- Finally my code uses this, your code does not necessarily needs to
open import Relation.Nullary using (does)



------------------------------------------------------------------------
-- MARKS
-- Syntax of polynomials
--    Operations                         13 MARKS
--    Properties                         12 MARKS
-- Semantics of polynomials
--    Definition                          4 MARKS
--    Properties                         21 MARKS
-- Approximations for Float functions
--    Graph and simple functions          5 MARKS
--    Population                          3 MARKS
--    Fitness                             6 MARKS
--    Evolution                          11 MARKS
-- Extension                             25 MARKS

------------------------------------------------------------------------
------------------------------------------------------------------------
-- Syntax of polynomials
------------------------------------------------------------------------
------------------------------------------------------------------------


-- We define a polynomial by its coefficients stored in
-- a vector. In essence, (Poly n) means "polynomial of
-- degree at most n".
Poly : ℕ → Set
Poly = Vec ℤ

-- We're going to use a lot of Polys so let's throw m & n as variables
variable
  m n : ℕ

------------------------------------------------------------------------
-- Operations: manipulating polynomials
------------------------------------------------------------------------

-- (2 MARKS)
-- Prove that polynomials enjoy decidable equality
-- Hint: you may be able to reuse library code
_≟_ : DecidableEquality (Poly n)
_≟_ = ≡-dec ℤ._≟_

open import Data.Sign using (Sign)
import Data.Sign.Properties as Sign

record Mono : Set where
  constructor _[_x^_]
  field
    sign        : Sign
    coeff       : ℕ
    {{coeff≢0}} : ℕ.NonZero coeff
    expon       : ℕ

module ShowSign where

  show : Sign → String
  show Sign.+ = "+"
  show Sign.- = "-"

showMono : Bool → Mono → String → String
showMono b (sign [ coeff x^ expon ]) var
  = String.concat
  $ List.catMaybes
  $ Maybe.when (does (sign Sign.≟ Sign.-) ∨ b) (ShowSign.show sign)
  ∷ (case coeff of λ where
      1 → Maybe.when (does (expon ℕ.≟ 0)) (ℕ.show coeff)
      _ → just (ℕ.show coeff))
  ∷ (case expon of λ where
      0 → nothing
      1 → just var
      _ → just (var String.++ "^" String.++ ℕ.show expon))
  ∷ []

open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_)

fromPoly : Poly n → Maybe (List⁺ Mono)
fromPoly = go 0 where

  go : ℕ → Poly n → Maybe (List⁺ Mono)
  go idx [] = nothing
  go idx (a ∷ p) with ℤ.signAbs a
  ... | s ℤ.◂ zero  = go (suc idx) p
  ... | s ℤ.◂ suc n = just (s [ suc n x^ idx ] ∷ maybe′ List⁺.toList [] (go (suc idx) p))

renderMonos : Maybe (List⁺ Mono) → String → String
renderMonos nothing var = "0"
renderMonos (just (m ∷ ms)) var
  = String.concat (showMono false m var ∷ List.map (λ m → showMono true m var) ms)

-- (5 MARKS)
-- Write a function displaying a polynomial
-- High marks for beautiful functions making sure we don't print
-- e.g.        3 * x ^ 0 + 0 * x ^ 1 + - 1 * x ^ 2
-- instead of  3 - x ^ 2
render : Poly n → String → String
render xs = renderMonos (fromPoly xs)

-- (1 MARK)
-- Define the constantly zero polynomial
zeros : Poly n
zeros = Vec.replicate _ (+ 0)

-- (1 MARK)
-- A monomial is a polynomial with a single non-zero coefficient.
-- (monomial a k) should give us the polynomial (x ↦ a * x ^ k)
monomial : ℤ → Fin n → Poly n
monomial a k = Vec.updateAt zeros k (const a)

-- (1 MARK)
-- Scale a polynomial by a given factor
scale : ℤ → Poly n → Poly n
scale k = Vec.map (k ℤ.*_)

-- (1 MARK)
-- Add two polynomials together
add : Poly n → Poly n → Poly n
add = Vec.zipWith ℤ._+_

-- (1 MARK)
-- Compute the negation of a polynomial
-- e.g. 2*x^2 + 4*x^10 should map to
-- -2*x^2 + -4*x^10
negate : Poly n → Poly n
negate = Vec.map (ℤ.-_)

-- (1 MARK)
-- Prove that if we have a polynomial of degree at most m,
-- and m is less than n, then we can also see it as
-- a polynomial with degree at most n.
embed : m ℕ.≤ n → Poly m → Poly n
embed z≤n p = zeros
embed (s≤s le) (a ∷ p) = a ∷ embed le p


------------------------------------------------------------------------
-- Properties: these  definitions are well behaved
------------------------------------------------------------------------

-- Poly's structure
-- (Poly n, zeros, add, negate) is an abelian group

-- (1 MARK)
-- Prove that zeros is neutral on the left of add
add-identityˡ : (p : Poly n) → add zeros p ≡ p
add-identityˡ [] = refl
add-identityˡ (a ∷ p) =
  cong₂ _∷_ (ℤₚ.+-identityˡ a) (add-identityˡ p)

-- (1 MARK)
-- Prove that add is associative
add-assoc : (p q r : Poly n) → add (add p q) r ≡ add p (add q r)
add-assoc [] [] [] = refl
add-assoc (a ∷ p) (b ∷ q) (c ∷ r) =
  cong₂ _∷_ (ℤₚ.+-assoc a b c) (add-assoc p q r)

-- (1 MARK)
-- Prove that add is commutative
add-comm : (p q : Poly n) → add p q ≡ add q p
add-comm [] [] = refl
add-comm (a ∷ p) (b ∷ q) =
  cong₂ _∷_ (ℤₚ.+-comm a b) (add-comm p q)

-- (1 MARK)
-- Prove that negate is the inverse on the right of add
add-inverse : (p : Poly n) → add p (negate p) ≡ zeros
add-inverse [] = refl
add-inverse (a ∷ p) =
  cong₂ _∷_ (ℤₚ.+-inverseʳ a) (add-inverse p)

------------------------------------------------------------------------
-- Embed preserves Poly's structure

-- (1 MARK)
-- Prove that embedding zeros gives us zeros
zeros-embed : ∀ (le : m ℕ.≤ n) → zeros ≡ embed le zeros
zeros-embed z≤n = refl
zeros-embed (s≤s le) = cong (+ 0 ∷_) (zeros-embed le)

-- (1 MARK)
-- Prove that addition and embedding commute
add-embed : ∀ (le : m ℕ.≤ n) p q → add (embed le p) (embed le q) ≡ embed le (add p q)
add-embed z≤n p q = add-identityˡ zeros
add-embed (s≤s le) (a ∷ p) (b ∷ q) = cong (a ℤ.+ b ∷_) (add-embed le p q)

-- (2 MARK)
-- Prove that negation and embed commute
negate-embed : ∀ (le : m ℕ.≤ n) p → negate (embed le p) ≡ embed le (negate p)
negate-embed z≤n p = begin
  negate (embed z≤n p)     ≡⟨⟩
  negate zeros             ≡⟨ add-identityˡ (negate zeros) ⟨
  add zeros (negate zeros) ≡⟨ add-inverse zeros ⟩
  zeros                    ≡⟨⟩
  embed z≤n (negate p)     ∎ where open ≡-Reasoning
negate-embed (s≤s le) (a ∷ p) = cong (ℤ.- a ∷_) (negate-embed le p)



------------------------------------------------------------------------
-- scale is a left monoid action

-- HINT: some of the properties imported from Data.Vec.Properties at
-- the top of the file may be useful!

-- (2 MARKS)
-- scale 1 is the identity
scale-one : (p : Poly n) → scale (+ 1) p ≡ p
scale-one p = begin
  scale (+ 1) p        ≡⟨⟩
  Vec.map (+ 1 ℤ.*_) p ≡⟨ map-cong ℤₚ.*-identityˡ p ⟩
  Vec.map id p         ≡⟨ map-id p ⟩
  p                    ∎  where open ≡-Reasoning

-- (2 MARKS)
-- scale distributes over *
scale-* : (k l : ℤ) (p : Poly n) → scale (k ℤ.* l) p ≡ scale k (scale l p)
scale-* k l p = begin
  scale (k ℤ.* l) p                     ≡⟨⟩
  Vec.map ((k ℤ.* l) ℤ.*_) p            ≡⟨ map-cong (ℤₚ.*-assoc k l) p ⟩
  Vec.map (λ x → k ℤ.* (l ℤ.* x)) p     ≡⟨ map-∘ (k ℤ.*_) (l ℤ.*_) p ⟩
  Vec.map (k ℤ.*_) (Vec.map (l ℤ.*_) p) ≡⟨⟩
  scale k (scale l p)                   ∎
 where open ≡-Reasoning






------------------------------------------------------------------------
------------------------------------------------------------------------
-- Semantics of polynomials
------------------------------------------------------------------------
------------------------------------------------------------------------


------------------------------------------------------------------------
-- Definition: meaning in a ring
------------------------------------------------------------------------

-- To give a meaning to a polynomial, we need:
-- 1. an interpretation of integer coefficients
-- 2. an interpretation of multiplication to form monomials
-- 3. a notion of addition to add monomials together

-- These are provided by a RawRing (a ring without any of its properties
-- enforced). We additionally require a `fromℤ` embedding for performance
-- reason. We will assume that it maps:
-- positive integers n  to    1 + ⋯ + 1  (where n 1s occur)
-- negative integers -n to - (1 + ⋯ + 1) (where n 1s occur)

-- You can jump to definition to see what a `RawRing`
-- gives you: a carrier type, an equivalence relation
-- for it and some operations over the carrier type.

module PolyMeaning {c e} (R : RawRing c e) (fromℤ : ℤ → RawRing.Carrier R) where

  open RawRing R

  -- (1 MARK)
  -- Define x ^ k by iterated multiplication
  infixl 9 _^_
  _^_ : Carrier → ℕ → Carrier
  x ^ zero = 1#
  x ^ suc n = x * x ^ n

  -- We give a meaning to a polynomial as a function on the
  -- carrier type of the ring. Concretely, `eval` takes a
  -- polynomial `p` and a value in the carrier `x` and
  -- returns the computation `p(x)`.

  -- When defining `eval`, we will need to remember how
  -- far down the vector of coefficients we currently are
  -- to know which power of `x` we need to compute.
  -- And so, we first define an auxiliary definition
  -- `evalIdx` taking an extra argument remembering that position.

  -- (1 MARK)
  -- Define monomial, the function taking a coefficient and
  -- an exponent and returning the function computing the value
  -- of the associated monomial
  mono : ℤ → Carrier → ℕ → Carrier
  mono a x k = fromℤ a * x ^ k

  -- (1 MARK)
  -- Implement evalIdx so that e.g.
  -- evalIdx 2 (10 ∷ 43 ∷ []) x computes the polynomial
  -- 10 * x ^ 2 + 43 * x ^ 3
  evalIdx : ℕ → Poly n → Carrier → Carrier
  evalIdx k []       x = 0#
  evalIdx k (a ∷ as) x = mono a x k + evalIdx (suc k) as x

  -- eval is derived from evalIdx
  eval : Poly n → Carrier → Carrier
  eval = evalIdx 0

  -- Horner's method (https://en.wikipedia.org/wiki/Horner%27s_method)
  -- [Note that Horner's method abides by Stigler's law of eponymy
  -- (https://en.wikipedia.org/wiki/Stigler%27s_law_of_eponymy), as
  -- it was actually invented long before Horner used it]
  -- is an alternative evaluation strategy avoiding the explicit
  -- computation of successive powers of `x`.

  -- Define `horner p x`.
  -- e.g. horner for 2*x^2 + x will look like
  -- 0 + (1 + (2 + 0 * x) * x) * x
  -- (1 MARK)
  horner : Poly n → Carrier → Carrier
  horner []       x = 0#
  horner (a ∷ as) x = fromℤ a + horner as x * x


------------------------------------------------------------------------
-- Properties: correctness of the operations
-------------------------------------------------------------------------

-- One way to prove that the syntatic transformations we perform on
-- polynomials using add, negate, etc. make sense is to prove that
-- the intended meaning of these transformations is preserved by
-- a meaning function like horner.
-- For instance, proving that (horner (add p q) x) gives the same
-- result as (horner p x + horner q x) is a way to demonstrate that
-- add is correctly implementing addition of polynomials.

open import 2-Genetic-Lib

-- We import the library defined in an auxiliary files to get
-- access to a fromℤ′ function that maps
-- positive integers n  to    1 + ⋯ + 1  (where n 1s occur)
-- negative integers -n to - (1 + ⋯ + 1) (where n 1s occur)
--
-- By adding the assumption (fromℤ-correct) as a module parameter
-- below we ensure that our more efficient fromℤ behaves the same
-- as the naïve fromℤ′ definition (defined in the Injection module).
-- fromℤ′ will be convenient to use in proofs because:
-- 1. it computes and
-- 2. it comes with properties proven in the InjectionCorrect module


module PolyCorrect {c e} (R : Ring c e)
  (fromℤ : ℤ → Ring.Carrier R)
  (open Ring R renaming (refl to ≈-refl))
  (open Injection rawRing)
  (open PolyMeaning rawRing fromℤ)
  (fromℤ-correct : ∀ i → fromℤ i ≈ fromℤ′ i)
  where

  -- A useful lemma
  open import Algebra.Consequences.Setoid setoid
    using ( comm∧assoc⇒middleFour )

  -- An equational reasoning kit for the notion of equivalence _≈_
  -- that comes with the Ring R.
  open import Relation.Binary.Reasoning.Setoid setoid
  -- This enables you to write proofs of `e₁ ≈ e₄` that look something like:
  -- begin
  --  e₁ ≡⟨⟩        -- e₁ related to e₂ because equal by computation alone
  --  e₂ ≈⟨ prf₁ ⟩  -- e₂ related to e₃ by proof step prf₁
  --  e₃ ≈⟨ prf₂ ⟨  -- e₃ related to e₄ by symmetric proof step prf₂ (note the flipped closing bracket)
  --  e₄ ∎


------------------------------------------------------------------------
-- Horner is a homomorphism of commutative monoid

  -- Prove that the meaning given by horner to Poly's zeros
  -- is the carrier's 0
  -- (3 MARKS)
  -- HINT: look at the types of:
  --     +-cong
  --     *-congʳ
  --     +-identityˡ
  --     zeroˡ
  --     fromℤ-correct
  zeros-homo : (n : ℕ) → ∀ x → horner (zeros {n}) x ≈ 0#
  zeros-homo zero x = ≈-refl
  zeros-homo (suc n) x = begin
    horner (zeros {suc n}) x
      ≡⟨⟩
    fromℤ (+ 0) + horner (zeros {n}) x * x
      ≈⟨ +-cong (fromℤ-correct (+ 0)) (*-congʳ (zeros-homo n x)) ⟩
    0# + 0# * x
      ≈⟨ +-identityˡ (0# * x) ⟩
    0# * x
      ≈⟨ zeroˡ x ⟩
    0# ∎


  -- (3 MARKS)
  -- HINT: look at the type of
  -- +-congˡ
  -- *-congʳ
  embed-homo : ∀ (le : m ℕ.≤ n) p x → horner (embed le p) x ≈ horner p x
  embed-homo {n = n} z≤n [] x = zeros-homo n x
  embed-homo (s≤s le) (a ∷ p) x = begin
    horner (embed (s≤s le) (a ∷ p)) x
      ≡⟨⟩
    (fromℤ a + horner (embed le p) x * x)
      ≈⟨ +-congˡ (*-congʳ (embed-homo le p x)) ⟩
    (fromℤ a + horner p x * x)
      ≡⟨⟩
    horner (a ∷ p) x ∎

  -- We're generous so we're giving you some facts about expressions
  -- in a ring that may very well be useful in the following proofs

  open import Algebra.Properties.Ring R
    using ( -0#≈0#
          ; -‿+-comm
          ; -‿distribˡ-*
          ; -‿distribʳ-*
          )

  open InjectionCorrect R
    using ( fromℤ′‿-‿homo
          ; fromℤ′-+-homo
          )

  -- (4 MARKS)
  -- Prove that the meaning associated by horner
  -- to the negation of a polynomial
  -- is the negation of the meaning of the polynomial
  -- HINT: Look at the types of the provided lemmas & -‿cong
  negate-homo : (p : Poly n) → ∀ x → horner (negate p) x ≈ - (horner p x)
  negate-homo [] x = sym -0#≈0#
  negate-homo (a ∷ p) x = begin
    horner (negate (a ∷ p)) x
      ≡⟨⟩
    (fromℤ (ℤ.- a) + horner (negate p) x * x)
      ≈⟨ +-cong (fromℤ-correct (ℤ.- a)) (*-congʳ (negate-homo p x)) ⟩
    fromℤ′ (ℤ.- a) + (- horner p x) * x
      ≈⟨ +-cong (fromℤ′‿-‿homo a) (sym (-‿distribˡ-* (horner p x) x)) ⟩
    (- fromℤ′ a + (- (horner p x * x)))
      ≈⟨ -‿+-comm (fromℤ′ a) (horner p x * x) ⟩
    (- (fromℤ′ a + horner p x * x))
      ≈⟨ -‿cong (+-congʳ (fromℤ-correct a)) ⟨
    (- (fromℤ a + horner p x * x))
      ≡⟨⟩
    - horner (a ∷ p) x ∎

  -- (6 MARKS)
  -- Prove that the meaning associated by horner
  -- to the sum of two polynomial
  -- is the sum of the meanings of each polynomial
  -- HINT: look at the types of
  --     distribʳ
  --     comm∧assoc⇒middleFour
  add-homo : (p q : Poly n) → ∀ x → horner (add p q) x ≈ horner p x + horner q x
  add-homo []       []       x = sym (+-identityʳ 0#)
  add-homo (a ∷ as) (b ∷ bs) x = begin
    horner (add (a ∷ as) (b ∷ bs)) x
      ≡⟨⟩
    fromℤ (a ℤ.+ b) + horner (add as bs) x * x
      ≈⟨ +-congˡ (*-congʳ (add-homo as bs x)) ⟩
    fromℤ (a ℤ.+ b) + (horner as x + horner bs x) * x
      ≈⟨ +-congˡ (distribʳ x (horner as x) (horner bs x)) ⟩
    fromℤ (a ℤ.+ b) + (horner as x * x + horner bs x * x)
      ≈⟨ +-congʳ (fromℤ-correct (a ℤ.+ b)) ⟩
    fromℤ′ (a ℤ.+ b) + (horner as x * x + horner bs x * x)
      ≈⟨ +-congʳ (fromℤ′-+-homo a b) ⟩
    (fromℤ′ a + fromℤ′ b) + (horner as x * x + horner bs x * x)
      ≈⟨ comm∧assoc⇒middleFour +-cong +-comm +-assoc
           (fromℤ′ a) (fromℤ′ b) (horner as x * x) (horner bs x * x) ⟩
    (fromℤ′ a + horner as x * x) + (fromℤ′ b + horner bs x * x)
      ≈⟨ +-cong (+-congʳ (sym (fromℤ-correct a))) (+-congʳ (sym (fromℤ-correct b))) ⟩
    (fromℤ a + horner as x * x) + (fromℤ b + horner bs x * x)
      ≡⟨⟩
    horner (a ∷ as) x + horner (b ∷ bs) x
      ∎

  -- We want to prover not-Horner's method correct i.e.
  -- that giving a meaning to the polynomial via either
  -- `eval` or `horner` gives the same value.

  -- But given that `eval` is defined in terms of `evalIdx`, we are
  -- going to need to prove a more general theorem first. Given that
  -- `evalIdx k` evaluates a polynomial "after having seen k coefficients
  -- already", it is equivalent to evaluating the polynomial as is
  -- & multiplying the result by `x ^ k`.

  -- (3 MARKS)
  -- Prove evalIdx-horner
  -- HINT:
  -- 1. how would you prove it on paper?
  -- 2. using equational reasoning will make the proof a lot cleaner
  -- 3. the proof is relatively short (mine has 3 steps requiring a
  -- justification & 3 purely cosmetic steps using the _≡⟨⟩_ combinator).
  -- Look at the type of
  -- *-assoc
  -- distribʳ
  evalIdx-horner : ∀ {n} (p : Poly n) x k → evalIdx k p x ≈ horner p x * x ^ k
  evalIdx-horner []       x k = sym (zeroˡ (x ^ k))
  evalIdx-horner (a ∷ as) x k = begin
    evalIdx k (a ∷ as) x
      ≡⟨⟩
    fromℤ a * x ^ k + evalIdx (suc k) as x
      ≈⟨ +-congˡ (evalIdx-horner as x (suc k)) ⟩
    fromℤ a * x ^ k + horner as x * x ^ suc k
      ≡⟨⟩
    fromℤ a * x ^ k + horner as x * (x * x ^ k)
      ≈⟨ +-congˡ (sym (*-assoc (horner as x) x (x ^ k))) ⟩
    fromℤ a * x ^ k + (horner as x * x) * x ^ k
      ≈⟨ sym (distribʳ (x ^ k) (fromℤ a) (horner as x * x)) ⟩
    (fromℤ a + horner as x * x) * x ^ k
      ≡⟨⟩
    horner (a ∷ as) x * x ^ k
      ∎

  -- (2 MARKS)
  -- From `evalIdx-horner` you should now be able to prove
  -- `eval-horner` fairly straightforwardly by equational
  -- reasoning.
  -- HINT: look at the type of *-identityʳ
  eval-horner : ∀ {n} (p : Poly n) x → eval p x ≈ horner p x
  eval-horner p x = begin
    eval p x            ≡⟨⟩
    evalIdx 0 p x       ≈⟨ evalIdx-horner p x 0 ⟩
    horner p x * x ^ 0  ≡⟨⟩
    horner p x * 1#     ≈⟨ *-identityʳ (horner p x) ⟩
    horner p x ∎




------------------------------------------------------------------------
------------------------------------------------------------------------
-- Floating point functions
------------------------------------------------------------------------
------------------------------------------------------------------------

-- Here we give you a lot of code to graph a function over an interval
-- There's still a couple of marks to grab.

open import Data.Float as F using (Float)

------------------------------------------------------------------------
-- Graph: Functions over a given interval
------------------------------------------------------------------------

module Graph (A : Set) where

  -- tail recursive version of _+_; convenient for the following functions
  _+ᵗ_ : (m n : ℕ) → ℕ
  zero +ᵗ n = n
  suc m +ᵗ n = m +ᵗ suc n

  -- Range between [lb,ub] with n slices
  -- Note that we assume that lb < ub
  range : (lb ub : Float) (n : ℕ) → Vec Float (suc (n +ᵗ 1))
  range lb ub n = lb ∷ steps n (ub ∷ []) where

    dist : Float
    dist = ub F.- lb

    steps : ∀ {m} (s : ℕ) → Vec Float m → Vec Float (s +ᵗ m)
    steps zero      acc = acc
    steps k@(suc s) acc = steps s (lb F.+ dist F.* (F.fromℕ k F.÷ F.fromℕ (2 ℕ.+ n)) ∷ acc)


  -- The graph of a function f on [lb, ub] with s slices
  -- is given by values together with the proof they correspond to f on that range
  record Graph (lb ub : Float) (s : ℕ) (f : Float → A) : Set where
    constructor mkGraph
    field outputs : Vec A (suc (s +ᵗ 1))
          @0 proof : ∀ k → Vec.lookup outputs k ≡ f (Vec.lookup (range lb ub s) k)
  open Graph public

  -- (2 MARKS)
  -- Prove that any function can be graphed.
  graph : ∀ lb ub s f → Graph lb ub s f
  graph lb ub s f = mkGraph
    (Vec.map f (range lb ub s))
    (λ k → lookup-map k f (range lb ub s))


------------------------------------------------------------------------
-- Simple functions
------------------------------------------------------------------------

-- (1 MARK)
-- Implement the square function mapping e.g. 3.0 to 9.0
square : Float → Float
square s = s F.* s


-- (1 MARK)
-- Implement sum the function adding up all the values in an input vector
sum : Vec Float n → Float
sum = Vec.foldl′ F._+_ 0.0

-- (1 MARK)
-- Implement absolute value, returning +v if v is positive, and -v otherwise
∣_∣ : Float → Float
∣ v ∣ =
  if F.isNaN v then v else
  if v F.≤ᵇ 0.0 then F.- v else v


------------------------------------------------------------------------
-- Free stuff: we give you a rendering function for graphs
------------------------------------------------------------------------

module FPoly where

--  open PolyMeaning rawRing F.fromℤ public
  open Graph Float public


  -- Find the (non NaN) maximum (if it exists)
  maximum : Vec Float n → Maybe Float
  maximum = Vec.foldl′ step nothing where

    compare : (v w : Maybe Float) → Maybe Float
    compare nothing w = w
    compare v nothing = v
    compare (just v) (just w) = just (if v F.≤ᵇ w then w else v)

    step : Maybe Float → Float → Maybe Float
    step acc v = compare acc (if F.isNaN v then nothing else just v)


  -- Find the (non NaN) maximum (if they exist)
  minmax : Vec Float m → Maybe (Float × Float)
  minmax = Vec.foldl′ step nothing where

    compare : (v w : Maybe (Float × Float)) → Maybe (Float × Float)
    compare nothing w = w
    compare v nothing = v
    compare (just (minv , maxv)) (just (minw , maxw)) =
      just ( (if minv F.≤ᵇ minw then minv else minw)
           , (if maxv F.≤ᵇ maxw then maxw else maxv)
           )

    step : Maybe (Float × Float) → Float → Maybe (Float × Float)
    step acc v = compare acc (if F.isNaN v then nothing else just (v , v))

  -- Compute a nat over-approximation of the distance between two floats
  -- Assuming these inputs are non-NaN
  ⌈_─_⌉ : Float → Float → Maybe ℕ
  ⌈ w ─ v ⌉ = case F.⌈ ∣ w F.- v ∣ ⌉ of λ where
    nothing → nothing
    (just (+ n)) → just n
    (just -[1+ n ]) → nothing -- this is impossible: we used absolute value!

  -- Compute a nat under-approximation of the distance between two floats
  ⌊_─_⌋ : Float → Float → Maybe ℕ
  ⌊ w ─ v ⌋ = case F.⌊ ∣ w F.- v ∣ ⌋ of λ where
    nothing → nothing
    (just (+ n)) → just n
    (just -[1+ n ]) → nothing -- this is impossible: we used absolute value!

  -- This is a disgusting piece of code drawing a graph with two axes,
  -- and attempting to display a function.
  show : ∀ {lb ub s f} → Graph lb ub s f → String
  show {lb} {ub} {s} gph with minmax (outputs gph)
  ... | nothing = "Error: no non-NaN value"
  ... | just (min , max)
    =  -- Build a big matrix of characters that are then displayed as a rectangle
      String.unlines
    $ let topline = ℤ.suc (fromMaybe (+ 0) F.⌈ max ⌉) in
      let botline = ℤ.pred (fromMaybe (+ 0) F.⌊ min ⌋) in
      Vec.toList
    $ go (2 ℕ.+ String.length (ℤₛ.show topline) ℕ.⊔ String.length (ℤₛ.show botline))
         (3 ℕ.+ fromMaybe 0 ⌈ max ─ min ⌉)
         topline
         (Vec.zip (range lb ub s) (outputs gph))

    where

    go : (pad n : ℕ) → ℤ → Vec (Float × Float) m → Vec String n
    go pad zero    line vs = []
    go pad (suc n) line vs
      = (String.padLeft ' ' pad (ℤₛ.show line)
          String.++ String.fromVec (' ' ∷ dash ∷ pipe ∷ Vec.map isHere vs ++ pipe ∷ []))
      ∷ go pad n (ℤ.pred line) vs where

      -- Being on y axis, show '|' if we're additionally on the x axis
      pipe : Char
      pipe = if does (line ℤ.≟ (+ 0)) then '-' else '|'

      -- If we're on the x axis then show '-' else show an empty cell ' '
      dash : Char
      dash = if does (line ℤ.≟ (+ 0)) then '-' else ' '

      -- Decide whether a function value is close enough to the current
      -- point on the graph that we need to draw it
      isHere : Float × Float → Char
      isHere (x , fx) with ⌊ fx ─ F.fromℤ line ⌋ | ⌊ 100.0 F.* x ─ 0.0 ⌋
      ... | just 0 | _ = '+'
      ... | _ | just 0 = pipe
      ... | _ | _ = dash


------------------------------------------------------------------------
------------------------------------------------------------------------
-- Genetic algorithms: fitness, crossovers, mutations
------------------------------------------------------------------------
------------------------------------------------------------------------

module DNA where

  open FPoly

  -- For now these are global constants
  lowerBound : Float
  upperBound : Float
  sliceNumber : ℕ
  geneNumber : ℕ

  lowerBound = -3.0
  upperBound = 3.0
  sliceNumber = 100
  geneNumber = 5


------------------------------------------------------------------------
-- Population
------------------------------------------------------------------------

  -- An approximation of a (Float → Float) function is given by a polynomial
  Approximation : Set
  Approximation = Poly geneNumber

  -- A population is a list of approximations
  Population : Set
  Population = List Approximation

  -- We build the raw ring with carrier type Float.
  -- Together with Polymeaning, this will give us horner as
  -- an interpretation of the approximations
  rawRing : RawRing _ _
  rawRing = record
    { _≈_ = _≡_
    ; _+_ = F._+_
    ; _*_ = F._*_
    ; -_ = F.-_
    ; 0# = 0.0
    ; 1# = 1.0
    }

  open PolyMeaning rawRing F.fromℤ public using (horner)

  -- Imports to work with the list monad
  import Data.List.Effectful as List
  open import Effect.Monad using (RawMonad)

  -- (3 MARKS)
  -- Manufacture a sensible initial population covering a lot of the
  -- search space (e.g. all the monomials for coefficients ranging
  -- from -10 to +10)
  -- HINT: it may be useful to work in the list monad
  population : Population
  population
    = let open RawMonad List.monad in
      do let expons = List.allFin geneNumber
         let coeffs = List.allFin 10
         let posmonos =
              do k ← expons
                 v ← coeffs
                 pure (monomial (+ suc (Fin.toℕ v)) k)
         let negmonos = List.map negate posmonos
         zeros ∷ posmonos List.++ negmonos

------------------------------------------------------------------------
-- Fitness
------------------------------------------------------------------------

  -- (3 MARKS)
  -- Compute the mean squared error of two functions over
  -- the [lowerBound, upperBound] interval using
  -- the number of slices specified by sliceNumber i.e.
  -- the sum of the squares of the difference between the
  -- two functions at each sampling point in the
  -- `range lowerBound upperBound sliceNumber` describing the interval.
  -- HINT: remember that `graph` exists.
  squareMean : (f, g : Float → Float) → Float
  squareMean f g
    = let gph = graph lowerBound upperBound sliceNumber (λ x → square (g x F.- f x)) in
      let clean = Vec.map (λ v → if F.isNaN v then 0.0 else v) (outputs gph) in
      sum clean

  -- (1 MARK)
  -- Define your fitness function. It takes an approximation and
  -- the function to approximate on the given interval and evaluates
  -- how good of a match they are by computing their mean squared error.
  fitness : Approximation → (Float → Float) → Float
  fitness p = squareMean (horner p)


  open import Relation.Binary using (IsDecTotalOrder; DecTotalOrder)

  -- We're cheating because there's no way we could build such
  -- a thing given we can't do proofs on Float.
  isDecTotalOrder : IsDecTotalOrder _≡_ (λ a b → T (a F.≤ᵇ b))
  isDecTotalOrder = record
    { isTotalOrder = trustMe
    ; _≟_ = F._≟_
    ; _≤?_ = λ a b → T? (a F.≤ᵇ b)
    } where postulate trustMe : _ -- oops!

  decTotalOrder : DecTotalOrder _ _ _
  decTotalOrder = record { isDecTotalOrder = isDecTotalOrder }

  -- we give you a sorting function
  open import Data.List.Sort.MergeSort using (sort)
  -- and (hint, hint) a way to compose an existing decidable
  -- total order with a function
  import Relation.Binary.Construct.On as On

  -- (2 MARK)
  -- For our simulation to run reasonably fast, we need the
  -- population not to exceed a given size; write a selection
  -- function using the fitness function to only keep the
  -- best candidates.
  -- 1. score each approximation
  -- 2. sort the list according to the scores
  -- 3. only keep the 101 best candidates
  -- 4. throw the scores away
  selection : (f : Float → Float) → Population → Population
  selection f
    = List.take 101
    ∘ List.map proj₁
    ∘ sort (On.decTotalOrder decTotalOrder proj₂)
    ∘ List.map (λ p → p , fitness p f)



------------------------------------------------------------------------
-- Evolution
------------------------------------------------------------------------

  open import IO
  open import System.Random

  module BoolIO where

    -- (1 MARK)
    -- Build a random function returning a boolean
    -- HINT: look at the type of Fin.randomIO
    randomIO : IO Bool
    randomIO = do
      k ← Fin.randomIO
      pure (Vec.lookup (true ∷ false ∷ []) k)


  {-# TERMINATING #-}
  loop : ∀ {A : Set} → List A → List A → List A → IO (A × List A)
  loop pop acc [] = loop pop [] pop
  loop pop acc (x ∷ xs) = do
    b ← BoolIO.randomIO
    if b then pure (x , List.reverse acc List.++ xs) else loop pop (x ∷ acc) xs

  pick : ∀ {A : Set} → ℕ → List A → IO (List A × List A)
  pick zero    pop = pure ([] , pop)
  pick (suc n) pop = do
    (x , xs)  ← loop pop [] pop
    (ys , zs) ← pick n xs
    pure (x ∷ ys , zs)

  mergeIO : Vec ℤ n → Vec ℤ n → IO (Vec ℤ n)
  mergeIO [] _ = pure []
  mergeIO (l ∷ ls) (r ∷ rs) = do
    b ← BoolIO.randomIO
    n ← ℕ.randomRIO 0 19 ℕ.z≤n
    ms ← mergeIO ls rs
    pure ((if InBounds.value n ℕ.≡ᵇ 0 then (l ℤ.+ r) else if b then l else r) ∷ ms)

  mergeIOs : Vec ℤ n → Vec ℤ n → IO (List (Vec ℤ n))
  mergeIOs par1 par2 = do
    n ← ℕ.randomRIO 1 10 ℕ.z<s
    kids ← Vec.randomIO (mergeIO par1 par2) (InBounds.value n)
    pure (Vec.toList kids)

  -- (5 MARKS)
  -- Define (at least one) crossover strategy combining various
  -- pairs of polynomials into new ones.
  -- https://en.wikipedia.org/wiki/Crossover_(evolutionary_algorithm)
  --
  -- Be creative in how you select pairs of parent
  -- approximations, the number and diversity of
  -- crossovers you generate
  -- Explain your reasoning!
  crossover : Population → IO Population
  crossover pop = do
    par1 , rest ← pick 40 pop
    par2 , rest ← pick 40 rest
    let mchld = List.zipWith mergeIOs par1 par2
    chld ← List.sequence mchld
    pure (List.concat chld)

  import Data.List.Effectful as List
  import Data.Vec.Effectful as Vec
  import IO.Effectful as IO

  wildMutation : ℤ → IO (Maybe ℤ)
  wildMutation z = do
    n ← ℕ.randomRIO 0 999 ℕ.z≤n
    if 0 ℕ.<ᵇ InBounds.value n then pure nothing else do
      z ← ℤ.randomRIO -[1+ 99 ] (+ 100) ℤ.-≤+
      pure (just $ InBounds.value z)

  smallMutation : ℤ → IO (Maybe ℤ)
  smallMutation (+ 0) = pure nothing
  smallMutation z = do
    n ← ℕ.randomRIO 0 99 ℕ.z≤n
    if 0 ℕ.<ᵇ InBounds.value n then pure nothing else do
      b ← BoolIO.randomIO
      pure (just (z ℤ.+ (if b then (+ 1) else -[1+ 0 ])))


  _orElse_ : ∀ {A : Set} → IO (Maybe A) → IO A → IO A
  cmp orElse dft = do
    mx ← cmp
    case mx of λ where
      nothing → dft
      (just x) → pure x


  -- (5 MARKS)
  -- Define a mutation function randomly changing some of
  -- the approximations present in the population.
  -- https://en.wikipedia.org/wiki/Mutation_(evolutionary_algorithm)

  -- Be creative! You can start simple and come back to it
  -- later if your executable does not explore enough of
  -- the search space.
  -- Explain your reasoning!

  mutation : Population → IO Population
  mutation
    = List.TraversableA.mapA IO.applicative
    $ Vec.TraversableA.mapA IO.applicative
    $ λ z → wildMutation z orElse (smallMutation z orElse pure z)


  -- From your definitions, we can build an evolution framework

  -- We evolve a population by
  -- 1. mutating some of its approximations,
  -- 2. performing crossovers on the result
  -- 3. combining the results of 1 & 2
  -- 4. performing a selection based on fitness on the result of 3
  evolve : (Float → Float) → Population → IO Population
  evolve f pop = do
    pop  ← mutation pop
    kids ← crossover pop
    let pop = kids List.++ pop
    pure $ selection f pop

  -- Call evolve a set number of times,
  -- logging every time we have found a new top candidate
  evolution : (iters : ℕ) → (Float → Float) →
              ℕ → Approximation → Population → IO Population
  evolution iters fit c candidate pop =
    case List.head pop of λ where
      nothing → pure pop -- should be impossible
      (just sel) → do
        unless (does (candidate ≟ sel)) $ do -- only log new candidates
          putStr ("Step n°" String.++ ℕ.show (iters ℕ.∸ c))
          putStrLn (" (current candidate: x ↦ " String.++ render sel "x" String.++ ")")
        eloop c sel pop

    where

      eloop : ℕ → Approximation → Population → IO Population
      eloop _ sel [] = pure [] -- should be impossible
      eloop 0 sel pop = pure pop -- done
      eloop (suc c) sel pop = do
        pop ← evolve fit pop
        evolution iters fit c sel pop



open DNA
open import IO



------------------------------------------------------------------------
------------------------------------------------------------------------
-- Main function
------------------------------------------------------------------------
------------------------------------------------------------------------

-- Let us import some more floating point functions

open import Data.Float.Base as F using
  ( Float
  ; sqrt
  ; e^_
  ; log
  ; sin
  ; cos
  ; tan
  ; asin
  ; acos
  ; atan
  ; atan2
  ; sinh
  ; cosh
  ; tanh
  ; asinh
  ; acosh
  ; atanh
  )

open FPoly using (show; graph)

-- You can run a bunch of genetic searches for approximations
-- Here are examples we like. Feel free to define your own

main : Main
main = run $ do
  -- for each of these functions
  List.forM′
      ( ("sin", λ x → 10.0 F.* sin x)
      ∷ ("cos", λ x → 10.0 F.* cos x)
      ∷ ("atan", λ x → 6.0 F.* atan x)
      ∷ ("x ↦ e^x", λ x → 2.0 F.* e^ x)
      ∷ ("x ↦ x * sin x"       , λ x → 6.0 F.* x F.* sin x)
      ∷ ("x ↦ x ÷ sin x"       , λ x → 2.0 F.* x F.÷ sin x)
      ∷ ("x ↦ x * x"           , λ x → 2.0 F.* x F.* x)
      ∷ ("x ↦ x * (1 + sin x)" , λ x → 6.0 F.* x F.* (1.0 F.+ sin x))
      ∷ ("x ↦ √ ∣ x ∣"         , λ x → 10.0 F.* sqrt ∣ x ∣)
      ∷ ("x ↦ ∣ x ∣"         , λ x → 5.0 F.* ∣ x ∣)
      ∷ [])
    $ λ (nm , f) → do
      -- show their name & graph
      putStrLn ""
      putStrLn (nm String.++ ":")
      putStrLn $ show $ graph lowerBound upperBound sliceNumber f
      -- get approximations for a number of generations
      let generations = 1_000
      pop ← evolution generations f generations zeros (selection f population)
      -- and print the result and its graph
      case List.head pop of λ where
        nothing → putStrLn "Couldn't find an approximation" -- should be impossible
        (just sel) → do
          putStrLn ""
          putStrLn ("Approximated by: x ↦ " String.++ render sel "x")
          putStrLn $ show $ graph lowerBound upperBound sliceNumber (horner sel)


------------------------------------------------------------------------
-- Extend the project (25 MARKS)
------------------------------------------------------------------------

-- You are free to implement whatever you want. Try to put an emphasis
-- on elegant type & code. Here are some ideas:

-- * A better renderer e.g.
--     multiple graphs with different colours
--     numbers on the x axis
--     dynamic resampling (so that you don't need to look at 50*cos instead of cos)?
--     using unicode Braille pattern characters for sub-character precision in rendering
--     gnuplot or output via a haskell lib
--
-- * A better DNA model e.g.
--     multiple strands for different intervals
--     dynamically discovering new interval splits
--
-- * A more developped theory of polynomials e.g.
--     closure under multiplication, composition, derivation
--     proven correct with respect to horner
--     used for new notions of crossovers?

-- You will be marked on how idiomatic your types and definitions are,
-- on the complexity of the extension, and on how well you made use of
-- Agda's features compared to e.g. Haskell.
