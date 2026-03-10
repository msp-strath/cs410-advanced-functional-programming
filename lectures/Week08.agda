module Week08 where

---------------------------------------------------------------------------
-- Monoids
---------------------------------------------------------------------------

-- Remember monoids? A monoid is a set, together with a binary
-- operation on it, which has a unit, and which satisfies the axiom of
-- associativity -- that is, "brackets are not needed".

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; module ≡-Reasoning)

-- DEFINE Monoid as a record

record Monoid (X : Set) : Set where
  field
    -- semigroup
    _<>_ : X → X → X
    <>-assoc : ∀ x y z → (x <> y) <> z ≡ x <> (y <> z)
    -- monoid
    neu : X
    neu-<> : ∀ {x} → neu <> x ≡ x
    <>-neu : ∀ {x} → x <> neu ≡ x

-- EXAMPLES: your favourite monoids

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Function.Base using (id; _∘′_)


module _ where

  open Monoid

  list : (X : Set) → Monoid (List X)
  list X ._<>_ = _++_
  list X .<>-assoc = ++-assoc
  list X .neu = []
  list X .neu-<> = refl
  list X .<>-neu = ++-identityʳ _

  endo : (X : Set) → Monoid (X → X)
  endo X ._<>_ = _∘′_
  endo X .<>-assoc = λ x y z → refl
  endo X .neu = id
  endo X .neu-<> = refl
  endo X .<>-neu = refl



---------------------------------------------------------------------------
-- Generic programs
-- Parametric vs. ad-hoc polymorphism


-- foldr as a monoid homomorphism
foldr0 : {X T : Set} -> (X -> T -> T) -> T -> List X -> T
foldr0 cons nil [] = nil
foldr0 cons nil (x ∷ xs) = cons x (foldr0 cons nil xs)

-- swapping the order of arguments
foldr1 : {X T : Set} -> (X -> T -> T) -> List X -> T -> T
foldr1 cons [] nil = nil
foldr1 cons (x ∷ xs) nil = cons x (foldr1 cons xs nil)

-- noticing that nil is just being threaded throughout
foldr2 : {X T : Set} -> (X -> T -> T) -> List X -> T -> T
foldr2 cons [] = id
foldr2 cons (x ∷ xs) = cons x ∘′ foldr2 cons xs


-- noticing that this is "just" turning a list of X into
-- a list of (endo T) and then squashing it using the fact
-- endo is a monoid.
-- Let's generalise!



---------------------------------------------------------------------------
-- Parametrised proofs
---------------------------------------------------------------------------


-- anonymous module
module _ {A : Set} (m : Monoid A) where

  open Monoid m

  -- DEFINE squish/crush/ whatever you want to call it
  foldMap : {X : Set} -> (X -> A) -> List X -> A
  foldMap f [] = neu
  foldMap f (x ∷ xs) = f x <> foldMap f xs


  -- PROVE it is a monoid homomorphism
  foldMap-[] : {X : Set} (f : X → A) → foldMap f [] ≡ neu
  foldMap-[] f = refl

  foldMap-++ : {X : Set} (f : X → A) →
    (xs ys : List X) →
    foldMap f (xs ++ ys) ≡ (foldMap f xs <> foldMap f ys)
  foldMap-++ f [] ys = sym neu-<>
  foldMap-++ f (x ∷ xs) ys = let open ≡-Reasoning in begin
    foldMap f ((x ∷ xs) ++ ys)
      ≡⟨⟩
    (f x <> foldMap f (xs ++ ys))
      ≡⟨ cong (f x <>_) (foldMap-++ f xs ys) ⟩
    (f x <> (foldMap f xs <> foldMap f ys))
      ≡⟨ <>-assoc (f x) (foldMap f xs) (foldMap f ys) ⟨
    ((f x <> foldMap f xs) <> foldMap f ys)
      ≡⟨⟩
    (foldMap f (x ∷ xs) <> foldMap f ys)
      ∎



-- going back to our prior observation: foldr3 is just
-- foldMap for endo
foldr3 : {X T : Set} -> (X -> (T -> T)) -> List X -> (T -> T)
foldr3 = foldMap (endo _)






-- DEFINE the acc-based version, prove it is equivalent




---------------------------------------------------------------------------
-- Homomorphisms
---------------------------------------------------------------------------

-- DEFINE Monoid Homomorphisms

-- EXAMPLE

-- PROVE they commute with squishing

---------------------------------------------------------------------------
-- Category
---------------------------------------------------------------------------

-- It's just a fancy monoid
-- DEFINE it

-- EXAMPLES
