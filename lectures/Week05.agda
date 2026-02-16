open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Maybe.Base using (Maybe; just; nothing; _>>=_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

---------------------------------------------------------------------------
-- Courseworks
---------------------------------------------------------------------------

-- CW (1st bits): deadline this Thursday at 5pm



---------------------------------------------------------------------------
-- Hutton's Razor
---------------------------------------------------------------------------

-- We will introduce a small toy programming language with
-- its evaluator. And then show how to improve its definition
-- to root out nonsensical errors.

-- This is the "hello world" of dependently typed languages
-- and goes back to at least 1999

-- References

-- Bahr, Patrick, and Graham Hutton.
-- "Calculating correct compilers."
-- Journal of Functional Programming 25 (2015): e14.

-- Augustsson, Lennart, and Magnus Carlsson.
-- "An exercise in dependent types: A well-typed interpreter."
-- Workshop on Dependent Types in Programming, Gothenburg. 1999.


---------------------------------------------------------------------------
-- Expressions
---------------------------------------------------------------------------

-- Define Expr (using at least 2 base types)

{-
pattern _+E_ a b = add a b
pattern ifE_then_else_ b t e = ifte b t e

infixl 4 _+E_
infix 0 ifE_then_else_
-}

-- Examples (name them so we can reuse them later on)

---------------------------------------------------------------------------
-- Evaluation
---------------------------------------------------------------------------

-- A value is either a number or a Boolean.
-- DEFINE Val




-- Now we can Maybe produce a value from an expression; we return
-- `nothing` if things don't make sense.

-- DEFINE eval

-- REFACTOR eval

-- DISCUSS denotational semantics


-- examples

-- tests

---------------------------------------------------------------------------
-- Typed expressions
---------------------------------------------------------------------------

-- We can try to rule out non-sensical expressions using types in our
-- toy language.

-- DEFINE Ty

-- We now annotate each expression with their expected type. Note that
-- if-then-else works for arbitrary types of the branches, as long as
-- they coincide.

-- DEFINE TExpr

-- EXAMPLES


---------------------------------------------------------------------------
-- Evaluation
---------------------------------------------------------------------------

-- We can now compute the type of the value of a given typed
-- expression.

-- DEFINE TVal


-- DEFINE teval : forall {T} -> TExpr T -> TVal T



--------------------------------------------------------------------------
-- Relating typed and untyped expressions
---------------------------------------------------------------------------

-- It is easy to forget the type of a typed expression.

-- DEFINE ∣_∣ : ∀ {t} → TExpr t -> Expr


-- STATE PROVE erasure correctness



-- Conversely, we can record when a given untyped expression is
-- welltyped. (As we have seen, this is not always the case.)

-- DEFINE record Welltyped (e : Expr) : Set where


-- STATE and PROVE type uniqueness


-- DEFINE infer

-- EXAMPLES


---------------------------------------------------------------------------
-- Optimising expressions
---------------------------------------------------------------------------
