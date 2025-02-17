open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

---------------------------------------------------------------------------
-- CW2
---------------------------------------------------------------------------

-- Released this afternoon
-- Demo?



---------------------------------------------------------------------------
-- Hutton's Razor
---------------------------------------------------------------------------

-- We will introduce a small toy programming language.

---------------------------------------------------------------------------
-- Expressions
---------------------------------------------------------------------------

-- An expression is either a natural number, a Boolean, a sum of two
-- expressions, or an if-then-else expression.

data Expr : Set where

-- infixl 4 _+E_
-- infix 0 ifE_then_else_

-- Examples (name them so we can reuse them later on)

---------------
-- Evaluation
---------------

-- A value is either a number or a Boolean.

data Val : Set where

-- Now we can Maybe produce a value from an expression; we return
-- `nothing` if things don't make sense.

-- eval : Expr → Val


-- examples


---------------------------------------------------------------------------
-- Typed expressions
---------------------------------------------------------------------------

-- We can try to rule out non-sensical expressions using types in our
-- toy language.

data Ty : Set where

-- We now annotate each expression with their expected type. Note that
-- if-then-else works for arbitrary types of the branches, as long as
-- they coincide.

data TExpr : Ty -> Set where

---------------
-- Evaluation
---------------

-- We can now compute the type of the value of a given typed
-- expression.

-- TVal; teval

--------------------------------------------------------------------------
-- Relating typed and untyped expressions
---------------------------------------------------------------------------

-- It is easy to forget the type of a typed expression.

-- ∣_∣  : ∀ {t} → TExpr t -> Expr



-- Conversely, we can record when a given untyped expression is
-- welltyped. (As we have seen, this is not always the case.)

record Welltyped (e : Expr) : Set where


-- And we can infer the type of an expression

-- infer : (e : Expr) -> Welltyped e




---------------------------------------------------------------------------
-- Optimising expressions
---------------------------------------------------------------------------

-- Let's write a function which "computes away" `if true` and `if
-- false`. Using typed expressions, we can already record in the type
-- of this function that this optimisation is type-preserving.

-- reduce-if : ∀ {T} → TExpr T -> TExpr T



-- We can also run our optimiser, of course

-- Examples



-- Now let's prove that our optimisation did not change the meaning of expressions.









-- Arguably our language is almost too simple, because if we think
-- about it, it should be the case that reduce-if optimises away *all*
-- if expressions (you wouldn't expect this as soon as you have
-- variables, for example). Let's prove this:












-- Constant folding: replace num n + num k with num (n + k)
-- cfold : ∀ {T} → TExpr T → TExpr T

{-
tex4 : TExpr Num
tex4 = ifE bit false then (ifE bit true then (num 1 +E num 2) else num 6) else (num 4 +E (num 12 +E num 9))

_ : cfold tex4 ≡ (ifE bit false then ifE bit true then num 3 else num 6 else num 25)
_ = refl

_ = reduce-if tex4 ≡ TExpr.num 25
_ = refl {x = TExpr.num 25}
-}


-- cfold-correct : ∀ {T} → (e : TExpr T) → teval (cfold e) ≡ teval e
