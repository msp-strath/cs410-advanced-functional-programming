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
data Expr : Set where
  aNat  : ℕ → Expr
  aBool : Bool → Expr
  add   : (m n : Expr) → Expr
  ifte  : (b : Expr) (l r : Expr) → Expr

aZero : Expr
aZero = aNat 0

aTrue : Expr
aTrue = aBool true

pattern _+E_ a b = add a b
pattern ifE_then_else_ b t e = ifte b t e

infixl 4 _+E_
infix 0 ifE_then_else_

-- Examples (name them so we can reuse them later on)

aGoodSum : Expr
aGoodSum = aZero +E (ifE aTrue then aNat 2 else aNat 1)

aBadSum : Expr
aBadSum = aZero +E aTrue

aBadIF : Expr
aBadIF = ifE aZero then aZero else aZero

---------------------------------------------------------------------------
-- Evaluation
---------------------------------------------------------------------------

-- A value is either a number or a Boolean.
-- DEFINE Val

data Val : Set where
  aNat  : ℕ → Val
  aBool : Bool → Val

-- Now we can Maybe produce a value from an expression; we return
-- `nothing` if things don't make sense.

getNat : Val → Maybe ℕ
getNat (aNat n) = just n
getNat _ = nothing

getBool : Val → Maybe Bool
getBool (aBool b) = just b
getBool _ = nothing

_+V_ : Maybe Val → Maybe Val → Maybe Val
mv +V mw = do
  v ← mv
  w ← mw
  m ← getNat v
  n ← getNat w
  just (aNat (m + n))

ifV_then_else_
  : Maybe Val
  → {- lazy -} Maybe Val
  → {- lazy -} Maybe Val
  → Maybe Val
ifV mv then l else r = do
  v ← mv
  b ← getBool v
  if b then l else r

-- DEFINE eval
eval : Expr → Maybe Val
eval (aNat n) = just (aNat n)
eval (aBool b) = just (aBool b)
eval (     m +E      n) =
      eval m +V eval n
eval (ifE      b then      l else      r) =
      ifV eval b then eval l else eval r

-- REFACTOR eval

-- DISCUSS denotational semantics


-- examples
_ : eval aZero ≡ just (aNat 0)
_ = refl

_ : eval aGoodSum ≡ just (aNat 2)
_ = refl

_ : eval aBadSum ≡ nothing
_ = refl

_ : eval aBadIF ≡ nothing
_ = refl

_ : eval (ifE aTrue then aZero else aBadSum) ≡ just (aNat 0)
_ = refl

-- tests

---------------------------------------------------------------------------
-- Typed expressions
---------------------------------------------------------------------------

-- We can try to rule out non-sensical expressions using types in our
-- toy language.

-- DEFINE Ty

data Ty : Set where
  `Nat : Ty
  `Bool : Ty

-- We now annotate each expression with their expected type. Note that
-- if-then-else works for arbitrary types of the branches, as long as
-- they coincide.

-- DEFINE TExpr

data TExpr : Ty → Set where
  aNat  : ℕ → TExpr `Nat
  aBool : Bool → TExpr `Bool
  add   : (m n : TExpr `Nat) → TExpr `Nat
  ifte  : ∀ {T} → (b : TExpr `Bool) (l r : TExpr T) → TExpr T

-- EXAMPLES

aGoodSumBis : TExpr `Nat
aGoodSumBis = add (aNat zero) (aNat 1)

{-
aBadSumBis : TExpr `Nat
aBadSumBis = add (aNat zero) (aBool true)
-}

---------------------------------------------------------------------------
-- Evaluation
---------------------------------------------------------------------------

-- We can now compute the type of the value of a given typed
-- expression.

-- DEFINE TVal
TVal : Ty → Set
TVal `Nat  = ℕ
TVal `Bool = Bool


-- DEFINE teval : forall {T} -> TExpr T -> TVal T
teval : forall {T} -> TExpr T -> TVal T
teval (aNat m) = m
teval (aBool b) = b
teval (add m n) = teval m + teval n
teval (ifte b l r) = if teval b then teval l else teval r

_ : teval aGoodSumBis ≡ 1
_ = refl


--------------------------------------------------------------------------
-- Relating typed and untyped expressions
---------------------------------------------------------------------------

-- It is easy to forget the type of a typed expression.

-- DEFINE ∣_∣ : ∀ {t} → TExpr t -> Expr
-- This is not a |, this is a \|
∣_∣ : ∀ {t} → TExpr t -> Expr
∣ aNat n     ∣ = aNat n
∣ aBool b    ∣ = aBool b
∣ add m n    ∣ = add ∣ m ∣ ∣ n ∣
∣ ifte b l r ∣ = ifte (∣ b ∣) (∣ l ∣) (∣ r ∣)

-- STATE PROVE erasure correctness wrt evaluation

∣_∣v : ∀ {t} → TVal t → Val
∣_∣v {`Nat}  v = aNat v
∣_∣v {`Bool} v = aBool v


if-cong : ∀ {A B : Set} →
  (f : A → B) → ∀ b l r →
  (if b then f l else f r) ≡ f (if b then l else r)
if-cong f false l r = refl
if-cong f true l r = refl

∣∣-correct : ∀ {t} (e : TExpr t) →
             eval ∣ e ∣ ≡ just ∣ teval e ∣v
∣∣-correct (aNat n)     = refl
∣∣-correct (aBool b)    = refl
∣∣-correct (add m n)
{- long form "rewrite"
  with eval ∣ m ∣ | ∣∣-correct m
... | w | refl = {!!}
-}
  rewrite ∣∣-correct m
  rewrite ∣∣-correct n
  = refl
∣∣-correct (ifte b l r)
{- cunning solution
  with eval ∣ b ∣ | teval b | ∣∣-correct b
... | u | false | refl = ∣∣-correct r
... | u | true | refl = ∣∣-correct l
-}
  rewrite ∣∣-correct b
  rewrite ∣∣-correct l
  rewrite ∣∣-correct r
{- brutally using with
  with (teval b)
... | false = refl
... | true = refl
-}
-- library-based solution
  = if-cong (λ v → just ∣ v ∣v) (teval b) (teval l) (teval r)








-- Conversely, we can record when a given untyped expression is
-- welltyped. (As we have seen, this is not always the case.)

-- DEFINE record Welltyped (e : Expr) : Set where

data ILike : Expr -> Set where
  iLikeTypes : (T : Ty)(e : TExpr T) -> ILike ∣ e ∣

tryLiking : (e : Expr) -> Maybe (ILike e)
tryLiking (aNat n) = just (iLikeTypes `Nat (aNat n))
tryLiking (aBool b) = just (iLikeTypes `Bool (aBool b))
tryLiking (n +E m)
  with tryLiking n | tryLiking m
... | just (iLikeTypes `Nat n') | just (iLikeTypes `Nat m')
      = just (iLikeTypes `Nat (add n' m'))
... | _ | _ = nothing
tryLiking (ifE b then l else r)
  with tryLiking b | tryLiking l | tryLiking r
... | just (iLikeTypes `Bool b') | just (iLikeTypes `Nat l') | just (iLikeTypes `Nat r') = just (iLikeTypes `Nat (ifte b' l' r'))
... | just (iLikeTypes `Bool b') | just (iLikeTypes `Bool l') | just (iLikeTypes `Bool r') = just (iLikeTypes `Bool (ifte b' l' r'))
... | _ | _ | _ = nothing

infer : Expr → Maybe Ty
infer e with tryLiking e
... | just (iLikeTypes ty _) = just ty
... | _ = nothing

-- STATE and PROVE type uniqueness


-- DEFINE infer

-- EXAMPLES


---------------------------------------------------------------------------
-- Optimising expressions
---------------------------------------------------------------------------
