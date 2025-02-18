open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Maybe.Base using (Maybe; just; nothing; _>>=_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

---------------------------------------------------------------------------
-- Courseworks
---------------------------------------------------------------------------

-- CW1: deadline this Thursday at 5pm

-- CW2: released this afternoon
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
  nat  : ℕ → Expr
  bool : Bool → Expr
  add  : Expr → Expr → Expr
  ifte : (b : Expr) (t e : Expr) → Expr


pattern _+E_ a b = add a b
pattern ifE_then_else_ b t e = ifte b t e

infixl 4 _+E_
infix 0 ifE_then_else_

-- Examples (name them so we can reuse them later on)

aNat : Expr
aNat = nat 42

aBool : Expr
aBool = bool true

aGoodSum : Expr
aGoodSum = add aNat (nat 10)

aBadSum : Expr
aBadSum = add aNat aBool

anIFTE : Expr
anIFTE = ifE aBool then aNat else nat 0

---------------
-- Evaluation
---------------

-- A value is either a number or a Boolean.

data Val : Set where
  nat : ℕ -> Val
  bool : Bool -> Val

-- Now we can Maybe produce a value from an expression; we return
-- `nothing` if things don't make sense.

_+V_ : Val → Val → Maybe Val
nat n +V nat n' = just (nat (n + n'))
_ +V _ = nothing

ifV_then_else : Val → Maybe Val → Maybe Val → Maybe Val
ifV bool b then l else r = if b then l else r
ifV _ then l else r = nothing

eval : Expr → Maybe Val
eval (nat n)  = just (nat n)
eval (bool b) = just (bool b)
eval (e +E e') = do
  nat n ← eval e where _ → nothing
  nat n' ← eval e' where
    bool true → nothing
    bool false → nothing
  just (nat (n + n'))
{-
eval (e +E e') = do
  val ← eval e
  val' ← eval e'
  val +V val'
-}
eval (ifE e then e' else e'') = do
  val ← eval e
  ifV val then eval e' else (eval e'')

{-
with eval e | eval e'
... | just (nat n) | just (nat n') = just (nat (n + n'))
... | _ | _ = nothing
eval (ifE e then e' else e'') with eval e
... | just (bool true) = eval e'
... | just (bool false) = eval e''
... | _ = nothing
-}

-- examples

test = eval (ifE bool true then aGoodSum else aBadSum)

---------------------------------------------------------------------------
-- Typed expressions
---------------------------------------------------------------------------

-- We can try to rule out non-sensical expressions using types in our
-- toy language.

data Ty : Set where
  bool nat : Ty

-- We now annotate each expression with their expected type. Note that
-- if-then-else works for arbitrary types of the branches, as long as
-- they coincide.

data TExpr : Ty -> Set where
  nat : ℕ -> TExpr nat
  bool : Bool -> TExpr bool
  add : TExpr nat -> TExpr nat -> TExpr nat
  ifte : forall {T} -> TExpr bool -> TExpr T -> TExpr T -> TExpr T

aTGoodSum : TExpr nat
aTGoodSum = add (nat 42) (nat 10)

-- aTBadSum : TExpr nat
-- aTBadSum = add (nat 42) {!bool true!}

---------------
-- Evaluation
---------------

-- We can now compute the type of the value of a given typed
-- expression.

TVal : Ty → Set
TVal bool = Bool
TVal nat = ℕ


{-
data TVal : Ty → Set where
  nat : ℕ -> TVal nat
  bool : Bool -> TVal bool
-}

teval : forall {T} -> TExpr T -> TVal T
teval (nat n) = n
teval (bool b) = b
teval (add en em) = teval en + teval em
teval (ifte eb et ee) = if teval eb then teval et else teval ee



--------------------------------------------------------------------------
-- Relating typed and untyped expressions
---------------------------------------------------------------------------

-- It is easy to forget the type of a typed expression.

∣_∣ : ∀ {t} → TExpr t -> Expr
∣ nat n         ∣ = nat n
∣ bool b        ∣ = bool b
∣ add en em     ∣ = add ∣ en ∣ ∣ em ∣
∣ ifte eb et ee ∣ = ifte (∣ eb ∣) (∣ et ∣) (∣ ee ∣)


embed : ∀ {t} → TVal t → Val
embed {bool} v = bool v
embed {nat} v = nat v

∣∣-correct : ∀ {t} (e : TExpr t) → eval ∣ e ∣ ≡ just (embed (teval e))
∣∣-correct = {!!}


-- Conversely, we can record when a given untyped expression is
-- welltyped. (As we have seen, this is not always the case.)

record Welltyped (e : Expr) : Set where
  constructor mkWellTyped
  field
    aType : Ty
    aTerm : TExpr aType
    proof : ∣ aTerm ∣ ≡ e
open Welltyped
-- And we can infer the type of an expression

eqTy? : (s : Ty) → (t : Ty) → Maybe (s ≡ t)
eqTy? bool bool = just refl
eqTy? nat nat = just refl
eqTy? _ _ = nothing



infer : (e : Expr) -> Maybe (Welltyped e)
infer (nat n) = just (mkWellTyped nat (nat n) refl)
infer (bool b) = just (mkWellTyped bool (bool b) refl)
infer (en +E em) = do
  mkWellTyped ty₁ tm refl <- infer en
  refl ← eqTy? ty₁ nat
  mkWellTyped ty₂ tm' refl <- infer em
  refl ← eqTy? ty₂ nat
  just (mkWellTyped nat (add tm tm') refl)
infer (ifE eb then et else ee) = do
  mkWellTyped ty₀ tm refl <- infer eb
  refl ← eqTy? ty₀ bool
  mkWellTyped ty₁ tm₁ refl <- infer et
  mkWellTyped ty₂ tm₂ refl <- infer ee
  refl <- eqTy? ty₁ ty₂
  just (mkWellTyped ty₁ (ifte tm tm₁ tm₂) refl)

typingUnique : (e : Expr) → (p q : Welltyped e) → aType p ≡ aType q
typingUnique = {!!}

anIFTE' : Expr
anIFTE' = ifE aBool then aNat else bool true


foo = infer anIFTE'


---------------------------------------------------------------------------
-- Optimising expressions
---------------------------------------------------------------------------

-- Let's write a function which "computes away" `if true` and `if
-- false`. Using typed expressions, we can already record in the type
-- of this function that this optimisation is type-preserving.

reduce-if : ∀ {T} → TExpr T -> TExpr T
reduce-if e = {!!}



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
