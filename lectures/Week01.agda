module Week01 where

------------------------------------------------------------------------
-- Administrative Details

-- | The Team
-- Guillaume Allais
-- Conor Mc Bride
-- Fredrik Nordvall-Forsberg

-- | The Events
-- * Lectures
-- Mondays  | 10am   to 11am | TL565
-- Tuesdays | 2pm    to 3pm  | TG227

-- * Labs
-- Mondays  | 11am to 12noon | LT1201
--
-- Help-me-install-Agda lab today after this lecture in LT1201.

-- * Teams
-- https://teams.microsoft.com/l/team/19%3A8Gl1lZT6PtpIEz26mwSB2cCU9hk33ZBdSLAXnDTKxsI1%40thread.tacv2/conversations?groupId=61b05fe6-8db1-4426-81f2-a2da413c5be8&tenantId=631e0763-1533-47eb-a5cd-0457bee5944e


-- | Assessment

-- Coursework only: 1 continuous coursework with 3 deadlines
-- * Week 5 (first 20%)
-- * Week 8 (up to 40%)
-- * Week 12 / whatever does not interfere with projects (up to 100%)

-- Support available during the weekly labs


-- | Lecture materials

-- Results of live programming on Github (https://github.com/msp-strath/cs410-advanced-functional-programming/)
-- Video recordings
-- Please tell us what you think in One-Minute Papers!



------------------------------------------------------------------------
-- Content starts here
------------------------------------------------------------------------

open import Data.String.Base using (String)

------------------------------------------------------------------------
-- Lists, partiality

-- List, append

data List (X : Set) : Set where
  [>]  :               List X
  _:>_ : X → List X -> List X -- \r is → but ->

-- in Haskell:
-- data List x = Nil | Cons x (List x)

-- example (list of strings)

_ : List String
_ = "hello" :> [>]

-- zap (ugh)

zap : {S T : Set} -> List (S -> T) -> List S -> List T
zap [>] ss = [>]
zap (f :> fs) [>] = [>]
zap (f :> fs) (s :> ss) = f s :> zap fs ss

-- example where zap goes wrong

-- tail

variable S T : Set

tail : List S → List S
tail [>] = [>]
tail (_ :> xs) = xs


-- head (?!)

head : List S → S
head [>] = {!!}
head (x :> _) = x


variable A : Set
{-# NON_TERMINATING #-}
brexit : A
brexit = brexit

------------------------------------------------------------------------
-- List1, totality


-- List1
data List1 (X : Set) : Set where
  _:>_ : X → List X → List1 X

-- head1
head1 : List1 S → S
head1 (x :> _) = x

------------------------------------------------------------------------
-- OMP
-- Emacs key combinations:
-- https://agda.readthedocs.io/en/v2.8.0/tools/emacs-mode.html#notation-for-key-combinations

-- zap1, still unsatisfactory

zap1 : List1 (S → T) → List1 S → List1 T
zap1 (f :> fs) (s :> ss) = (f s) :> (zap fs ss)

------------------------------------------------------------------------
-- ListN, invariant-aware

-- Nat, _+_
data Nat : Set where
  zero : Nat
  succ : Nat → Nat

-- example

three : Nat
three = succ (succ (succ zero))

-- variables of type Nat

variable m n p : Nat

-- ListN

infixr 5 _:>_

-- data List  (X : Set) :       Set where
-- invariant: the Nat index is the length of the list
data    ListN (X : Set) : Nat → Set where
  [>]  :                          ListN X zero
  _:>_ : ∀ {n} → X → ListN X n -> ListN X (succ n)
     -- ∀ {n} is the same as {n : _} →

_ : ListN String three
_ = "hello" :> " " :> "world" :> [>]

-- headN

headN : forall {X n} -> ListN X (succ n) -> X
headN (x :> xs) = x

tailN : forall {X n} -> ListN X (succ n) -> ListN X n
tailN (x :> xs) = xs

-- zapN

zapN : forall {S T n} -> ListN (S -> T) n -> ListN S n -> ListN T n
zapN [>] [>] = [>]
zapN (f :> fs) (s :> ss) = f s :> zapN fs ss

infixr 5 _+_
_+_ : Nat → Nat → Nat
zero     + n = n
(succ m) + n = succ (m + n)

-- appendN
-- what's its type?
appendN : ListN S m → ListN S n → ListN S (m + n)
appendN [>]       ys = ys
appendN (x :> xs) ys = x :> appendN xs ys

-- another definition of addition
infixr 5 _+'_
_+'_ : Nat → Nat → Nat
m +' zero   = m
m +' succ n = succ (m +' n)

-- appendN' is not appendN
appendN' : ListN S m → ListN S n → ListN S (m +' n)
appendN' xs [>]       = xs
appendN' xs (y :> ys) = y :> (appendN' xs ys)

-- Pairs of things
record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

-- unAppending
unAppending : ListN S (m + n) → ListN S m × ListN S n
unAppending {m = m} = {!!}

-- record _×_ (+ similar-looking data Pair)


-- example


-- splitN, the unAppending
