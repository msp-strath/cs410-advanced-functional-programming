module Week1 where

{-------------------------
-- Administrative Details
-------------------------}

-- | The Team

-- Guillaume Allais
-- Conor McBride
-- Fredrik Nordvall Forsberg
-- Sean Watters

-- | The Events

-- * Lectures
-- Mondays   | 10am   to 11am   | TL565
-- Tuesdays  | 2pm    to 3pm    | TG227

-- * Labs
-- Announced tomorrow.
-- Special help-me-install-Agda lab today after this lecture in LT1201.

-- | Assessment

-- Coursework only.
-- 2 courseworks (40% and 60%)

-- | Lecture materials

-- Results of live programming on Github
-- Video recordings
-- Please tell us what you think in One-Minute Papers!

{-------------------------
-- Content starts here
-------------------------}

-- Lists

data List (X : Set) : Set where
  [] : List X
  _,-_ : X -> List X -> List X

append : {X : Set} -> List X -> List X -> List X
append [] ys = ys
append (x ,- xs) ys = x ,- append xs ys


-- zap

zap : {S T : Set} -> List (S -> T) -> List S -> List T
zap [] [] = []
zap [] (s ,- ss) = []
zap (f ,- fs) [] = []
zap (f ,- fs) (s ,- ss) = f s ,- zap fs ss

-- head and tail

tail : {X : Set} -> List X -> List X
tail [] = []
tail (x ,- xs) = xs

head : {X : Set} -> List X -> X
head [] = {!!}
head (x ,- xs) = x

-- ...

data List1 (X : Set) : Set where
  _,-_ : (x : X) (xs : List X) -> List1 X

variable
  X : Set
  xs : List X

head1 : List1 X -> X
head1 (x ,- xs) = x

zap1 : {S T : Set} -> List1 (S -> T) -> List1 S -> List1 T
zap1 (f ,- fs) (x ,- xs) = f x ,- zap fs xs


---- ListN

data Nat : Set where
  zero : Nat
  suc : Nat → Nat

_+N_ : Nat -> Nat -> Nat
zero +N m = m
suc n +N m = suc (n +N m)

_ : Nat
_ = suc (suc (suc zero))

variable
  m n p : Nat

data ListN (X : Set) : Nat -> Set where
  []   : ListN X zero
  _,-_ : (x : X) (xs : ListN X n) -> ListN X (suc n)

headN : ListN X (suc n) -> X
headN (x ,- xs) = x

zapN : {S T : Set} -> ListN (S -> T) n -> ListN S n -> ListN T n
zapN [] [] = []
zapN (f ,- fs) (s ,- ss) = (f s) ,- zapN fs ss

appendN : ListN X n -> ListN X m -> ListN X (n +N m)
appendN [] ys = ys
appendN (x ,- xs) ys = x ,- appendN xs ys

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

data Pair (A B : Set) : Set where
  _,_ : A → B → Pair A B

_ : Nat × List Nat
_ = zero , []

splitN : ListN X (m +N n) → ListN X m × ListN X n
splitN {m = zero}  xs = [] , xs
splitN {m = suc m} (x ,- xs)
  = let (pref , suff) = splitN {m = m} xs in
    (x ,- {!!}) , {!!}
