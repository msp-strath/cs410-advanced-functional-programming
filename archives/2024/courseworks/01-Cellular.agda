------------------------------------------------------------------------
-- Coursework 1: Cellular (100 marks, 40% of course total)
--
-- The goal of this coursework is to write a small one dimensional
-- cellular automaton that traces a rule (e.g. rule 90 [1]) on an
-- initial state.
--
-- For that we are going to introduce some fancy types making explicit
-- the notion of sliding window that arises naturally during the
-- implementation.
--
-- [1] https://en.wikipedia.org/wiki/Rule_90
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Submission
--
-- Remember that this is submitted by creating a *private* repository
-- on either github or the departmental gitlab and inviting me so that
-- I can mark your work.
--
-- Deadline: Thursday 15 February at 5pm
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Workflow
--
-- If you find below some concepts or syntax we have not yet seen, don't
-- hesitate to skip the questions and complete other problems further
-- down the file.
-- You can come back to the questions you skipped once we have covered
-- the related material in the lectures.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Marks
--
-- Boolean functions     5   MARKS
-- Equality relation     1   MARK
-- First proofs          6   MARKS
-- Natural numbers       13  MARKS
-- Forwards lists        11  MARKS
-- Backwards lists       13  MARKS
-- Combining lists       2   MARKS
-- Quantifiers           9   MARKS
-- Membership            15  MARKS
-- Cellular automaton    10  MARKS
-- Extension             15  MARKS
--
-- TOTAL                 100 MARKS

------------------------------------------------------------------------
-- Warming up: data, functions, proofs
------------------------------------------------------------------------

-- We will be mentioning a Set or two, so let declare variables for them
variable A B C D : Set

------------------------------------------------------------------------
-- Boolean functions (5 MARKS)

-- The cells in a cellular automata only have two possible states: alive
-- or dead. We will be using the booleans as our representation of these
-- two states (true ↦ alive; false ↦ dead).
-- To describe various rules, it is convenient to have some basic functions
-- acting on booleans. So let us get started with them.

-- The type of booleans has two constructors: true and false
data Bool : Set where
  true : Bool
  false : Bool

-- (1 MARK)
-- Implement boolean negation
not : Bool → Bool
not = {!!}

-- (1 MARK)
-- Implement boolean conjunction
_∧_ : Bool → Bool → Bool
_∧_ = {!!}

-- (1 MARK)
-- Implement boolean disjunction
_∨_ : Bool → Bool → Bool
_∨_ = {!!}

-- (1 MARK)
-- Implement boolean exclusive or
_xor_ : Bool → Bool → Bool
_xor_ = {!!}

-- (1 MARK)
-- Implement if then else
infix 0 if_then_else_
if_then_else_ : Bool → A → A → A
if_then_else_ = {!!}

------------------------------------------------------------------------
-- Equality relation (1 MARK)

-- In order to have some unit tests or to prove some properties of our
-- functions, we are going to need propositional equality as well as
-- some related functions and concepts.

-- Propositional equality is the inductive family with a single
-- constructor insisting that both of its indices are equal on the
-- nose.
infix 0 _≡_
data _≡_ (a : A) : A → Set where
  refl : a ≡ a

-- Equality is symmetric
symmetric : ∀ {x y : A} → x ≡ y → y ≡ x
symmetric refl = refl

-- Equality is transitive
transitive : ∀ {x y z : A} → x ≡ y → y ≡ z → x ≡ z
transitive refl eq = eq

-- If `x` is equal to `y` then applying `f` to one is indistinguishable
-- from apply it to the other. Prove it.
cong : ∀ (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

-- The empty type has no constructor. There are no closed proof of it.
-- It is a useful encoding of impossibility.
data ⊥ : Set where

-- From the empty type we can conclude anything: the context we are in
-- is simply absurd.
⊥-elim : ⊥ → A
⊥-elim ()

-- Two terms `x` and `y` are distinct precisely when assuming that there
-- are equal leads to a contradiction i.e. a proof of the empty type.
_≢_ : (x y : A) → Set
x ≢ y = x ≡ y → ⊥

-- (1 MARK)
-- For instance: true and false are not equal!
_ : true ≢ false
_ = {!!}

------------------------------------------------------------------------
-- First proofs (6 MARKS)

-- (1 MARK)
-- Prove that boolean negation is involutive
not-involutive : ∀ b → not (not b) ≡ b
not-involutive = {!!}

-- (1 MARK)
-- Prove that boolean negation is not the identity function
not-not-id : ∀ b → not b ≢ b
not-not-id = {!!}

-- Prove the following de Morgan laws.
-- Bonus for style: good operator definitions can lead to short proofs

-- (2 MARKS)
not-and : ∀ b c → not (b ∧ c) ≡ not b ∨ not c
not-and = {!!}

-- (2 MARKS)
not-or : ∀ b c → not (b ∨ c) ≡ not b ∧ not c
not-or = {!!}

------------------------------------------------------------------------
-- Natural numbers (13 MARKS)

-- The inductive type of natural numbers
data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

variable m n : ℕ

-- (1 MARK)
-- Implement addition by recursion on the first argument
_+_ : ℕ → ℕ → ℕ
m + n = {!!}

-- (1 MARK)
-- Prove that `_+_` commutes with `suc`
+-suc : ∀ m n → m + suc n ≡ suc (m + n)
+-suc = {!!}

-- (1 MARK)
-- Prove that addition is a monoid
zero-+ : ∀ m → zero + m ≡ m
zero-+ = {!!}

-- (1 MARK)
+-zero : ∀ m → m + zero ≡ m
+-zero = {!!}

-- (3 MARKS)
-- hint: +-suc could be useful
+-commutative : ∀ m n → m + n ≡ n + m
+-commutative = {!!}

-- (1 MARK)
+-associative : ∀ m n p → (m + n) + p ≡ m + (n + p)
+-associative = {!!}

-- (1 MARK)
-- Prove that suc is injective
suc-injective : ∀ {m n} → suc m ≡ suc n → m ≡ n
suc-injective = {!!}

-- The sum type
data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

-- (1 MARK)
-- Implement bimap
bimap : (A → C) → (B → D) → A ⊎ B → C ⊎ D
bimap f g s = {!!}

-- (3 MARKS)
-- Prove that equality of natural numbers is decidable
≡-dec : (m n : ℕ) → (m ≡ n) ⊎ (m ≢ n)
≡-dec = {!!}

------------------------------------------------------------------------
-- Lists
-- The state of a cellular automaton can be represented using a list of
-- cells. Let us introduce two types of lists (forwards denoted using `>`,
-- and backwards denoted using `<`) and some operations over them.
-- As a sanity check we will also prove some of these operations' properties.


------------------------------------------------------------------------
-- Forwards lists (11 MARKS)

-- A forwards list is held from its left end and processed left-to-right
-- e.g. in [>1,2,3] the first element is 1, the second 2, etc.

-- Mnemonic: _,-_ has the dash pointing towards the tail
infixr 5 _,-_
data List> (A : Set) : Set where
  [] : List> A
  _,-_ : A → List> A → List> A

-- (1 MARK)
-- Give the list [>1,2,3]
[>1,2,3] : List> ℕ
[>1,2,3] = {!!}

-- (1 MARK)
-- Give the list [>4,5,6]
[>4,5,6] : List> ℕ
[>4,5,6] = {!!}

variable
  xs ys zs : List> A

-- We will be using the same name for the same operations over forwards
-- and backwards so we need to put them in a module. This mean all of
-- the List>-related definition should be indented to be in this inner
-- module.
module List>P where

  -- Programs

  -- (1 MARK)
  -- Implement `replicate` the function that takes a natural number and
  -- a value and returns a list containing `n` copies of the value.
  replicate : ℕ → A → List> A
  replicate = {!!}

  -- (1 MARK)
  -- Implement the length operation, it counts the number of elements
  -- in the list
  length : List> A → ℕ
  length = {!!}

  -- (1 MARK)
  infixr 6 _++_
  -- Append combines the content of two forwards list in an order-respecting
  -- manner e.g. [>1,2,3] ++ [>4,5,6] computes to [>1,2,3,4,5,6].
  -- Feel free to add unit tests
  _++_ : List> A → List> A → List> A
  xs ++ ys = {!!}

  -- (1 MARK)
  -- Implement `map` which, given a function from `A` to `B` and a `List> A`,
  -- applies the function to every element in the list thus creating a `List> B`.
  map : (A → B) → List> A → List> B
  map = {!!}

  -- Proofs

  -- (1 MARK)
  -- Prove that the `length` of the list obtained by calling `replicate`
  -- is the size given as an input.
  length-replicate : (n : ℕ) (x : A) → length (replicate n x) ≡ n
  length-replicate = {!!}

  -- (1 MARK)
  -- Prove that length distributes over append
  length-++ : (xs ys : List> A) → length (xs ++ ys) ≡ length xs + length ys
  length-++ = {!!}

  -- (1 MARK)
  -- Prove that append is associative
  ++-assoc : (xs ys zs : List> A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
  ++-assoc = {!!}

  -- (2 MARKS)
  -- State and prove another property. I can think of various ones e.g.
  -- length-map, replicate-+, map-++, map-map whose names are hopefully
  -- suggestive enough.




------------------------------------------------------------------------
-- Backwards lists (13 MARKS)

-- A backwards list is held from its right and processed righ-to-left
-- e.g. in [<1,2,3] the first element is 3, the second 2, etc.

infixl 5 _-,_
data List< (A : Set) : Set where
  [] : List< A
  _-,_ : List< A → A → List< A

-- (1 MARK)
-- Give the list [<1,2,3]
[<1,2,3] : List< ℕ
[<1,2,3] = {!!}

-- (1 MARK)
-- Give the list [<4,5,6]
[<4,5,6] : List< ℕ
[<4,5,6] = {!!}

variable
  sx sy sz : List< A

-- Implement here the same operations and proofs we had for backwards list
-- length-++ is 3 MARKS here
module List<P where

  -- Programs

  -- (1 MARK)
  -- Creating a backwards list
  replicate : {!!}
  replicate = {!!}

  -- (1 MARK)
  -- The length of a list is its number of elements
  length : {!!}
  length = {!!}

  -- (1 MARK)
  -- Combining two backwards lists
  _++_ : {!!}
  _++_ = {!!}

  -- (1 MARK)
  -- Modifying a backwards list
  map : {!!}
  map = {!!}

  -- Proofs

  -- (1 MARK)
  length-replicate : {!!}
  length-replicate = {!!}

  -- (3 MARKS)
  length-++ : {!!}
  length-++ = {!!}

  -- (1 MARK)
  ++-assoc : {!!}
  ++-assoc = {!!}

  -- (2 MARKS)
  -- State and prove a (different!) property of your own once again.

------------------------------------------------------------------------
-- Combining different kinds of lists (2 MARKS)

-- There are two ways to combine [<1,2,3] and [>4,5,6] in a way that
-- respects the elements' ordering depending on whether we return a
-- forwards or a backwards list.


-- Mnemonic: _<><_ takes a backwards (<) and a forwards (>) list and
-- returns a backwards one (<)

infixl 5 _<><_

-- (1 MARK)
-- Implement fish
_<><_ : List< A → List> A → List< A
_<><_ = {!!}

-- Unit test
_ : [<1,2,3] <>< [>4,5,6] ≡ [] -, 1 -, 2 -, 3 -, 4 -, 5 -, 6
_ = {!!}


-- Mnemonic: _<>>_ takes a backwards (<) and a forwards (>) list and
-- returns a forwards one (>)

infixr 5 _<>>_

-- (1 MARK)
-- Implement chips
_<>>_ : List< A → List> A → List> A
_<>>_ = {!!}

-- Unit test
_ : [<1,2,3] <>> [>4,5,6] ≡ 1 ,- 2 ,- 3 ,- 4 ,- 5 ,- 6 ,- []
_ = {!!}



------------------------------------------------------------------------
-- Getting ready: Quantifiers, Focus
------------------------------------------------------------------------

variable
  P Q : A → Set
  x : A

------------------------------------------------------------------------
-- The universal quantifier for forward lists (9 MARKS)
-- (you could define a similar thing for backward lists but we will not
-- need it here)

-- `All> P xs` states that `P` holds of all the elements in `xs`.
-- The proofs of that statement are:

-- `[]` is the trivial proof that when `xs = []`, the statement is vacuously true.
-- `_,-_` packs together a proof that `P x` holds and that `All> P xs` holds to
-- conclude that `All> P (x ,- xs)` holds.

data All> (P : A → Set) : List> A → Set where
  []   : All> P []
  _,-_ : P x → All> P xs → All> P (x ,- xs)

module All>P where

  -- (1 MARK)
  -- A (safe!) head function extracting a proof that `P x` holds when
  -- we know that `P` holds of all of the elements in `x ,- xs`
  head : All> P (x ,- xs) → P x
  head = {!!}

  -- (1 MARK)
  -- A (safe!) tail function building a proof that `P` holds of all
  -- the elements in `xs` when we already know that it holds of all
  -- of the elements in `x ,- xs`
  tail : All> P (x ,- xs) → All> P xs
  tail = {!!}

  -- (1 MARK)
  -- If the P implies Q and P holds of all the elements in xs then
  -- Q also does!
  map : (∀ {x} → P x → Q x) → All> P xs → All> Q xs
  map = {!!}

-- A `List> A` can be seen as giving an element of type `A` for every
-- element in `xs`. Conversely, if we have an element of a type `B` for
-- every element in `xs` then we have a list of `B`s.
-- `fromList>` and `toList>` witness this. Additionally, we expect them
-- `toList>` to be a left inverse to `fromList>`.

-- (2 MARKS)
-- Implement `fromList>`
fromList> : (xs : List> A) → All> (λ _ → A) xs
fromList> = {!!}

-- (2 MARKS)
-- Implement `toList>`
toList> : All> (λ _ → B) xs → List> B
toList> = {!!}

-- (1 MARK)
-- Prove that `toList>` and `map` commute!
toList>-map : (f : A → B) (xs : All> (λ _ → A) xs) →
              toList> (All>P.map f xs) ≡ List>P.map f (toList> xs)
toList>-map f xs = {!!}

-- (1 MARK)
-- Prove that `toList>` is a left inverse to `fromList>`
from-to-List> : (xs : List> A) → toList> (fromList> xs) ≡ xs
from-to-List> = {!!}


------------------------------------------------------------------------
-- Membership as a context-revealing view (15 MARKS)

-- The following definition is a membership predicate: it states that
-- `x` belongs to `as` (written `x ∈ as`) whenever we can find a way
-- to take `as` apart into:
--   1. a backwards list `sx` acting as a prefix
--   2. the element `x` itself
--   3. a forwards list `xs` acting as a suffix

infix 1 _∈_
infix 3 _[_]_
data _∈_ {A : Set} :  A → List> A → Set where
  _[_]_ : (sx : List< A) (x : A) (xs : List> A) → x ∈ (sx <>> x ,- xs)

-- (2 MARKS)
-- Prove that membership is a proof-relevant notion i.e.
-- you can have two proofs that have the same type and
-- are not equal. Keep it as simple as possible!
proof-relevant :
  let x : ℕ
      x = {!!}
      xs : List> ℕ
      xs = {!!}
      p : x ∈ xs
      p = {!!}
      q : x ∈ xs
      q = {!!}
  in p ≢ q
proof-relevant = {!!}

-- HARD (4 MARKS):
-- Prove that if `x` belongs to ‵xs` and `P` holds of all the elements
-- in `xs` then `P x` also holds. This will require coming up with the type
-- of a tricky auxiliary lemma!
lookup : x ∈ xs → All> P xs → P x
lookup = {!!}


-- Interlude: We can say that a list `xs` is focused if we have a `focus`
-- together with a proof that it belongs to `xs` i.e. that we have a split
-- of `xs` of the form `prefix <>> focus ,- suffix`.
infix 1 !_
record Focused (xs : List> A) : Set where
  constructor !_
  field
    {focus} : A
    member : focus ∈ xs

-- (1 MARK)
-- Write the function that slides the focus one step to the left if possible
-- and behaves like the identity otherwise.
leftwards : Focused xs → Focused xs
leftwards = {!!}

-- (1 MARK)
-- Same but for sliding one step to the right.
rightwards : Focused xs → Focused xs
rightwards = {!!}

-- (2 MARKS)
-- Prove that it is *not* the case that leftwards and rightwards are inverses
-- Keep it as simple as possible!
counter-example :
  let xs : List> ℕ
      xs = {!!}
      f : Focused xs
      f = {!!}
  in leftwards (rightwards f) ≢ f
counter-example = {!!}

-- (1 MARK)
-- Write the function that takes a list of boolean corresponding to left/right
-- instructions (true ↦ left; false ↦ right) and repeatedly moves the focus
-- according to it
following : List> Bool → Focused {A} xs → Focused xs
following = {!!}

{- uncomment the unit test
_ : following (true ,- true ,- false ,- []) (! ([<1,2,3] [ 0 ] [>4,5,6]))
  ≡ ! [] -, 1 -, 2 [ 3 ] 0 ,- 4 ,- 5 ,- 6 ,- []
_ = {!!}
-}

-- HARD (4 MARKS)
-- Prove that for every element in a list we can create a focus around it.
focus : (xs : List> A) → All> (_∈ xs) xs
focus = {!!}

{-
-- Unit test for focus
_ : focus [>1,2,3] ≡ ([] [ 1 ] 2 ,- 3 ,- []) ,- -- 1 in focus
                     ([] -, 1 [ 2 ] 3 ,- []) ,- -- 2 in focus
                     ([] -, 1 -, 2 [ 3 ] []) ,- -- 3 in focus
                     []
_ = {!!}
-}

------------------------------------------------------------------------
-- And now: a cellular automaton! (10 MARKS)
------------------------------------------------------------------------

-- A rule from `A` to `B` is a function that, given a `List> A` and an
-- element that belongs to it, produces a value of typen `B`.
Rule : Set → Set → Set
Rule A B = ∀ {x : A} {xs : List> A} → x ∈ xs → B

-- Here is an example of a rule returning the left neighbour
-- of the current focus (if it exists) and the default value
-- otherwise.
left-neighbour : A → Rule A A
left-neighbour default (_ -, l [ x ] _) = l -- l is on the left of the focus
left-neighbour default ([] [ x ] xs) = default -- nothing is on the left: default!

-- (3 MARKS)
-- Implement `step`, the function which applies a rule to every element
-- in an initial `List> A`.
step : Rule A B → List> A → List> B
step f xs = {!!}

-- The left neighbour rule with default value 17 deployed over [>1,2,3]
_ : step (left-neighbour 17) [>1,2,3] ≡ 17 ,- 1 ,- 2 ,- []
_ = {!!}

-- Rules such as rule 90 (https://en.wikipedia.org/wiki/Rule_90) are more
-- restricted: they operate on a sliding window of size 3 (one element to
-- the left of the focus, the focus, and one element to its right).
-- Such windows can be represented by the following record type.
record Window : Set where
  constructor _,_,_
  field
    left : Bool
    middle : Bool
    right : Bool

-- (1 MARK)
-- Write the function turning a membership proof into the appropriate window.
-- Pad the missing cells with `false`.
pad : Rule Bool Window
pad = {!!}

-- (1 MARK)
-- Implement `rule`, the function turning a window-consuming boolean
-- function into a Rule.
rule : (Window → Bool) → Rule Bool Bool
rule table c = {!!}


-- Implement (at least) rule 90, 30, and 110.
-- https://en.wikipedia.org/wiki/Rule_90
-- https://en.wikipedia.org/wiki/Rule_30
-- https://en.wikipedia.org/wiki/Rule_110

-- (1 MARK)
rule90 : Rule Bool Bool
rule90 = {!!}

-- (1 MARK)
rule30 : Rule Bool Bool
rule30 = {!!}

-- (1 MARK)
rule110 : Rule Bool Bool
rule110 = {!!}

-- (1 MARK)
-- Define an initial state with: 90 dead cells, followed by 1 alive cell,
-- followed by anoter 90 dead cells
0⋯010⋯0 : List> Bool
0⋯010⋯0 = {!!}

-- (1 MARK)
-- Define an initial state with: 180 dead cells, followed by 1 alive cell
0⋯01 : List> Bool
0⋯01 = {!!}


------------------------------------------------------------------------
-- Printing the results
------------------------------------------------------------------------

-- We need a bit of magic to actually get something out on the console

postulate
  Char : Set
  String : Set
  toString : List> Char → String

{-# BUILTIN CHAR Char #-}
{-# BUILTIN STRING String #-}
{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# COMPILE GHC List> = data [] ([] | (:)) #-}
{-# COMPILE GHC toString = T.pack #-}

display : List> Bool → String
display bs = toString (List>P.map (if_then '█' else ' ') bs)

record ⊤ : Set where
  constructor tt

{-# COMPILE GHC ⊤ = data () (()) #-}

postulate
  IO : Set → Set
  pure : A → IO A
  _>>=_ : IO A → (A → IO B) → IO B
  putStrLn : String → IO ⊤

_>>_ : IO A → IO B → IO B
ma >> mb = ma >>= λ _ → mb

{-# BUILTIN IO IO #-}
{-# FOREIGN GHC import qualified Data.Text.IO as T #-}
{-# COMPILE GHC IO = type IO #-}
{-# COMPILE GHC pure = \ _ -> pure #-}
{-# COMPILE GHC _>>=_ = \ _ _ -> (>>=) #-}
{-# COMPILE GHC putStrLn = T.putStrLn #-}

postulate
  wait : ℕ → IO ⊤

{-# FOREIGN GHC import Control.Concurrent (threadDelay) #-}
{-# COMPILE GHC wait = threadDelay . fromIntegral #-}



------------------------------------------------------------------------
-- The function entrypoint

{-# NON_TERMINATING #-}
main : IO ⊤
main = loop 0⋯010⋯0 -- you can modify the initial state here

  where

  loop : List> Bool → IO _
  loop bs = do
    putStrLn (display bs)
    wait 30000
    loop (step rule90 bs) -- you can modify the rule being used here




------------------------------------------------------------------------
-- Extend the project (15 MARKS)
------------------------------------------------------------------------

-- You are free to implement whatever you want. Try to put an emphasis
-- on elegant type & code. Here are some ideas:

-- * a command line interface with user-provided rules (cf. Wolfram codes)
-- * loop detection (if a state repeats itself, stop the program)
-- * treat the state of the cellular automaton as circular: the last cell
--   is considered to the left of the first one, and vice-versa.
