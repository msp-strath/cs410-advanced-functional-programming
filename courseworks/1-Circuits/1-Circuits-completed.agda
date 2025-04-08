------------------------------------------------------------------------
-- Coursework 1: Circuits (100 marks)
--
-- The goal of this coursework is to write a Domain Specific Language
-- to define small circuits. We will use dependent types to keep track
-- of properties of the circuits such as their number of inputs and
-- outputs and prove that they compute specific boolean functions.
--
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

open import Agda.Builtin.FromNat
open import Data.Bool.Base using (Bool; true; false; not; _∧_; _∨_; _xor_; if_then_else_)
open import Data.Fin.Base using (Fin; zero; suc; fromℕ; _↑ˡ_; _↑ʳ_)
import Data.Fin.Literals; instance finLiterals = λ {n} → Data.Fin.Literals.number n
open import Data.Nat.Base as Nat using (ℕ; zero; suc; _+_; _⊔_; _*_; _≤_; z≤n; s≤s; NonZero)
import Data.Nat.Literals; instance natLiterals = Data.Nat.Literals.number
open import Data.Nat.Properties
  using ( +-comm; +-assoc; +-identityʳ
        ; *-identityˡ; *-identityʳ
        ; module ≤-Reasoning
        ; ≤-reflexive; +-monoˡ-≤
        ; ⊔-idem)
open import Data.Product.Base using (_,_)
open import Data.Unit.Base using (tt)
open import Data.Vec.Base using (Vec; []; _∷_; replicate; head; _++_; lookup)

open import Function.Base using (_∘_; _$_)

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; module ≡-Reasoning)

variable i j o m n : ℕ

------------------------------------------------------------------------
-- Marks
--
-- Boolean logic            6 MARKS
-- Vector functions        11 MARKS
-- Syntax of circuits       5 MARKS
-- Semantics of circuits   10 MARKS
-- Logic gates             18 MARKS
-- Complex circuits        30 MARKS
-- Extension               20 MARKS
--
-- TOTAL                   100 MARKS

------------------------------------------------------------------------
-- Boolean logic (6 MARKS)
------------------------------------------------------------------------

-- (1 MARK)
-- Define nand
nand : Bool → Bool → Bool
nand x y = not (x ∧ y)

-- (1 MARK)
-- Prove that not is involutive
not-involutive : ∀ b → not (not b) ≡ b
not-involutive false = refl
not-involutive true  = refl

-- (1 MARK)
-- Prove that the conjunction is idempotent
∧-diag : ∀ b → b ∧ b ≡ b
∧-diag false = refl
∧-diag true  = refl

-- (3 MARK)
-- Prove the 2 de Morgan laws
-- (Bonus mark for making the proofs as short as possible)
not-∧ : ∀ x y → not (x ∧ y) ≡ not x ∨ not y
not-∧ false y = refl
not-∧ true  y = refl

not-∨ : ∀ x y → not (x ∨ y) ≡ not x ∧ not y
not-∨ false y = refl
not-∨ true  y = refl

------------------------------------------------------------------------
-- Vector functions and their properties (11 MARKS)
------------------------------------------------------------------------

variable A B C : Set

-- (1 MARK)
-- Implement map, the function applying a function to all of
-- values stored in a vector
map : (A → B) → Vec A n → Vec B n
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

-- (1 MARK)
-- Flatten a vector of vectors.
-- Hint: look at the definition of _*_ in terms of _+_ and
-- consider using _++_
concat : Vec (Vec A n) m → Vec A (m * n)
concat [] = []
concat (xs ∷ xss) = xs ++ concat xss

_ : concat ((Nat.zero ∷ 1 ∷ []) ∷ (2 ∷ 3 ∷ []) ∷ []) ≡ 0 ∷ 1 ∷ 2 ∷ 3 ∷ []
_ = refl

-- (1 MARK)
-- Given a natural number n, enumerate all the (Fin n)
-- values from smallest (0) to largest (n-1).
allFin : (n : ℕ) → Vec (Fin n) n
allFin zero = []
allFin (suc n) = zero ∷ map suc (allFin n)

_ : lookup (allFin 4) 2 ≡ 2
_ = refl

-- SplitAt is a record type describing how a vector of size
-- (m + n) can be taken into
--  * a record named left  of size m
--  * a record named right of size n
-- such that (left ++ right) is the original vector
record SplitAt (m : ℕ) {n : ℕ} (xs : Vec A (m + n)) : Set where
  constructor mkSplitAt
  field left : Vec A m
        right : Vec A n
        correct : left ++ right ≡ xs

-- (1 MARK)
-- Prove that if we know how to split (xs) according to m
-- then we know how to split (x ∷ xs) according to (suc m)
cons : ∀ (x : A) {xs} → SplitAt m {n} xs → SplitAt (suc m) (x ∷ xs)
cons x (mkSplitAt left right correct)
  = mkSplitAt (x ∷ left) right (cong (x ∷_) correct)

-- (1 MARK)
-- Prove that we can always split a vector
splitAt : (m : ℕ) (xs : Vec A (m + n)) → SplitAt m xs
splitAt zero xs = mkSplitAt [] xs refl
splitAt (suc m) (x ∷ xs) = cons x (splitAt m xs)

-- (1 MARK)
-- Prove that map distributes over replicate:
map-replicate : (f : A → B) (n : ℕ) (x : A) →
  map f (replicate n x) ≡ replicate n (f x)
map-replicate f zero x = refl
map-replicate f (suc n) x = cong (f x ∷_) (map-replicate f n x)

-- (1 MARK)
-- Prove that map distributes over append
map-++ : (f : A → B) (xs : Vec A m) (ys : Vec A n) →
  map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++ f [] ys = refl
map-++ f (x ∷ xs) ys = cong (f x ∷_) (map-++ f xs ys)

-- (1 MARK)
-- Prove that map distributes over concat
map-concat : (f : A → B) (xss : Vec (Vec A n) m) →
  map f (concat xss) ≡ concat (map (map f) xss)
map-concat f [] = refl
map-concat f (xs ∷ xss) = let open ≡-Reasoning in begin
  map f (xs ++ concat xss)       ≡⟨ map-++ f xs (concat xss) ⟩
  map f xs ++ map f (concat xss) ≡⟨ cong (map f xs ++_) (map-concat f xss) ⟩
  map f xs ++ concat (map (map f) xss) ∎

-- (1 MARK)
-- Prove that we can fuse two consecutive maps into a single one
map-map : (g : B → C) (f : A → B) (xs : Vec A m) →
  map g (map f xs) ≡ map (g ∘ f) xs
map-map g f [] = refl
map-map g f (x ∷ xs) = cong (g (f x) ∷_) (map-map g f xs)

-- (2 MARKS)
-- Prove that mapping lookup on allFin yields the identity
map-lookup-allFin : (xs : Vec A m) → map (lookup xs) (allFin m) ≡ xs
map-lookup-allFin [] = refl
map-lookup-allFin {m = suc m} (x ∷ xs) = let open ≡-Reasoning in begin
  map (lookup (x ∷ xs)) (allFin (suc m))
    ≡⟨⟩
  x ∷ map (lookup (x ∷ xs)) (map suc (allFin m))
    ≡⟨ cong (x ∷_) (map-map (lookup (x ∷ xs)) suc (allFin m)) ⟩
  x ∷ map (lookup (x ∷ xs) ∘ suc) (allFin m)
    ≡⟨⟩
  x ∷ map (lookup xs) (allFin m)
    ≡⟨ cong (x ∷_) (map-lookup-allFin xs) ⟩
  x ∷ xs
    ∎

------------------------------------------------------------------------
-- Syntax of circuits (5 MARKS)
------------------------------------------------------------------------

-- First we introduce a type of circuits. It is indexed by
-- two natural numbers:
--   i represents the number of inputs to the circuit
--   o represents the number of outputs to the circuit

data Circuit : (i o : ℕ) → Set where
  -- `false is the constructor representing the constant bit 0
  -- Viewed as a circuit it takes 0 input and has exactly 1 output
  -- that is constantly false. It corresponds to the diagram
  --
  --          ⌈‾‾‾‾‾‾‾⌉
  --          | false |---- 0
  --          ⌊_______⌋

  `false : Circuit 0 1

  -- `nand is the constructor representing the universal nand gate
  -- It takes two inputs and returns a single output and corresponds
  -- to the diagram:
  --
  --   x₁ ----⌈‾‾‾‾‾‾⌉
  --          | nand |---- y₁ = nand x₁ x₂
  --   x₂ ----⌊______⌋

  `nand : Circuit 2 1

  -- `seq  sequentially composes two circuits: if the first one has
  -- i inputs and m outputs and the second one m inputs and o outputs
  -- we can plug the first's outputs into the second's inputs and
  -- obtain a bigger circuit with i inputs and o outputs.
  -- It corresponds to the following diagram
  --
  --   x₁ ----⌈‾‾‾‾‾‾⌉---- y₁ ----⌈‾‾‾‾‾‾⌉---- z₁
  --   ⋮       |  c₁  |     ⋮       |  c₂  |
  --   xᵢ ----⌊______⌋---- yₘ ----⌊______⌋---- zₒ

  `seq  : (c₁ : Circuit i m) (c₂ : Circuit m o) → Circuit i o

  -- `par composes two circuits in parallel: if the first one
  -- has i inputs and o outputs and the second one has m inputs
  -- and n outputs, we obtain a bigger circuit with (i + m) inputs
  -- and (o + n) outputs.
  -- It corresponds to the following diagram:
  --
  --   x₁ ------ u₁ ----⌈‾‾‾‾‾‾⌉---- y₁ ---- z₁
  --             ⋮       |  c₁  |     ⋮
  --             uᵢ ----⌊______⌋---- yₘ
  --   ⋮                                      ⋮
  --             l₁ ----⌈‾‾‾‾‾‾⌉---- t₁
  --             ⋮       |  c₂  |     ⋮
  --   x₍ᵢ₊ₘ)--- sₘ ----⌊______⌋---- tₙ ---- z₍ₒ₊ₙ₎

  `par  : (c₁ : Circuit i o) (c₂ : Circuit m n) → Circuit (i + m) (o + n)

  -- Last but not least, `mix allows you to produce arbitrary wiring
  -- patterns mapping (possibly duplicating, throwing away, permutting,
  -- etc.) i inputs into o outputs. It takes a vector of length o
  -- containing (Fin i) values. Each (Fin i), a finite number up to i,
  -- describes the input the specific output is linked to.
  -- For instance, `mix (1 ∷ 0 ∷ 3 ∷ []) would correspond to the
  -- following diagram linking
  -- 1 ∷ 0 ∷ 3 ∷ []
  -- |   |   ⌊ the third output to the 4th input (Fins start indexing at 0)
  -- |   ⌊ the second output to the 1st input
  -- ⌊ the first output to the 2nd input
  --
  --   x₁ -----, ,---- y₁ = x₂
  --           ><
  --   x₂ -----' '---- y₂ = x₁
  --   x₃ ---⊣
  --   x₄ ------------ y₃ = x₄

  `mix  : Vec (Fin i) o → Circuit i o


-- (1 MARK)
-- Implement the empty circuit with 0 inputs and 0 outputs.
-- Build it using `mix.
`empty : Circuit 0 0
`empty = `mix []

-- (1 MARK)
-- The identity wire has 1 input and 1 output.
-- Build it using `mix. It should correspond to the circuit
--
--   x --------- x
--
`id : Circuit 1 1
`id = `mix (zero ∷ [])

-- (1 MARK)
-- The identity circuit for n wires can be defined generically.
-- Do so below.
`idₙ : (n : ℕ) → Circuit n n
`idₙ n = `mix (allFin n)

-- (1 MARK)
-- Build `dup, the circuit taking one input and duplicating it
-- to produce two outputs. It should correspond to the circuit
--
--         ,---- x
--   x ---<
--         '---- x
--
`dup : Circuit 1 2
`dup = `mix (zero ∷ zero ∷ [])

-- (1 MARK)
-- Sometimes expressions do not quite line up and
-- we can only *prove* that the input/output arities
-- we get are equal to the ones we want.
-- Implement a combinator allowing you to adapt the
-- arities in that case.
_[_]_ : m ≡ i → Circuit i o → o ≡ n → Circuit m n
refl [ c ] refl = c

------------------------------------------------------------------------
-- Semantics of circuits (10 MARKS)
------------------------------------------------------------------------

-- (5 MARKS)
-- Define the 'depth' of a circuit as the maximum number of
-- nand logic gates separating its inputs from its outputs.
-- It is an important measure as it gives a sense of the
-- circuit's latency (the time it takes for the input to be
-- turned into the outputs).
depth : Circuit i o → ℕ
depth `false     = 0
depth `nand      = 1
depth (`seq s t) = depth s + depth t
depth (`par s t) = depth s ⊔ depth t
depth (`mix s)   = 0

-- (5 MARKS)
-- Define the meaning of a circuit as a function from
-- vectors of boolean inputs to vectors of boolean outputs
-- Hint: some of the functions over vectors we defined above
-- may be useful
meaning : Circuit i o → (Vec Bool i → Vec Bool o)
meaning `false _ = false ∷ []
meaning `nand (a ∷ b ∷ [])
  = nand a b ∷ []
meaning (`seq s t) ρ
  = let ρ = meaning s ρ in meaning t ρ
meaning (`par s t) ρ
  = let (mkSplitAt ρₛ ρₜ _) = splitAt _ ρ in
    meaning s ρₛ ++ meaning t ρₜ
meaning (`mix ws) ρ
  = map (lookup ρ) ws


------------------------------------------------------------------------
-- Building logic gates and proving their properties (18 MARKS)
------------------------------------------------------------------------

-- Channelling your CS106 memories, we are going to build
-- basic logic gates in terms of the universal gate `nand,
-- the constant wire `false and wiring components.

-- (1 MARK)
-- Build `not. Remember that (x ∧ x ≡ x) and so that
-- (¬ (x ∧ x) ≡ ¬ x) i.e. not can be obtained by plugging
-- the same input into both of nand's input ports like so:
--
--         ,----⌈‾‾‾‾‾‾⌉
--   x ---<     | nand |--- not x
--         '----⌊______⌋

`not : Circuit 1 1
`not = `seq `dup `nand

-- Test: not's depth is 1
_ : depth `not ≡ 1
_ = refl

-- (1 MARK)
-- Prove that the meaning of `not is exactly the boolean
-- function not
not-correct : ∀ x → meaning `not (x ∷ []) ≡ not x ∷ []
not-correct x = cong (λ v → not v ∷ []) (∧-diag x)

-- (1 MARK)
-- Build the function turning a boolean into a constant
-- signal corresponding to it
`bit : Bool → Circuit 0 1
`bit true  = `seq `false `not
`bit false = `false

-- (1 MARK)
-- Prove that bit's meaning is indeed the appropriate constant bit
bit-correct : ∀ b → meaning (`bit b) [] ≡ b ∷ []
bit-correct true  = refl
bit-correct false = refl

-- (2 MARK)
-- Now implement `and, the circuit taking the conjunction
-- of its two inputs
`and : Circuit 2 1
`and = `seq `nand `not

-- Test: and's depth is 2
_ : depth `and ≡ 2
_ = refl

-- (2 MARK)
-- Prove that your implementation is correct: the meaning of
-- `and is the conjunction of its inputs.
and-correct : ∀ x y → meaning `and (x ∷ y ∷ []) ≡ (x ∧ y) ∷ []
and-correct x y = let open ≡-Reasoning in begin
  meaning `and (x ∷ y ∷ [])                 ≡⟨⟩
  meaning `not (meaning `nand (x ∷ y ∷ [])) ≡⟨ not-correct (not (x ∧ y)) ⟩
  not (not (x ∧ y)) ∷ []                    ≡⟨ cong (_∷ []) (not-involutive (x ∧ y)) ⟩
  x ∧ y ∷ []                                ∎

-- (1 MARK)
-- Implement `or, the circuit taking the disjunction
-- of its two inputs
`or : Circuit 2 1
`or = `seq (`par `not `not) `nand

-- Test: `or's depth is 2
_ : depth `or ≡ 2
_ = refl

-- (3 MARK)
-- Prove that your implementation is correct: the meaning of
-- `or is the disjunction of its inputs.
or-correct : ∀ x y → meaning `or (x ∷ y ∷ []) ≡ (x ∨ y) ∷ []
or-correct x y = let open ≡-Reasoning in begin
  meaning `or (x ∷ y ∷ [])
    ≡⟨⟩
  meaning `nand
    (head (meaning `not (x ∷ [])) ∷
     head (meaning `not (y ∷ [])) ∷ [])
    ≡⟨ cong₂ (λ x y → meaning `nand (head x ∷ head y ∷ []))
         (not-correct x)
         (not-correct y) ⟩
  nand (not x) (not y) ∷ []
    ≡⟨ cong (_∷ []) (not-∧ (not x) (not y)) ⟩
  (not (not x) ∨ not (not y)) ∷ []
    ≡⟨ cong₂ (λ x y → (x ∨ y) ∷ []) (not-involutive x) (not-involutive y) ⟩
  (x ∨ y) ∷ [] ∎


-- (1 MARK)
-- Implement `xor
`xor : Circuit 2 1
`xor = `seq (`mix (0 ∷ 1 ∷ 0 ∷ 1 ∷ []))
     $ `seq (`par (`seq (`par `id `not) `and)
                  (`seq (`par `not `id) `and))
     $ `or

-- (2 MARK)
-- Prove `xor correct
xor-correct : ∀ x y → meaning `xor (x ∷ y ∷ []) ≡ (x xor y) ∷ []
xor-correct false false = refl
xor-correct false true  = refl
xor-correct true  false = refl
xor-correct true  true  = refl

-- (1 MARK)
-- Implement `eq, the circuit whose output is 1 if
-- its inputs are equal, and 0 otherwise
`eq : Circuit 2 1
`eq = `seq `xor `not

_≡ᵇ_ : Bool → Bool → Bool
true  ≡ᵇ true  = true
false ≡ᵇ false = true
_     ≡ᵇ _     = false

-- (2 MARK)
-- Prove `eq correct: it behaves the same as the equality
-- test defined above
eq-correct : ∀ x y → meaning `eq (x ∷ y ∷ []) ≡ x ≡ᵇ y ∷ []
eq-correct false false = refl
eq-correct false true  = refl
eq-correct true  false = refl
eq-correct true  true  = refl

------------------------------------------------------------------------
-- Building more complex circuits (30 MARKS)
------------------------------------------------------------------------

-- (1 MARK)
-- Implement bits, the constant circuit returning exactly
-- the outputs passed as an argument
`bits : Vec Bool o → Circuit 0 o
`bits [] = `empty
`bits (v ∷ vs) = `par (`bit v) (`bits vs)

-- (1 MARK)
-- Prove bits correct: its meaning is exactly its input
bits-correct : (ρ : Vec Bool o) → meaning (`bits ρ) [] ≡ ρ
bits-correct [] = refl
bits-correct (b ∷ ρ) = cong₂ _++_ (bit-correct b) (bits-correct ρ)

-- (1 MARK)
-- Write fan, the circuit copying its input n times.
-- It should look something like
--   x ----⌈‾‾‾‾‾‾⌉---- y₁ = x
--         | fan  |     ⋮
--         ⌊______⌋---- yₙ = x
-- Hint: use functions imported from Data.Vec.Base
`fanₙ : (n : ℕ) → Circuit 1 n
`fanₙ n = `mix (replicate n zero)

-- (1 MARK)
-- Prove fan correct
fan-correct : ∀ n x → meaning (`fanₙ n) (x ∷ []) ≡ replicate n x
fan-correct n x = map-replicate (lookup (x ∷ [])) n zero


-- (3 MARKS)
-- Implement the circuit copying its group of inputs n times
-- It should look something like:
--
--   x₁ ----⌈‾‾‾‾‾‾⌉---- y₁ = x₁        ‵|
--   ⋮       |      |     ⋮                > 1st copy of the inputs
--   xᵢ ----|      |---- yᵢ = xᵢ        ,|
--          |      |
--          | copy |       ⋮
--          |      |
--          |      |---- y₍ₙ₋₁₎ᵢ = x₁   `|
--          |      |     ⋮                > nth copy of the inputs
--          ⌊______⌋---- yₙᵢ     = xᵢ   ,|
-- Hint: use functions imported from Data.Vec.Base
`copyₙ : (n : ℕ) → Circuit i (n * i)
`copyₙ {i} n = `mix (concat (replicate n (allFin i)))

-- (5 MARKS)
-- Prove `copyₙ correct: its outputs are literally just its
-- inputs replicated n times.
-- Hint: use the properties of the functions imported from
-- Data.Vec.Properties!
-- It may be useful to additionally prove:
-- map-concat : {A B : Set} (f : A → B) (xss : Vec (Vec A m) n) →
--             map f (concat xss) ≡ concat (map (map f) xss)
copy-correct : ∀ n ρ → meaning (`copyₙ {i} n) ρ ≡ concat (replicate n ρ)
copy-correct {i} n ρ = let open ≡-Reasoning in begin
  meaning (`copyₙ n) ρ
    ≡⟨⟩
  map (lookup ρ) (concat (replicate n (allFin i)))
    ≡⟨ map-concat (lookup ρ) (replicate n (allFin i)) ⟩
  concat (map (map (lookup ρ)) (replicate n (allFin i)))
    ≡⟨ cong concat (map-replicate (map (lookup ρ)) n (allFin i)) ⟩
  concat (replicate n (map (lookup ρ) (allFin i)))
    ≡⟨ cong (concat ∘ replicate n) (map-lookup-allFin ρ) ⟩
  concat (replicate n ρ)
    ∎

-- Defining double-unfold, a useful lemma for the next
-- question, and later down the file too
double-unfold : ∀ n → 2 * n ≡ n + n
double-unfold n = cong (n +_) (+-identityʳ n)

-- (1 MARK)
-- Implement dup as a special case of copy:
-- it takes its inputs and duplicates them.
`dupₙ : (n : ℕ) → Circuit n (n + n)
`dupₙ n = refl [ `copyₙ 2 ] double-unfold n


-- (4 MARKS)
-- Implement shuffle, the circuit taking 4 blocks of inputs
-- and interleaving them. See the test case below to see how
-- it is meant to work.
-- Hint: use some of the functions imported from Data.Fin.Base
`shuffle : (i j m n : ℕ) → Circuit ((i + m) + (j + n)) ((i + j) + (m + n))
`shuffle i j m n = `mix ((leftₗ ++ rightₗ) ++ (leftᵣ ++ rightᵣ)) where

  leftₗ : Vec (Fin ((i + m) + (j + n))) i
  leftₗ = map (λ k → (k ↑ˡ m) ↑ˡ (j + n)) (allFin i)

  leftᵣ : Vec (Fin ((i + m) + (j + n))) m
  leftᵣ = map (λ k → (i ↑ʳ k) ↑ˡ (j + n)) (allFin m)

  rightₗ : Vec (Fin ((i + m) + (j + n))) j
  rightₗ = map (λ k → (i + m) ↑ʳ (k ↑ˡ n)) (allFin j)

  rightᵣ : Vec (Fin ((i + m) + (j + n))) n
  rightᵣ = map (λ k → (i + m) ↑ʳ (j ↑ʳ k)) (allFin n)


-- 0,1,2,3,4,5,6,7,8,9,10,11 viewed as:
--  a first block 0,1,2,3,4
--      split into A = 0,1 and B = 2,3,4
--  a second block 5,6,7,8,9,10,11
--      split into C = 5,6,7 and D = 8,9,10,11
-- Using shuffle to act on ABCD, we reorganise it into ACBD
_ : `shuffle 2 3 3 4
  ≡ `mix ( 0 ∷ 1           -- first 2 bits of the first half
         ∷ 5 ∷ 6 ∷ 7       -- first 3 bits of the second half
         ∷ 2 ∷ 3 ∷ 4       -- remainder of the first half
         ∷ 8 ∷ 9 ∷ 10 ∷ 11 -- remainder of the second block
         ∷ [])
_ = refl


-- (5 MARKS)
-- HARD
-- Implement the function taking a circuit C expecting i+j inputs
-- and returning the circuit taking two sequence of n blocks of
-- i (respectively j) inputs and applying C in parallel to these
-- n blocks.
-- It should look something like
--
--   x₁₁ ----⌈‾‾‾‾‾‾⌉ ---- z₁₁
--    ⋮       |  b   |       ⋮    = C(x₁₁,⋯,x₁ᵢ,y₁₁,⋯,y₁ⱼ)
--   x₁ᵢ ----|  l   | ---- z₁ₒ
--    ⋮       |  o   |
--   xₙᵢ ----|  c   |
--           |  k   |    ⋮
--   y₁₁ ----|  w   |
--    ⋮       |  i   |
--   y₁ⱼ ----|  s   | ---- zₙ₁
--    ⋮       |  e   |       ⋮    = C(xₙ₁,⋯,xₙᵢ,yₙ₁,⋯,yₙⱼ)
--   yₙⱼ ----⌊______⌋ ---- zₙₒ
--
`blockwiseₙ : Circuit (i + j) o → (n : ℕ) → Circuit (n * i + n * j) (n * o)
`blockwiseₙ             f zero    = `empty
`blockwiseₙ {i} {j} {o} f 1
  = cong₂ _+_ (*-identityˡ i) (*-identityˡ j) [ f ] (sym $ *-identityˡ o)
`blockwiseₙ {i} {j} {o} f (suc n)
  = `seq (`shuffle i j (n * i) (n * j))
  $ `par f (`blockwiseₙ f n)


-- (1 MARK)
-- As a corollary of `blockwise, define pairwise the function
-- doing the same with a binary circuit
`pairwiseₙ : Circuit 2 1 → (n : ℕ) → Circuit (n + n) n
`pairwiseₙ f n
  = sym (cong₂ _+_ (*-identityʳ n) (*-identityʳ n))
  [ `blockwiseₙ f n
  ] *-identityʳ n

-- (5 MARK)
-- HARD
-- Combine previous definitions to implement `branch,
-- the circuit that uses its first input to decide
-- between two circuits with the same input/output
-- arities (here passed as a function from Bool to Circuit i o)
`branch : (Bool → Circuit i o) → Circuit (suc i) o
`branch {i} {o} f
  = `seq (`par (`fanₙ (o + o)) $ `seq (`dupₙ i) (`par (f true) (f false)))
  $ `seq (`shuffle o o o o)
  $ `seq (`par (`pairwiseₙ `and o) (`pairwiseₙ (`seq (`par `not `id) `and) o))
  (`pairwiseₙ `or o)

-- Test: we can define `swap by branching twice to collect two
-- inputs x & y and outputing constant bits in y & x order.
`swap : Circuit 2 2
`swap = `branch $ λ x → `branch $ λ y → `par (`bit y) (`bit x)

-- Test: swap should indeed swap its input.
_ : ∀ x y → meaning `swap (x ∷ y ∷ []) ≡ y ∷ x ∷ []
_ = λ { true  true  → refl
      ; true  false → refl
      ; false true  → refl
      ; false false → refl }

-- (2 MARKS)
-- Reusing previous definitions, define `tabulate the
-- function turning a function operating on booleans
-- into a circuit with the same meaning.
`tabulate : (Vec Bool i → Vec Bool o) → Circuit i o
`tabulate {zero}  f = `bits (f [])
`tabulate {suc i} f = `branch (λ b → `tabulate (f ∘ (b ∷_)))


------------------------------------------------------------------------
-- Extend the project (20 MARKS)
------------------------------------------------------------------------

-- You are free to implement whatever you want. Try to put an emphasis
-- on elegant type & code. Here are some ideas:

-- * A collection of CS106-type circuits (proven correct? maximasing parallelism?)
-- * A renderer displaying a circuit as a string (or a dot graph?)
-- * A compiler from a small language to circuits
-- * Recursive definitions of complex circuits
-- * Compilation to an actual hardware description language

-- You will be marked on how idiomatic your types and definitions are,
-- on the complexity of the extension, and on how well you made use of
-- Agda's features compared to e.g. Haskell.
