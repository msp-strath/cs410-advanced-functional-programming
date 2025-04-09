-- These are the annotated notes which include more detail about what the code is doing.
-- NB: there was a preamble at the start of this lecture about how to use equational reasoning syntax to prove propositional equality. This has not been copied here and the video "Lecture 8: Proof by reflection" should be consulted.

-- Quickly importing and defining a bunch of stuff:
open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)

open import Data.List.Base using (List; []; _∷_)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)

variable A B C : Set
variable m n p : ℕ
variable
  x : A
  xs : List A

data Dec (A : Set) : Set where
    yes : A -> Dec A
    no  : ¬ A -> Dec A

data Even : ℕ -> Set
data Odd  : ℕ -> Set

data Even where
    zero : Even zero
    suc  : Odd n -> Even (suc n)

data Odd where
    suc : Even n -> Odd (suc n)

even? : ∀ n -> Dec (Even n)
odd?  : ∀ n -> Dec (Odd n)

even? zero = yes zero
even? (suc n) with odd? n
... | yes oddn = yes (suc oddn)
... | no ¬oddn = no \ where (suc oddn) -> ¬oddn oddn

odd? zero = no \ ()
odd? (suc n) with even? n
... | yes evenn = yes (suc evenn)
... | no ¬evenn = no \ where (suc evenn) -> ¬evenn evenn


{-
Continuing from yesterday, we are now going to try and build something that will find a proof for us. Let's suppose that we're trying to find proofs that a number is even, without having to chain huge quantities of sucs together.
-}
isYes : Dec A -> Set
isYes (yes _) = ⊤
isYes (no _)  = ⊥

isEven : (n : ℕ) -> {_ : isYes (even? n)} -> Even n
isEven n {constraint} with even? n
... | yes evenn = evenn

_ : Even 100
_ = isEven 100
{-
We start by building something that can identify whether our decisions are yes or no. This gives us the ability to then say that we can give you an Even n precisely when we know that the answer to even? n is yes. Essentially, all the work for isEven is being done in the typeline.

We can then extend our definition with an extra pattern "even? n". Now our constraint has the type "isYes p". This is the magic of with: as we make observations by inspecting the pattern, the type of the constraint will get more precise. Specifically, once we split p and get yes evenn, constraint now has the type ⊤, and we as humans can see that this is correct: we have what we need, something of type Even n, so we're done.

This principle is called proof by reflection: this is the idea that we are running a computation *at the type level*, in order to do a proof for us. Here, our type-level computation is even? n, and because our computation is concrete, it can manage to go all the way through and work it out for us. Generally, this is useful for problems that are *easy* to prove but also *annoying* to prove by hand. The essence of this proof principle can be expressed in the general form:
-}
magic : (d : Dec A) -> {_ : isYes d} -> A
magic (yes p) = p
{-
and if we wanted to, we could write our proof that 100 is even using this, as:
_ : Even 100
_ = magic (even? 100)
-}


{-
Going back to our notions of existence from yesterday with Markov, we saw that if we have a domain that we can enumerate (like the natural numbers), we can search it, but Agda will not know the search is terminating. However, there are weaker notions of existence which are finite and thus can be searched in a provably terminating manner.
-}

-- First we have All, aka universal quantification:
data All (P : A -> Set) : List A -> Set where
    []  : All P []
    _∷_ : P x -> All P xs -> All P (x ∷ xs)

_ : All Even (0 ∷ 100 ∷ 20 ∷ 42 ∷ [])
_ = magic (even? 0) ∷ magic (even? 100) ∷ magic (even? 20) ∷ magic (even? 42) ∷ []
{-
It is trivially true that P is true of all values in the empty list: in a nonempty list, we just check that P is true of the head and of all the elements in the tail.
-}

-- We also have Any, aka existential quantification:
data Any (P : A -> Set) : List A -> Set where
    win  : P x -> Any P (x ∷ xs)
    next : Any P xs -> Any P (x ∷ xs)
{-
Here, if the list is empty there is no way for a value in it to satisfy the predicate, so we don't have a constructor for the empty list. In our nonempty list, we can check either if our current value satisfies and we've won, or if any other value in the list satisfies and we need to go to the next.

Thinking back to our Markov case before, we could now implement a similar version of search which, rather than searching the whole set of the natural numbers, searches a list of xs. Because Agda knows that list is finite, Agda will know that search is terminating.
-}
