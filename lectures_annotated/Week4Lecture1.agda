-- These are the annotated notes which include more detail about what the code is doing.

open import Data.Empty using (⊥)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
-- ⊎ is the canonical Or (\u+), × is the canonical And (\x), and ¬ is the canonical Not (\neg).

data Dec (A : Set) : Set where
    yes : A -> Dec A
    no  : ¬ A -> Dec A

variable A B C : Set


{-
Last time, we were looking at the Curry-Howard principle, the correspondence between types and mathematical statements. Now that we have a functioning definition of all of our logical operators and a notion of decidability, we can start to prove some things. We'll start by having a look at De Morgan's laws of substitution.
-}

-- First, that "Not (A Or B) = (Not A) And (Not B)":
¬-⊎-⇒ : ¬ (A ⊎ B) -> ¬ A × ¬ B
¬-⊎-⇒ ¬[a⊎b] = (\ a -> ¬[a⊎b] (inj₁ a)) , (\ b → ¬[a⊎b] (inj₂ b))
{-
Here, we have our proof that ¬[a⊎b], and our goal is ¬ A × ¬ B, so clearly we need to start by constructing something of the shape ? × ?. Now our left half has the goal ¬ A and the right half has the goal ¬ B. Agda can actually figure these out for us using C-c C-a (here they've been renamed to make it clearer).

In the left hand side, we're use the lambda to take a proof of A, a. Now our goal is to prove ⊥ which we can get by proving a contradiction. Here we inject a into the left hand side of our assumption. Proof of A would make A ⊎ B true, which we know is not possible, ergo our assumption a is wrong and we have ¬ A. We then repeat the same strategy on the right hand side taking an assumption of b.
-}

-- And in the opposite direction:
¬-⊎-⇐ : ¬ A × ¬ B -> ¬ (A ⊎ B)
¬-⊎-⇐ (¬a , ¬b) (inj₁ a) = ¬a a
¬-⊎-⇐ (¬a , ¬b) (inj₂ b) = ¬b b
{-
This proof is a little trickier, so Agda can't work it out. However, we can see that once we have our (¬a , ¬b), our normalised goal is now A ⊎ B -> ⊥. Thus, if we use our injections to get our hands on proofs of a and b, then we can easily prove our ⊥ by contradiction.

We have now successfully proved this law in both directions, so this law still holds.
-}


-- However, in some cases we will struggle, as with "Not (A And B) = (Not A) Or (Not B)":
-- ¬-×-⇒ : ¬ (A × B) -> ¬ A ⊎ ¬ B
-- ¬-×-⇒ ¬[a×b] = {!   !}
{-
Here we don't have enough information to know whether to go left or right - we're not sure whether to try proving that A is impossible or that B is impossible. For now, we can't get anywhere with this.
-}

-- We *can* prove the reverse implication, however, since here we have one extra bit of information:
¬-×-⇐ : ¬ A ⊎ ¬ B -> ¬ (A × B)
¬-×-⇐ (inj₁ ¬a) (a , b) = ¬a a
¬-×-⇐ (inj₂ ¬b) (a , b) = ¬b b
-- Again, we make progress by assuming (a , b) and then using that assumption to produce a contradiction.


{-
So how can we recover that last law that we're missing? Well, we need one more bit of information. We can achieve this by implementing it with decidability!
-}
¬-×-⇒ : Dec A -> ¬ (A × B) -> ¬ A ⊎ ¬ B
¬-×-⇒ (yes a) ¬[a×b] = inj₂ (\ b -> ¬[a×b] (a , b))
¬-×-⇒ (no ¬a) ¬[a×b] = inj₁ ¬a
{-
Here we start by introducing a?, our knowledge of whether a is true or false, and then we can grab ¬[a×b] as before. Now, however, we can make a choice: if a is true then we go right, and if a is false we can go left.
-}


{-
Now we're going to see how we can use Curry-Howard to actually write interesting programs. We'll start with equality of natural numbers.
-}
open import Data.Nat.Base using (ℕ; zero; suc; pred)
open import Function.Base using (_∘′_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

nat-eq-dec : (m n : ℕ) -> Dec (m ≡ n)
nat-eq-dec zero    zero    = yes refl
nat-eq-dec zero    (suc n) = no \ ()
nat-eq-dec (suc m) zero    = no \ ()
nat-eq-dec (suc m) (suc n) with nat-eq-dec m n
... | yes m≡n   = yes (cong suc m≡n)
... | no ¬[m≡n] = no \ sucm≡sucn -> ¬[m≡n] (cong pred sucm≡sucn)
{-
What we're saying here is that for any two natural numbers, we can *decide* whether or not they are equal, by either providing a proof of the statement or by proving it's impossible.

To compare two natural numbers we need to inspect them. "zero zero" is our easy case: they're obviously the same. In our "zero (suc n)" / "(suc m) zero" cases, we can also easily say they're obviously different using our absurd pattern. Our last case, "(suc m) (suc n)", is the interesting one. We don't know if they're distinct from their shape, but we also don't know if they're equal since m might not equal n.

We can solve this by using *with* to inspect m and n. This lets us see our two cases, where m≡n and thus we can say that our answer is yes, they're equal by cong suc, and where ¬[m≡n] and we can say no, they're not, by cong pred. For our no case, we could remove the mention of the assumption sucm≡sucn to rewrite just using function composition:
... | no ¬[m≡n] = no (¬[m≡n] ∘′ (cong pred))
-}


-- Next we can have a look at proving evenness.
variable m n p : ℕ

data Even : ℕ -> Set
data Odd  : ℕ -> Set

data Even where
    zero : Even zero
    suc  : Odd n -> Even (suc n)

data Odd where
    suc : Even n -> Odd (suc n)

_ : Odd (suc (suc (suc (suc (suc (zero))))))
_ = (suc (suc (suc (suc (suc (zero))))))
{-
NB we are here using syntax that allows us to declare our types together and then define them afterwards (useful here since the types refer to each other).

As we can see, we can use our constructors for Even and Odd to just prove the property of a number by the exact shape of the number, but this is going to get extremely annoying extremely quickly, so it would be nice to have a way to prove a number's evenness/oddness quickly.
-}
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
For even?, we can either say that zero is even, or that a nonzero number is even when its predecessor is odd, and is not even otherwise.

For odd?, we can either say that zero is obviously not odd with our absurd pattern (since we have no constructor for it), or that a nonzero number is odd when its predecessor is even, and is not odd otherwise.

So we have successfully proved these, but they're not the most satisfactory proofs in the world: this is essentially a partition of the natural numbers, and so when we get a proof of ¬ Odd, it would be nicer to get a positive proof of Even.
-}
evenOrOdd : ∀ n -> Even n ⊎ Odd n
evenOrOdd zero = inj₁ zero
evenOrOdd (suc n) with evenOrOdd n
... | inj₁ evenn = inj₂ (suc evenn)
... | inj₂ oddn  = inj₁ (suc oddn)


{-
Now we can start to look at *finding a witness*, aka the Markov Principle.
-}
open import Data.Product.Base using (∃)

{-# TERMINATING #-}
markov : {P : ℕ -> Set} ->     -- for some predicate P on nats
         (∀ n -> Dec (P n)) -> -- where p is decidable
         ¬ (∀ n -> ¬ (P n)) -> -- we know it's not untrue of all nats
         ∃ P                   -- so we can find a nat where it's true
markov {P} p? ¬∀¬ = loop 0 where
    loop : ℕ -> ∃ P
    loop i with p? i
    ... | yes pi = i , pi
    ... | no ¬pi = loop (suc i)
{-
What we're saying here is that, given some predicate P, if we know that P is decidable *and* that it is not untrue of all nats, then there must be some good input we can find.

We start with markov p? ¬A¬, where p? : "(n : N) -> Dec (P n)" and ¬A¬ : "((n : ℕ) → P n → ⊥) → ⊥". ¬A¬ looks a little scary, but what we're saying is "the statement that P applied to n is always false is itself not true". Our goal is now ∃ P: find a proof that there is an n such that P (ie "∃ (\ n -> P n)").

We can start looking through values using a loop. At each stage, if p applied to our i is true, then we're done: otherwise, we need to keep going. However, Agda is now going to point something out to us: Agda's termination checking *cannot tell that this will terminate*. We as humans can see that it will, since we know P cannot be untrue for all nats, so we *will* find one eventually. However, we cannot *prove* this to Agda (as we only have negative information, not positive), but we can just *tell* it that it will terminate using the TERMINATING flag.
-}
