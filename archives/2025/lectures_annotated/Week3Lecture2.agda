-- These are the annotated notes which include more detail about what the code is doing.

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_)

data ⊥ : Set where

Not : Set -> Set
Not X = X -> ⊥

explosion : ⊥ -> {A : Set} -> A
explosion ()

dni : {X : Set} -> X -> Not (Not X)
dni x notx = notx x


-- Now that we have a definition of negation, we can also define implication.
Implies : Set -> Set -> Set
Implies A B = A -> B
{-
All this says is that we have two sets. One might imply the other A -> B, and the return type of this function is whether that implication is true or not. In other words, if Implies A B is true, we are saying that given evidence for A, we can produce evidence for B.

For example, we can see when an implication does not exist:
-}
_ : Not (Implies (0 ≡ 0) ⊥)
_ = dni refl
{-
Here we can see that clearly (0 ≡ 0) does not imply ⊥. We have evidence for 0 ≡ 0 - it's provable by refl - but no evidence for ⊥ as it is not possible to have evidence of false. Thus (0 ≡ 0) -> ⊥ is clearly absurd. We can also see this as a broader example:
-}
_ : Not (Implies ℕ ⊥)
_ = dni 0
{-
We don't normally think of ℕ as a proposition but here we can think of it as a proposition with many proofs. 0 is an acceptable proof that ℕ is true, but so is 1, or 7, or 52.
-}


-- Next up we have conjunction, aka ∧ (\and).
record And (A B : Set) : Set where
    constructor _,_
    field
        fst : A
        snd : B
{-
We can think of And A B as being evidence for the conjunction of A and B. In order to construct a proof of A ∧ B, we need two pieces of information, a proof of A and a proof of B.
-}

-- We can use this to define various useful properties, starting with diagonal:
diagonal : ∀ {A} -> A -> And A A
diagonal prfA = prfA , prfA
{-
This is very simply saying that if we have proof of A, we have proof of A ∧ A. We can construct this evidence using our constructor _,_ and giving a proof of left and right - these proofs are both simply our proof of A.
-}

-- We can also demonstrate that the fields in ∧ can be swapped:
swap : ∀ {A B} -> And A B -> And B A
swap (prfA , prfB) = prfB , prfA
-- Very simply we just split our original And in two and then reassemble.

{-
We can achieve the same goal by projecting out. Note we need to open And first, as unlike Haskell, the projection functions for a record type are not automatically in scope. This means we can reuse the same names for different types (eg we could have another record type with fst and snd and as long as we did not try to open that as well we would not have a problem).
-}
open And

swapAgain : ∀ {A B} -> And A B -> And B A
swapAgain prfAB = snd prfAB , fst prfAB
-- Now instead of explicitly taking prfAB apart into (prfA , prfB), we can grab the individual elements out using the field projections fst and snd.

-- This also gives us another way to prove NotImplies.
NotImplies : Set -> Set -> Set
NotImplies A B = And A (Not B)
{-
If we think of implication as saying "when A is true, B must be true", then a pair (A ∧ Not B) refutes implication. Thus if we can produce (A ∧ Not B) from our inputs, we have demonstrated there is no implication.
-}
_ : NotImplies (0 ≡ 0) ⊥
_ = refl , (\ x -> x)


-- Now we can move onto disjunction, aka ∨ (\or).
data Or (A B : Set) : Set where
    inl : A -> Or A B
    inr : B -> Or A B
{-
Now rather than a datatype with one constructor which takes two arguments, we have a datatype with two constructors which each take one argument. Thus, we have two possible ways to construct a proof of A ∨ B - either by providing proof of A or providing proof of B.
-}

-- We can distribute or across and:
distribute : ∀ {A B C} -> And A (Or B C) -> Or (And A B) (And A C)
distribute (a , inl b) = inl (a , b)
distribute (a , inr c) = inr (a , c)
{-
This says "if we have proof of A, and we also have proof of either B or C, then we either have proof of A and B, or we have proof of A and C". Intuitively we can see this to be true, and Agda allows us to say this fairly simply. We start with distribute (a , borc), and then case split on borc to give us our two cases: inl, where we have proof of b, and inr, where we have proof of c. Then we can easily construct one of our two output cases.
-}


-- The last thing we're missing is a definition of truth, aka ⊤ (\top):
record ⊤ : Set where
    constructor tt
{-
In contrast to ⊥, which has no constructors and so is impossible to build, ⊤ has a constructor which takes no arguments and is thus always possible to build. We can use any inhabited type as a truth - eg ℕ - but the record with no fields is the canonical one. It's very easy to give all the fields of a record with no fields! In fact, there's a few different ways to do it.
-}
_ : ⊤
_ = record {}

_ : ⊤
_ = tt

_ : ⊤
_ = _
{-
In the last case using _, because there is exactly one inhabitant of ⊤, Agda can work out which one we want. In contrast:
_ : ℕ
_ = _
-- will not work, as there are too many natural numbers to choose from and Agda doesn't know which one we want.
-}


{-
Now we have the full set of features required to talk about classical logic - truth, negation, conjunction, disjunction and implication - we can look at the law of excluded middle.
-}
LEM : Set₁
LEM = (B : Set) -> Or B (Not B)
{-
To B or not to B, that is the question - whether 'tis nobler in the mind for B to be false or true, the law of excluded middle guarantees that for some proposition B, it is either true or not true.
-}
lem : LEM
lem B = {!   !}
{-
So. How do we actually do this? We don't know anything about B at all, so we actually have no idea whether to go left or right. We don't even know if B has a proof at all - it could encode an undecidable proposition, like the halting problem!
-}


{-
Once again, we have arrived at a situation where we cannot prove a property because we don't know enough about our input to know which strategy to take. This is the same issue we ran into with double negation elimination. We can actually use these to prove each other... *kind of*.

We start by making a type DNE which encodes double negation elimination, in a similar format to our type LEM above:
-}
DNE : Set₁
DNE = (B : Set) → Not (Not B) → B

-- And now we are able to prove that LEM implies DNE:
open import Function.Base using (case_of_)

lem⇒dne : LEM -> DNE
lem⇒dne lem B notnotb = case lem B of λ where
    (inl b)    → b
    (inr notb) → explosion (notnotb notb)
{-
We have lem : LEM, B : Set, notnotb, a proof of Not (Not B), and our goal is B. Intuitively, we can now see which way to go. LEM asks us to either prove B, or prove Not B. But we have a proof that Not B is false in notnotb, so we can dismiss that branch and go left, proving B.

We are using a bit of bonus technology here in case_of_. This lets us explicitly ask which version of B we have (B or Not B), which changes our goal to Or B (Not B) -> B. We can then use our pattern-matching lambda λ to split on our cases, and provide proofs of both.
-}

-- We can likewise prove the implication in the other direction:
dne⇒lem : DNE -> LEM
dne⇒lem dne B = dne (Or B (Not B)) f
  where
    f : (Or B (B → ⊥) → ⊥) → ⊥
    f not-[b-or-notb] = not-[b-or-notb] (inr \ b -> not-[b-or-notb] (inl b))
{-
Now we're in the same situation as before, but this time we have more information: dne tells us that we can prove some b *if* we can prove its double negation, notnotb. This lets us make some progress! We start by introducing some f with the type we want in a where clause. f receives our argument not-[b-or-notb].

We then do something clever. Essentially, any time we have an assumption that something is false, this gives us some ability: at any point, we can say that we would rather be proving whatever it is that is negated. Here, we can decide partway through to start proving b-or-notb, rather than not-[b-or-notb]. Because we know that thing is false, if we can prove it true, then we have a contradiction and we're done.

We might look like we're now back at the start, but we have actually made some progress. Our goal is once again Or B (Not B), but now we have an additional fact - namely, that b-or-notb is false. We choose to go right and prove Not B, as this will give us a B. We can then supply that B as an argument to not-[b-or-notb] to get a proof of false, and we're done.

What we need to bear in mind is that we've not implemented either DNE or LEM here: we've proven that they imply each other, and thus that we can't implement either of them (because if we could, we could solve the halting problem and make a lot of money on the Millenium Prize).
-}


{-
All of this might seem a bit strange, because we know from our work in CS106 that law of excluded middle *is* possible and does exist. However, what we need to bear in mind is that in that class we looked at excluded middle *for the booleans*, whereas here we are attempting to reason about any abstract type.

Thus, it stands to reason that some types can have LEM & DNE, whilst some types cannot. We want to encode this property, which we call *decidability*. If a type is decidable, then we can use classical reasoning with it.
-}
Dec : Set -> Set
Dec B = Or B (Not B)
{-
Very simply, we say a type B is decidable precisely when we have either B or Not B. This is, conveniently, the law of excluded middle, and so if a type is decidable then clearly we can implement LEM (and thus DNE) for that type.
-}
