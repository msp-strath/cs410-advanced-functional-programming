-- These are the annotated notes which include more detail about what the code is doing.

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_)

{-
Last time we looked at subst, aka Leibniz equality, which lets us substitute values that are equal for each other. Now we can try to prove some of our equality properties in terms of subst rather than refl. Our implicit claim is that anything we want to state about equality, we can do just with subst.
-}


-- Let's start with symmetry.
sym : {X : Set} -> {x y : X} -> x ≡ y -> y ≡ x
sym {x = x} x≡y = subst (\ z -> z ≡ x) x≡y refl
{-
Syntax note: \ is the same as λ, it indicates the start of an anonymous function.

If we wanted to prove this with refl, we just pattern match on p and see that our goal is easy. But we want to try and prove this with subst instead. We can start with sym p = { subst } and use C-u C-u C-c C-. to normalise and view subst relative to our goal. Our relevant bit is the last part of it: x ≡ y -> P x ≡ P y. If we can prove x equals y, any property that holds of x, holds of y.

Thus we need two arguments to subst - a predicate to prove of x, plus a proof that x ≡ y. This is the hard part: what predicate do we choose? In essence, this is the key challenge of using subst for proofs.

If we hand over subst ? x≡y, and check subst again, we can see that we now have ?3 x -> ?3 y. In other words, if we can come up with a predicate we can prove for x, then we can also prove it for y. This is a much less scary goal, and crucially, it gives us a clue about what predicate we want. We need something that a) is true for x and b) when is instantiated for y, gives us what we want. Looking at our goal, clearly we want a proof that something is equal to x! For this we will need to quickly bring x into scope on the left hand side, and then we have a very simple predicate.

Once we arrive at "sym {x = x} p = {subst (\ z -> ≡ x) p}", we can normalise and check one more time, and see that we now have "x ≡ x -> y ≡ x". Our last thing to do is to add one more argument, namely that x ≡ x, which we can prove with refl. And we're done!

Thinking broadly, when trying to prove using subst, we want to abstract away everything *except* the goal. When trying to work out what predicate to use, we want to look at the goal and see what we're trying to capture. Here, we want to turn ys into xs, so that's what we want to capture with our lambda.
-}


-- Let's see transitivity next.
trans : {X : Set} -> {x y z : X} -> x ≡ y -> y ≡ z -> x ≡ z
trans {x = x} {y} {z} x≡y y≡z = subst (\ y -> y ≡ z -> x ≡ z) x≡y (\ r -> r) y≡z
{-
Here we have two possible equalities we could try working with, x ≡ y and y ≡ z. For simplicity's sake, we'll start with the first one, {subst ? x≡y}. This gets us to a similar status as before: we now have ?3 x -> ?3 y. Our goal is x ≡ z, and looking at our type signature we can see that means that, since we're using x≡y, our subst goal should now be the rest of our type, namely y ≡ z -> x ≡ z. So we can try copying that right in, {subst (\ y -> y ≡ z -> x ≡ z) p}.

Now we have (x ≡ z -> x ≡ z) -> y ≡ z -> x ≡ z, so we can see that subst will need two more arguments to finish: one that proves (x ≡ z -> x ≡ z), and one that proves y ≡ z. These are both now fairly trivial: we can prove the first with (\ r -> r), and the second using y≡z.

A note - since y≡z is simply introduced on the left and then given on the right, we can actually omit writing it altogether if we want to. However, it can increase clarity to be explicit about it, so if you prefer to have it written out that's fine.
-}


-- We now want to generalise this slightly, by proving that propositional eq and Leibniz eq are equivalent.
infix 4 _≡ᴸ_

_≡ᴸ_ : {X : Set} (x y : X) -> Set₁
x ≡ᴸ y = (P : _ -> Set) -> P x -> P y
-- NB subscript and superscript can be typed with \_ and \^ respectively.

-- Let's start by turning propositional into Leibniz:
toLeibniz : ∀ {X : Set} {x y : X} -> x ≡ y -> x ≡ᴸ y
toLeibniz x≡y P px = subst P x≡y px
{-
Normalising the goal, we can see we are trying to prove (P : X -> Set) -> P x -> P y. (Again, this means we're proving anything that is true is about x, is true about y.) This looks an awful lot like the statement of subst. Let's start by introducing some predicate P and px : P x (representing the knowledge that that predicate is true for x). Now we need to prove P y. If we place "subst P x≡y" in the goal, we can see that we now have P x -> P y. We have a thing of type P x - it's px! So add that at the end, and we're done.

Leibniz equality essentially says "the equality that does what subst does", so it's fairly obvious that we just need to follow through the steps of subst to prove it.
-}

-- And now the other way:
fromLeibniz : ∀ {X : Set} {x y : X} -> x ≡ᴸ y -> x ≡ y
fromLeibniz {x = x} x≡ᴸy = x≡ᴸy (\ y -> x ≡ y) refl
{-
Normalising this, we can see we now *have* (P : X -> Set) -> P x -> P y. This is very useful, as this P will let us prove all sorts of things. Here, we have a problem that's talking in terms of y, so we literally just take a y and ask it to prove x ≡ y (we need to bring x into scope for this). Now we have x ≡ x -> x ≡ y, so adding a simple refl to the end gets us there.

It's important here not to overthink. We could spend forever stressing about "how do I choose P?", but we are allowed to look at our goal. Make P whatever will get us to the goal - here, that taking a y shows x ≡ y!
-}


{-
We now have a slight change of scene, as we start looking at the Curry-Howard principle. This allows us to use Agda's type system to form and then prove statements, by applying deduction steps. The trick is that these deduction steps are just functions we can use. Remember - functions, programs and proofs are really all the same.

Earlier, we struggled to prove (n + 1) ≡ (1 + n), and had to prove it by induction (by taking n apart). We also *failed* to prove 17 ≡ 42, as it's clearly not true.

Now we want to look at finding a way to different between failing to prove and *disproving*, ie proving false. This is the difference between saying "I can't find a proof that 17 ≡ 42 is true" and saying "I can find proof that 17 ≡ 42 is *not* true". We are now proving that a proof *doesn't exist*, not just that we aren't looking at it.

In order to define what it means for something to be false, we need a new type - the empty type. Since we're expressing what it means to be empty, this type should have no constructors.
-}
data ⊥ : Set where


-- Now we can express that 17 ≡ 42 is nonsense.
_ : 17 ≡ 42 -> ⊥
_ = \ ()
{-
The () is what we call the "absurd pattern" - it indicates that there are no valid arguments for this constructor. Essentially it is an impossible pattern - here, it encodes a statement that there is no way to construct 17 ≡ 42. Since there is no way to build the empty type, then a proof of 17 ≡ 42 -> ⊥ means that something has gone wrong if we are able to get a value out of this function. We can think of () as a counterpart to refl: where refl gives trivial equality, () gives trivial emptiness.
-}

-- We can see another, more pedestrian way to do this:
0≠1 : 0 ≡ 1 → ⊥
0≠1 = \ p → subst P p 7
  where
    P : ℕ → Set
    P 0 = ℕ -- something inhabited
    P 1 = ⊥ -- something empty
    P n = ℕ -- anything
{-
Rather than just throwing stuff away, we can now prove that this is not true by demonstrating that we can write a function that can tell 0 apart from 1. If a deterministic function returns two different outputs on two given inputs, clearly those inputs are not the same.

Here, our function P just takes a natural number and returns a set. For P 0, we return the natural numbers, but for P 1 we return ⊥. Thus clearly 0 and 1 are not equal.
-}


{-
If we have a proof of the empty type, then we can do whatever we like. We can think of this as arriving at a proof of false in natural logic - clearly it cannot be the case, so we are allowed to assume whatever we like because it is not possible.

In Agda, this is a very useful property as it allows us to implement *explosion* - a way of discarding "dead" branches that are impossible to reach. Essentially, we can use a proof of ⊥ to say that the branch has whatever type we want, because we know the branch will never actually be reached.
-}
explosion : ⊥ -> {A : Set} -> A
explosion ()
{-
If we bind our proof of ⊥, Agda will instantly be able to recognise when we case split that we are looking for our absurd pattern. Essentially, instead of specifying what our *output* should be, we're explaining why our *input* is impossible: because the input is impossible, Agda doesn't have to bother producing A. We can think of this as a normal function that takes every possible input and produces an output - it just so happens that there are no inputs.
-}


-- Let's prove inequality between something more complex:
broken : _+_ ≡ _*_ -> ⊥
broken eq = 0≠1 (sym (cong (\ f -> f 1 0) eq))
{-
Agda can neither disprove it nor find a way to solve it on its own: it's just too complex. However, from our perspective, we just need to find a way to reduce our inputs down into a specific impossible case. So, we choose to prove that 0+1 ≠ 0*1, which is a concrete case that Agda can evaluate. We do this by applying congruence and specifying a function from ℕ -> ℕ -> ℕ, which can be either our + or our *. Agda will then realise that these produce different outputs when fed 1 and 0, and thus we arrive at a proof of ⊥ - it is false.

Broadly, we can think of disproving as finding a specific observation that pushes things apart. Coming up with the case that will demonstrate inequality can take a bit of thinking. Agda can come up with these test for telling different constructors of the same datatype apart, but not much more than that. Here, we've refined a problem of reasoning about some functions to telling that zero and suc n are not the same constructor.
-}


-- We can move on to looking at negation.
Not : Set -> Set
Not X = X -> ⊥
{-
The negation of any X is a function from X to the empty type. Since a function is a promise to give back an answer, then clearly we can see here that we cannot return ⊥, so there'd better be no such thing as X. Essentially, "Not X" claims that X is an uninhabited type.
-}

-- We can demonstrate this simply by proving Not ⊥ (not false).
_ : Not ⊥
_ = \ x -> x
-- This is a function from ⊥ -> ⊥, and luckily, we know one - id.


-- Something more interesting: double negation introduction.
dni : {X : Set} -> X -> Not (Not X)
dni x notx = notx x
{-
This says "if we have proof of an X, we should be able to prove that Not X is false". Here, we pull the internal Not X out of the type and make it an argument. Now we can feed our proof of x into the "function" of Not X, and thus produce the empty type. It may help to think about what this typeline is really saying: since Not X is a function, this really says:
dni : {X : Set} -> X -> (X -> ⊥) -> ⊥
which is more obviously provable, as the absurdity of having both X and X -> ⊥ is clear in the type.
-}


-- The trickier one is the counterpart, double negation elimination.
dne : {X : Set} -> Not (Not X) -> X
dne notnotx = {!   !}
{-
This says "if the absence of something is unthinkable, then we know how to make it". For booleans (eg when thinking about circuits) this is clearly true. Here, where we don't know what our type is, it's not so obvious. We don't know if X is inhabited or not, so we have two possible strategies and we don't know which one to pursue. If X were inhabited, we'd just give it back, and if X *isn't* inhabited, we have (⊥ -> ⊥) -> ⊥, which is easy. The problem is, we don't know which one we have, so we currently have no hope of implementing this.
-}
