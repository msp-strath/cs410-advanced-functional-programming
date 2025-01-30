-- These are the annotated notes which include more detail about what the code is doing.

-- Let's quickly import and define the things we had last time:
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Function.Base using (id; _∘′_)
open import Data.Vec.Base using (Vec; []; _∷_; zipWith; replicate)

data  _≡_ {X : Set} (a : X) : X -> Set where
    refl : a ≡ a

cong : {X Y : Set} -> (f : X -> Y) -> {x x' : X} -> (x ≡ x') -> (f x ≡ f x')
cong f refl = refl


-- Now we're going to have a look at the actual proof for our zipWith-replicate equivalence.
zipWith-replicate : 
    ∀ {X Y Z : Set} (f : X -> Y -> Z) x y n ->
    zipWith f (replicate n x) (replicate n y)
    ≡ replicate n (f x y)
zipWith-replicate f x y zero    = refl
zipWith-replicate f x y (suc n) = cong (f x y ∷_) (zipWith-replicate f x y n)
{-
Thinking about our "action replay" strategy, how did we get here? To start with, we know that we have four arguments: f, x, y and n. So what should we be looking at? We cannot refine by our zipWith definition, since zipWith needs to know what is at the head of both of its inputs. Its inputs are (replicate n x) and (replicate n y), and it's stuck on these because replicate is stuck on n (since its construction will vary depending on what n is). Clearly, n is what's causing the problems, so we start by case-splitting on n. This will get us to two cases, one where n is zero, and one where it is suc n.

Inspecting the goal where n is zero, we can now see that the goal is simply [] ≡ []. Clearly, this can be solved by refl, so for that goal we're done!

Our second goal looks a little more complicated. Once again, we have the same thing at the start on both sides (f x y ∷), and then the remainder of our goal looks like the theorem itself. Thinking about our previous tests with congruence, we can take a similar strategy here. Ultimately, if we keep recursing replicate, we'll get down to the base case eventually. Then we will once again have a list of function calls applied to some arguments, which we can prove are equal using congruence. Thus, all we need is cong (f x y ∷_) (the recursive call).

Note that we have a new syntactic trick here, which relies on us paying attention to whitespace. When using vectors, _∷_ is our cons constructor, but here we have (f x y ∷_). Note there is a space between the left argument and ∷, but not between the ∷ and the right argument. This is a partially applied constructor: we've given the first argument (it's the result of applying f to x and y), and are telling Agda to cons that to some second argument which we're letting it figure out - it will be the result of our recursive call to zipWith-replicate. This is the same as in Haskell when we give (1 +), meaning "the function that takes some argument x and returns 1 + x", ie \x -> 1 + x.

_∷_   : unapplied constructor
_ ∷_  : constructor with first arg (letting Agda guess at it)
_∷ _  : constructor with second arg (letting Agda guess at it)
_ ∷ _ : fully applied constructor (letting Agda guess at both)

Here, because the righthand argument has to be the thing that solves the equation, Agda can figure it out. The left underscore actually *has* to represent (f x y), so we could write it as _ ∷_ if we wanted to.
-}


{-
Some properties are much more difficult to prove than others. For example, we will struggle to prove associativity of append for vectors, even though we can see intuitively it is the case.
-}
open import Data.Vec.Base using (_++_)

vecAppendAssoc : {X : Set}{l m n : ℕ}
  (xs : Vec X l) (ys : Vec X m) (zs : Vec X n)
  -> ((xs ++ ys) ++ zs) ≡ {!(xs ++ (ys ++ zs)) !}
vecAppendAssoc xs ys zs = {!   !}
{-
Here, we don't even make it to the definition: just stating *what* we want to prove is a challenge. We can see that the right-hand side our ≡ in the type signature has the goal shape Vex X (l + m + n). This might seem fine, given we're trying to prove something of the shape (xs ++ (ys ++ zs)). However, we need to remember that (l + m + n) is *actually* ((l + m) + n) - left-to-right is default so the brackets are hidden, but to Agda they are still there. When working with zipWith, we didn't have an issue because our vectors were the same size, but now this is a problem.

One way to fix this would be by changing our definition of ≡:
data _≡_ {X : Set} (a : X) : {Y : Set} -> Y -> Set where
   refl : a ≡ a

Note that we have slightly relaxed our argument types: we no longer say explicitly that our second argument must be the same kind of Set as our first (although this will still need to practically be the case as the only way a ≡ a is if they are the same type). While this specific example is not relevant for the coursework, relaxing the definition of ≡ *may* be appropriate in some cases - generally, if you are working on something where you get a confusing error message even though the types seem to match, this may be the issue.
-}


-- We can now start to combine some proofs of equality, starting with symmetry:
sym : ∀ {X} {x y : X} -> x ≡ y -> y ≡ x
sym refl = refl
{-
As we'd expect, our type signature says "if x is equivalent to y, then y is equivalent to x".

Once again, we'll run through an action replay: we begin with sym x≡y = ?. Note here our spacing is *very* important. In the type signature, x ≡ y is a statement about the properties of x and y, but in the argument here, without spaces, it's merely an identifier. It can be useful when writing Agda to use *suggestive names*: this can help us remember what our big-picture goal is as we progress.

There's very little we can do here, since we don't know the types of x and y, so the only thing we can really do is case split on x≡y. Unsurprisingly, this gives us refl on the left, and the goal is now quite simply x ≡ x, which we can easily prove with refl once again.
-}


-- Next up is transitivity:
trans : ∀ {X} {x y z : X} -> x ≡ y -> y ≡ z -> x ≡ z
trans refl refl = refl
{-
As we'd expect, our type signature says "if x is eqivalent to y, and y is equivalent to z, then x is equivalent to z".

We start knowing x≡y and y≡z, and wanting to prove x≡z, so we have trans x≡y y≡z = ?, and our goal is x ≡ z. We have two arguments we can pattern-match on, but it doesn't actually matter which one we pick. For argument's sake, let's case-split on x≡y. This results in trans refl y≡z = ?. If we try mashing in the other one, that will work too, and we have two refls on the left! Our goal has now changed shape to x ≡ x, so a simple refine (C-c C-r) will finish us off.
-}


{-
A short interlude. The issue with all of this - and the reason  these incredibly long-winded notes with their action replay descriptions exist - is because Agda doesn't save any of this intermediary information, and just leaves us with an end product which is usually extremely difficult to read and understand.

However, Agda does *have* syntax that allows us to show our intermediate steps to an extent. (This is commented out as the imports clash with our local definitions of ≡ and refl. If you want to play with it, comment out the rest of this file, then uncomment this following chunk.)
-}
-- open import Relation.Binary.PropositionalEquality using
--   (_≡_; refl; module ≡-Reasoning)
-- open ≡-Reasoning

-- trans : {X : Set} {x y z : X} -> x ≡ y -> z ≡ y -> x ≡ z
-- trans {x = x} {y = y} {z = z} x≡y z≡y = begin
--     x ≡⟨ x≡y ⟩
--     y ≡⟨ z≡y ⟨
--     z ∎
{-
This makes more explicit the transitivity proof we just defined: you begin your proof, then step from x to y to z, each time showing your justification for the steps you are taking inside the ⟨ combinators ⟩ (\< and \>). We then use ∎ \qed to say that we are done.

Note that although this is unusual syntax, it's still fundamentally the same Agda: we can place goals in our brackets ⟨ ? ⟩ and Agda will tell us what we're looking for as we're used to. Also note that in our second step, we are using a proof that z≡y rather than y≡z. This is not a problem: we just flip our combinator to be moving in the opposite direction!
-}


{-
We can now create a function that encodes what it means for things to be equal on a more fundamental level than merely congruence/symmetry/associativity. This is substitution, the essence of equality, and it can be re-used to implement all of the other combinators. Formally, this is the proof that if two values are equal, any property true of one of them is true of the other. This is Leibniz equality, based on how we can *use* a value.
-}
subst :
    ∀ {X} (P : X -> Set) ->
    ∀ {x y : X} -> x ≡ y ->
    P x -> P y
subst P refl px = px
{-
As usual, let's break this down. First we have a predicate (a function) that, for any value of type X, will return a type. Then we have two values of type X, plus a proof that they are equal. Then, if we can prove P x, we have P y. We set this up as subst P x≡y px = ?.

By now we are used to the fact that the only thing we can split on is x≡y, so we do that, and Agda provides us with refl. Once again, our goal is now easy: we're looking for P x, so px is our answer.

Note that although we do not actually use P in the definition, we still state it explicitly as it is very difficult for Agda to infer and will usually need to be passed explicitly.
-}


-- This ability to subtitute can let us do some useful things, like casting types:
cast : ∀ {A m n} -> m ≡ n -> Vec A m -> Vec A n
cast {A} = subst (Vec A)
{-
Here, this is letting us show that two vectors are, in fact, the same length even if their types are not the same, as long as their types are equivalent. This is another example of using an equation we've proven to fix an annoying type mismatch (just like back when we were showing n + 1 ≡ 1 + n).
-}
  