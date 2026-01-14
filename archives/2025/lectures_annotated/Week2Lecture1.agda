-- These are the annotated notes which include more detail about what the code is doing.

{-
We're now going to start looking at how to define and use a useful property, *propositional equality* - the proof that two things are equivalent. This is very useful, eg proving an efficient function is equivalent to an inefficient function.

Because this is evidence of something, we are using a data structure. What we want is a setup such that "5 ≡ (3 + 2)" has an element, and "17 ≡ 42" does not. There's nothing that stops us from *asking* whether 17 ≡ 42, but the answer should be no. ≡ can be typed with \==
-}
data  _≡_ {X : Set} (a : X) : X -> Set where
    refl : a ≡ a
{-
Like with our (listN A), associating to each natural number a type of lists that have that length, this is generating a family of types. This time, we're saying that for a fixed type X, and for a fixed element a : X, there is a family of types associating to every value b of type X the type of proofs that a is equal to b.

Plainly, the question being asked by these types is: "what does it mean for some argument with type X to be the same as a?". This has quite a simple answer: the only thing that is equal to a is a itself. Thus, we simply have the "refl" (reflexivity) constructor: everything is equivalent only to itself.

It is worth noting that, in the type signature of data declarations, arguments belong to two classes:
1. On the *left of the colon* we have *parameters* whose scope ranges over the whole data definition and *must* be kept the same across all constructors.
2. On the *right of the colon* we have *indices* which can be different in each constructor.

In ListN, the type of elements A was a parameter and the length n was an index; specialised to 0 in the nil case and (suc n) in the cons one.

Here, we have two parameters (the type X and a of type X). The declaration of the unique constructor uses the parameter a straight away, and we can insist that the index of type X right of the colon is specialised into a.
-}


-- Let's try running some tests on this definition! For this, it will be helpful for us to have some functionality related to the natural numbers ℕ.
open import Data.Nat.Base using (ℕ; zero; suc; _+_)

-- Because we have _+_, Agda knows how to reduce (3 + 2) to 5, and our reflexivity property can then prove that these are equal.
test1 : 5 ≡ (3 + 2)
test1 = refl

-- But lest we think it just accepts anything, we *cannot* solve "17 ≡ 42" using refl, because we have no proof that these are the same.
test2 : 17 ≡ 42
test2 = {!  !}


{-
These tests are fairly simple. It can be useful to think about a slightly more complicated test. First, we should define *congruence*. This is the foundational principle of algebra: if you have an equation that is true, and then perform the same operation on both sides of the equation, the result is still true. In other words, if a ≡ b is true, then 2a ≡ 2b is also true.
-}
cong : {X Y : Set} -> (f : X -> Y) -> {x x' : X} -> (x ≡ x') -> (f x ≡ f x')
cong f refl = refl
{-
In order to understand this definition, it can be helpful to perform an "action replay" of how we constructed it, to see why this is the way it is. This is very often a useful strategy for understanding proofs after the fact (as they are often not easy to understand just from looking at the final product). If you like, try commenting out the line "cong f refl = refl" and following along with what's described here.

We start with our type signature. This is a long one, but it's less complicated than it looks. First, we set up the things we know or are being given: that X and Y are sets, that we have a function from X to Y, and x and x' are both Xs. Then we make our actual statement of congruence: since we have proof that x ≡ x', then f x ≡ f x'.

So, how do we proceed from here? Well, we need to take a function, so we can start with "cong f". We then need something else - specifically, to demonstrate x ≡ x'. However, since we're not sure what that actually is at this point, we can just put in a placeholder: "cong f p = ?". Using C-c C-. to inspect the hole, we can now see that the shape of p is x ≡ x'. It's also important to note that at this point, the shape of the goal is f x ≡ f x'.

Agda is actually smart enough to work p out by itself: the only way x ≡ x' is if x = x' (note the double-bar equals, rather than triple), which will allow us to substitute into x ≡ x. So, if we put p in our hole and case split with C-c C-c, Agda replaces p with refl straight away. From Agda's perspective, this gets rid of x' entirely. We are now able to talk about the problem *only* in terms of x. Notably, at this point, the shape of the goal has now changed: we are now looking to prove f x ≡ f x. This is clearly possible by refl, since we have exactly the same thing on both sides, so a quick C-c C-r will give us our answer! We should note that the two refls here are talking about different things: the refl on the left is a statement about x ≡ x', while the one on the right is a statement about f x ≡ f x'.

Congruence is an extremely useful property which we can make frequent use of. If we ever see the same stuff on both sides of something we're attempting to prove, it's usually worth trying cong - and if it's a constructor, then *definitely* try cong.
-}


-- Now that we understand congruence, we can look at a harder test - proving that (n + 1) ≡ (1 + n).
test3 : (n : ℕ) -> (n + 1) ≡ (1 + n)
test3 zero    = refl 
test3 (suc n) = cong suc (test3 n)
{-
To a human, this is obvious, but Agda runs into a problem here. Before, Agda could turn 3+2 into 5 via computation alone, and thus work out that 5 ≡ 3+2. However, because `_+_` is defined by induction on its first argument (you can always see the definition of a symbol by putting your cursor over it and "jumping to definition", aka M-. in emacs and F12 in VSCode), Agda will only make progress if the first argument to `_+_` starts with a constructor. And so Agda *cannot* make any progress in this case: when attempting to run (n + 1), the fact that n is only a mere variable immediately gets in the way.

It's important to remember when thinking about how this works that = and ≡ are *different types of equality*. = represents definitional equality: this is what makes Agda run your programs, by allowing it to substitute. In contrast, ≡ is only propositional equality - we might know these things are equivalent, but we can only use that information in a more limited way. refl is our way of telling Agda that it should be able to turn our ≡s into =s (and thus produce a solution) only using computation. Thus, refl is not enough on its own when computation is insufficient.

Clearly, we have to case split on n.

1. Base case: If it is 0, then our question is just 1 ≡ 1, which is easily solved with refl.

2. Step case: If it is nonzero i.e. of the form (suc n), then Agda will make a little bit of progress and evaluate (suc n + 1) into (suc (n + 1)). Meanwhile, the right hand side evaluates from (1 + suc n) into (suc (suc n)). Noticing that both sides start with `suc` and remembering that congruence will give us a proof that the same function applied to the same argument produces the same output, we can use `cong suc` to peel off both sides' leading suc. We are left with a goal stating that (n + 1) and (1 + n) are equal which is exactly what a recursive call to test3 on n will give us. We have performed our first proof by induction!

Thinking about an example, if our original value of n was 3, we will end up with a proof of (3 + 1) ≡ (1 + 3), given by (cong suc (cong suc (cong suc refl))): each recursive call adds a (cong suc) in front of the proof until we reach the base case 1 ≡ 1 proven by refl.
-}


{-
So far, we've been using propositional equality for some reasonably simple examples. But it can also be used to prove the equivalence of more complicated types. Now we're going to take a look at proving equivalence of *functions*. For this, we're going to need to import a few things.
-}
open import Function.Base using (id; _∘′_)
open import Data.Vec.Base using (Vec; []; _∷_; zipWith; replicate)
{-
Note that a Vec (Vector) is just the standard library name for the ListN we defined last week - it's a collection of elements of a codified length. _∷_ is the vector cons constructor (the equivalent to our constructor ,- for ListNs), and ∷ can be typed with \::. 
-}


{-
We're going to take a look at two functions, zipWith and replicate, and prove that it doesn't matter which way around we apply them: as long as we give the same arguments, we'll get the same results. For now, we're just going to look at the type signature: next time, we'll see how to actually prove this.
-}
zipWith-replicate : 
    ∀ {X Y Z : Set} (f : X -> Y -> Z) x y n ->
    zipWith f (replicate n x) (replicate n y)
    ≡ replicate n (f x y)
zipWith-replicate = {!   !}
{-
A note on ∀ (\forall): in Agda, ∀ {A} is syntactic sugar for {A : _}. Essentially, it's our way of telling Agda that it can work out the type of the things that come after it *based on how we use them*. We still have to specify the types of X, Y, Z and f explicitly, because Agda cannot work out their types from their usage. However, it *can* work out that x is an X, y is a Y and n is an ℕ, because of how they are used. (For instance, Agda can tell that n must be a natural number because it is later given as the first argument of replicate: the first argument of replicate must be a natural number, thus n : ℕ.)

As a reminder, zipWith takes a function X -> Y -> Z plus two lists of equal length, xs and ys, and produces a list of zs from them; replicate takes an element x and a natural number n and produces a list of length n where every element in the list is x.

What this definition is functionally saying is "if I have the value 3 and the value 2, it shouldn't matter whether I add those together to get 5 and then duplicate that ten times, or if I duplicate the 3 and 2 ten times and then add all those pairs together". Either way, we should clearly get a list of ten 5s.

Of course, this numeric addition is just an example: our inputs and function can be anything. This is subtle but significant, because in some languages, these two things actually will not always be equivalent. In OCaml, another functional language, functions can be *impure* - that is, they can take into account factors other than those we give them in their arguments/type signature.

For instance, we could have a function in OCaml which takes two inputs, but then ignores them and returns true or false based on whether it's currently Wednesday. In that case, using zipWith on a single pair of inputs at 5 seconds before midnight on Tuesday would give false, and if we then replicated that 100 times we would give a list of 100 falses. However, if we instead replicated the inputs 100 times, and started zipWithing them, we would run over into Wednesday and our function would start returning true. Despite giving the same function and the same arguments, our outputs would differ.

In contrast, Agda guarantees *pure* functions: functions are only allowed to take into account things explicitly given in the arguments/type signature. While this makes some functions harder to write, it also allows us to guarantee behaviour that other languages cannot. This is one of the payoffs of Agda's purity.
-}
