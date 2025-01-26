-- These are the annotated notes which include more detail about what the code is doing.

-- Looking back, one solution to our problem with the "head" function is to just define a new data type for a list that can't be empty.

-- Instead of our previous list:
data List (X : Set) : Set where
    []   : List X
    _,-_ : X -> List X -> List X

-- We can have a non-empty list, defined using the generic List, which only has a cons constructor.
data NonEmptyList (X : Set) : Set where
    _,-_ : (x : X) (xs : List X) -> NonEmptyList X

-- And we can also declare some variables - this lets us skip having to include {X : Set} in our method definitions.
variable
    X  : Set
    xs : List X

-- So now we have a head function with no issues!
nonEmptyHead : NonEmptyList X -> X
nonEmptyHead (x ,- xs) = x


{-
However, this doesn't fix our issues with zap. We can still have "raggedy" cases arising, since we aren't guaranteeing that the lists are the same length. NonEmptyList is only useful when we care about the head and nothing else.

To solve this, we need a list that codifies the length of the list as part of it: morally, we want something that tells us how many conses ,- there are in the list (remember that a 1-element list ["hello"] is actually "hello" ,- []). For this, we need to start by encoding our natural numbers. We can say that every natural number is either zero, or a successor of another natural number.
-}
data Nat : Set where
    zero : Nat
    suc  : Nat -> Nat

variable
    m n p : Nat

-- And now we can define our length-specified list.
data ListN (X : Set) : Nat -> Set where
    []   : ListN X zero
    _,-_ : (x : X) (xs : ListN X n) -> ListN X (suc n)
{-
Breaking this down, we still define the type of elements in the list (X : Set). But now, instead of defining a type for our data structure, we're generating a *family of types*: one for each natural number. In essence, our types are "length-zero list", "length-one list", "length-two list" and so on.
We then have our two cases. The empty list [] has length zero. The non-empty list contains an element of type X (the head), a list xs of length n (the tail), and a length of (suc n), ie n + 1.
-}


-- This gives us another safe version of head.
headN : ListN X (suc n) -> X
headN (x ,- xs) = x
{-
Originally, we were trying to promise "if you give me any list, I'll give you a value", but that's actually too much to promise. We now have a way to express our actual promise, which is "if you give me a non-empty list, I'll give you a value". We can do this by specifying that the length value of our ListN just has to be a successor of something - ie, that our list has at least one element.
-}


-- We also have a safe zap!
zapN : {T U : Set} -> ListN (T -> U) n -> ListN T n -> ListN U n
zapN [] []               = []
zapN (f ,- fs) (t ,- ts) = (f t) ,- zapN fs ts
{-
By specifying that the lists that we're zapping *must* be the same length, we can discard our annoying "raggedy" list cases. We will also know the length of our output list - the same as the inputs. This is one example of how Agda's strict typing can end up giving us more information about the data we're working with.
-}


-- We can define append for ListN as well. We will need an understanding of *addition* for natural numbers for this.
_+N_ : Nat -> Nat -> Nat
zero  +N m = m  
suc n +N m = suc (n +N m)

appendN : ListN X n -> ListN X m -> ListN X (n +N m)
appendN [] ys = ys  
appendN (x ,- xs) ys = x ,- appendN xs ys
{-
Note that here, because we've defined our addition function as being "left to right", so to speak, our definition of the length of our output list has to give the list lengths in "left to right" order - if we give our output's type as "List X (m +N n)" Agda will get mad, because it doesn't know that n+m == m+n (since the definition of our addition function is not symmetric: it works by taking the first argument apart).
-}


{-
When we want an output that has multiple pieces of data in it (possibly of different types), we need to define a data structure for this. This concept is called *pairing*.

Here, we can define a record we can use to store information. The syntax is a little different, but it's still conveying the same information. We have two elements, which may be different types. Our constructor _,_ shows how we define a record, and our fields fst and snd are how we access the values.

This is equivalent to the following CS316-style Haskell definition
data Pair a b = MkPair
  { fst :: a
  , snd :: b
  }
except that the constructor is called _,_ rather than MkPair.
-}
record _×_ (A B : Set) : Set where
    constructor _,_
    field
        fst : A
        snd : B

_ : Nat × List Nat
_ = zero , []

-- We can now a split a list of length m+n into two lists of lengths m and n respectively.
splitN : ListN X (m +N n) -> ListN X m × ListN X n
splitN {m = zero} xs = [] , xs
splitN {m = suc m} (x ,- xs)
    = let (pref , suff) = splitN xs
      in (x ,- pref) , suff

{-
This is a little complicated, but we can step through it slowly to understand. Our type signature indicates that we're turning one ListN into a record containing two ListNs. We then have two cases to consider.

This function works recursively. Plainly, we're taking elements off the start of the list until we have m elements, which we assemble into the first list in our record, and then putting the remainder in the second list. Thus, we'll have a base case and a recursive case. We can syntactically distinguish these using the same implicit notation as before {m = zero} and {m = suc m}.

In our base case, m is zero. Plainly, this means we're done taking elements off for the first list in our output. In terms of Agda, this means the shape of the goal is *ListN X zero × ListN X n*. Thus, we return an empty list which the other elements will be consed to to create our first record value, and return the remainder of the list as the second record value.

In our recursive case, m is a successor (ie not zero). Plainly, this means we still have more elements to take off the list. In terms of Agda, this means the shape of the goal is *ListN X (suc m) × ListN X n*. We can case split on xs and now see with C-c C-. that we have a few things in scope: {m : Nat}, {x : X}, and {xs : ListN X (m +N n)}. We know that we want to grab x: since m is still a successor, we need at least one more element. This means the shape of our goal is now (x ,_ ?) , ?. This is where we need to perform our recursive call, to fill in those question marks.

We now call splitN again on just the xs, naming the outputs of that call (pref , suff), then return x consed to pref, paired with suff left unchanged. In this way, we will recursively call all the way down until m is no longer a suc and is now 0, hit our base case, construct the first element in our record and return ListN X m × ListN X n.

It may be clearer to understand if the arguments that are implicit in the above definition are made explicit, as below:
-}

splitNExplicit : ListN X (m +N n) -> ListN X m × ListN X n
splitNExplicit {m = zero} xs = [] , xs
splitNExplicit {m = suc m} (x ,- xs)
    = let (pref , suff) = splitN {m = m} xs in
        (x ,- pref) , suff

{-
This allows us to see more explicitly what Agda infers for us - that with each recursive call, the value of m is decreasing by 1 (changing from {m = suc m} to {m = m}). Thus the recursive call will continue until m = 0, run the base case, and produce our final result.
-}
