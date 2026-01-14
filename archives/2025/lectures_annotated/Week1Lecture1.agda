-- These are the annotated notes which include more detail about what the code is doing.

-- We can start by building one of our simplest data types, a List.
data List (X : Set) : Set where
    []   : List X
    _,-_ : X -> List X -> List X
{-
This is the shape of a standard data declaration in Agda. Like in Haskell, the first line defines the *type* of the data structure (note Agda uses only one colon : for type). Here, we're defining a Set, where the elements being stored - X - are themselves a Set.
We then need to give our constructors. A List has two constructors. The empty list [] is just a List. The cons operator ,- which joins a head and tail takes an X (the head) and a List X (the tail) and combines them into a List X.
Notably, the underscores _ represent our values being consed together, with ,- as an operator being used *infix* between the values.
-}


-- Now we can have a go at append, which should join two lists together.
append : {X : Set} -> List X -> List X -> List X
append [] ys        = ys
append (x ,- xs) ys = x ,- append xs ys
{-
This is the shape of a standard function declaration in Agda. Again, the first line defines the type. Notably, here we include an *implicit* argument in the form of {X : Set}. This is not an explicit value we intend to use, but rather a statement about the type of all Xs.
We started our implementation by typing 'append = ?'. Then when we C-c C-l, Agda replaces the ? with a hole. We then work with the hole to produce our actual definition. We started by adding our arguments (xs and ys), and we can then use C-c C-c set up our cases. At that point, we then have two holes that Agda can have a guess at filling, using C-c C-a with -l and -s arguments to select the solution we want.
-}


-- Next is zap (Zipping APplication).
zap : {T U : Set} -> List (T -> U) -> List T -> List U
zap [] []               = [] 
zap [] (t ,- ts)        = []
zap (f ,- fs) []        = []
zap (f ,- fs) (t ,- ts) = f t ,- zap fs ts
{-
As a reminder, this function says "assuming T and U are both sets, if you give me a list of functions T -> U and a list of Ts, I can give you a list of Us".

Our cases here are:
1   - Our lists are both empty
2/3 - Our lists are "raggedy", ie different lengths
4   - Our lists both have a value
In case 1, we want to return the empty list, and in case 4 we want to apply the function and keep going.
For cases 2 and 3, usually raggedy lists indicate something is wrong (eg we're zipping the wrong things together) and we would want a clearer response in these cases. However, it isn't possible with this version of List to do better than this. We'll come back to this later.
-}


-- We can also see a similar problem arising with tail and head.
-- Tail is pretty simple:
tail : {X : Set} -> List X -> List X
tail []        = []
tail (x ,- xs) = xs

-- But head is a little harder:
head : {X : Set} -> List X -> X
head = {!   !}
-- What is the head of an empty list? In Haskell, this would just crash, but in Agda that's not allowed. Clearly we need something better - that's for next time!
