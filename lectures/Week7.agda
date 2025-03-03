module Week7 where

---------------------------------------------------------------------------
-- Monoids
---------------------------------------------------------------------------

-- Remember monoids? A monoid is a set, together with a binary
-- operation on it, which has a unit, and which satisfies the axiom of
-- associativity -- that is, "brackets are not needed".

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)

-- define monoid as a record
record Monoid : Set₁ where
  -- Type and operations
  field
    Carrier : Set
    _<>_    : Carrier → Carrier → Carrier
    mempty  : Carrier

  -- and their properties
  field
    <>-assoc  : ∀ x y z → ((x <> y) <> z) ≡ (x <> (y <> z))
    <>-mempty : ∀ x → (x <> mempty) ≡ x
    mempty-<> : ∀ x → (mempty <> x) ≡ x

    -- <>-comm : ∀ x y → (x <> y) ≡ (y <> x)

-- Your favourite example of a monoid


data List (X : Set) : Set where
  [] : List X
  _,-_ : X -> List X -> List X

_++_ : forall {X} -> List X -> List X -> List X
[] ++ ys = ys
(x ,- xs) ++ ys = x ,- (xs ++ ys)

open import Function.Base using (id; _∘′_)

foldr : ∀ {X Y : Set} → (X → Y → Y) → List X → Y → Y
foldr c []        = id
foldr c (x ,- xs) = c x ∘′ foldr c xs

foldl : ∀ {X Y : Set} → Y → (Y → X → Y) → List X → Y
foldl acc c [] = acc
foldl acc c (x ,- xs) = foldl (c acc x) c xs

module _ where

  open Monoid

  List-Monoid : Set -> Monoid
  List-Monoid X .Carrier = List X
  List-Monoid X ._<>_ xs ys = xs ++ ys
  List-Monoid X .mempty = []
  List-Monoid X .<>-assoc [] ys zs = refl
  List-Monoid X .<>-assoc (x ,- xs) ys zs =
    cong (x ,-_) (List-Monoid X .<>-assoc xs ys zs)
  List-Monoid X .<>-mempty [] = refl
  List-Monoid X .<>-mempty (x ,- xs) =
    cong (x ,-_) (List-Monoid X .<>-mempty xs)
  List-Monoid X .mempty-<> xs = refl

  Endo-Monoid : Set → Monoid
  Endo-Monoid X = record
             { Carrier   = X → X
             ; _<>_      = _∘′_
             ; mempty    = id
             ; <>-assoc  = λ _ _ _ → refl
             ; <>-mempty = λ _ → refl
             ; mempty-<> = λ _ → refl
             }


---------------------------------------------------------------------------
-- Parametrised proofs
---------------------------------------------------------------------------

-- Parametrised module
module MonProofs (Mon : Monoid) where

  -- puts the operations and axioms in scope
  open Monoid Mon renaming (Carrier to M)


  -- We can "squish together" all the elements in a list
  squish : List M → M
  squish xs = foldr _<>_ xs mempty

  -- And squishing works in any left-right respecting order
  -- For instance:

  squish-++ : ∀ {xs ys} → squish (xs ++ ys) ≡ (squish xs <> squish ys)
  squish-++ {[]} {ys} = sym (mempty-<> (squish ys))
  squish-++ {x ,- xs} {ys} rewrite squish-++ {xs} {ys}
    = sym (<>-assoc x (squish xs) (squish ys))

  -- 1 ,- (2 ,- (3 ,- (4 ,- [])))
  -- 1 <> (2 <> (3 <> (4 <> mempty))) -- foldr

  --               1 ,- (2 ,- (3 ,- (4 ,- [])))
  -- ((((mempty <> 1) <> 2) <> 3) <> 4)

  squish' : List M → M
  squish' = foldl mempty _<>_

  squish'-correct : ∀ xs → squish xs ≡ squish' xs
  squish'-correct = {!!}


---------------------------------------------------------------------------
-- Homomorphisms
---------------------------------------------------------------------------


  -- define Monoid Homomorphisms
  -- prove they commute with squishing
