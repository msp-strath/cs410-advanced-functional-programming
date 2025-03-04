module Week7 where

---------------------------------------------------------------------------
-- Monoids
---------------------------------------------------------------------------

-- Remember monoids? A monoid is a set, together with a binary
-- operation on it, which has a unit, and which satisfies the axiom of
-- associativity -- that is, "brackets are not needed".

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; module ≡-Reasoning)

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
             ; <>-assoc  = λ _ _ _ → refl -- f ≡ (λ x → f x)
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

  squish-mempty : squish [] ≡ mempty
  squish-mempty = refl

  squish-++ : ∀ xs ys → squish (xs ++ ys) ≡ (squish xs <> squish ys)
  squish-++ [] ys = sym (mempty-<> (squish ys))
  squish-++ (x ,- xs) ys rewrite squish-++ xs ys
    = sym (<>-assoc x (squish xs) (squish ys))

  -- 1 ,- (2 ,- (3 ,- (4 ,- [])))
  -- 1 <> (2 <> (3 <> (4 <> mempty))) -- foldr

  --               1 ,- (2 ,- (3 ,- (4 ,- [])))
  -- ((((mempty <> 1) <> 2) <> 3) <> 4)

  squishAcc' : M → List M → M
  squishAcc' acc = foldl acc _<>_

  squish' : List M → M
  squish' = squishAcc' mempty

  open ≡-Reasoning

  squishAcc'-correct : ∀ acc xs → acc <> squish xs ≡ squishAcc' acc xs
  squishAcc'-correct acc []        = <>-mempty acc
  squishAcc'-correct acc (x ,- xs) =
    begin
      (acc <> squish (x ,- xs)) ≡⟨⟩
      (acc <> (x <> squish xs)) ≡⟨ <>-assoc acc x (squish xs) ⟨
      ((acc <> x) <> squish xs) ≡⟨ squishAcc'-correct (acc <> x) xs ⟩
      squishAcc' (acc <> x) xs  ≡⟨⟩
      squishAcc' acc (x ,- xs)
    ∎

  squish'-correct : ∀ xs → squish xs ≡ squish' xs
  squish'-correct xs = begin
    squish xs            ≡⟨ mempty-<> (squish xs) ⟨
    mempty <> squish xs  ≡⟨ squishAcc'-correct mempty xs ⟩
    squishAcc' mempty xs ≡⟨⟩
    squish' xs ∎


---------------------------------------------------------------------------
-- Homomorphisms
---------------------------------------------------------------------------

  -- define Monoid Homomorphisms
  -- prove they commute with squishing


record HomoMorphism (S T : Monoid) : Set where
  module S = Monoid S
  module T = Monoid T
  field
    function    : S.Carrier → T.Carrier
    mempty-resp : function S.mempty ≡ T.mempty
    <>-resp     : ∀ x y → function (x S.<> y) ≡ function x T.<> function y

HomoMorphism-List : (M : Monoid) → HomoMorphism (List-Monoid (Monoid.Carrier M)) M
HomoMorphism-List M = record
  { function    = MonProofs.squish M
  ; mempty-resp = MonProofs.squish-mempty M
  ; <>-resp     = MonProofs.squish-++ M
  }

---------------------------------------------------------------------------
-- Category
---------------------------------------------------------------------------

-- _≤_
-- source ≤ middle → middle ≤ target → source ≤ target

record Category : Set₁ where
  field
  -- Type and operations
    Object : Set
    Morphism : (source target : Object) → Set
    _then_   : ∀ {s m t} → Morphism s m → Morphism m t → Morphism s t
    identity : ∀ {s} → Morphism s s

  field
    then-assoc  : ∀ {s m₁ m₂ t} (x : Morphism s m₁) (y : Morphism m₁ m₂) (z : Morphism m₂ t)
                → ((x then y) then z) ≡ (x then (y then z))

    then-identity : ∀ {s t} (x : Morphism s t) → (x then identity) ≡ x
    identity-then : ∀ {s t} (x : Morphism s t) → (identity then x) ≡ x
