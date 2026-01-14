{-# OPTIONS --guardedness #-}

open import Data.Bool.Base using (Bool; true; false)
open import Data.List.Base using (List; []; _∷_; zip; length)
open import Data.Nat.Base using (ℕ; zero; suc; _≤′_; ≤′-reflexive; ≤′-step)
open import Data.Nat.Properties using (_≤′?_)
open import Data.Product.Base using (_×_; _,_)
open import Data.String.Base using (String)
open import Data.Unit.Base using (⊤)

open import Function.Base using (_$_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)

variable
  A B C I O S T : Set

------------------------------------------------------------------------
-- Adding indices to a list, poorly

[_⋯_] : ℕ → ℕ → List ℕ
[ m ⋯ n ] with m ≤′? n
... | no ¬m≤′n = []
... | yes m≤′n = go [] _ m≤′n where

  go : List ℕ → (up : ℕ) → m ≤′ up → List ℕ
  go acc up (≤′-reflexive refl) = up ∷ acc
  go acc up (≤′-step p) = go (up ∷ acc) _ p

_ : [ 1 ⋯ 10 ] ≡ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ 10 ∷ []
_ = refl

_ : [ 10 ⋯ 1 ] ≡ []
_ = refl

-- Using zip
addIndices : List A → List (ℕ × A)
addIndices xs = zip [ 1 ⋯ length xs ] xs

_ : (a b c : A) → addIndices (a ∷ b ∷ c ∷ [])
   ≡ (1 , a) ∷ (2 , b) ∷ (3 , c) ∷ []
_ = λ a b c → refl


------------------------------------------------------------------------
-- Adding indices to a list, streamly

-- streams

{-
Stream : Set -> Set
Stream A = ℕ -> A
-}

record Stream (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Stream A
open Stream

ones : Stream ℕ
ones .head = 1
ones .tail = ones

[_⋯] : ℕ → Stream ℕ
[ n ⋯] .head = n
[ n ⋯] .tail = [ suc n ⋯]

[_⋯]' : ℕ → Stream ℕ
[ n ⋯]' .head = n
[ n ⋯]' .tail = [ suc (suc n) ⋯]'

take : ℕ → Stream A → List A
take zero s = []
take (suc n) s = head s ∷ take n (tail s)

-- t = take 10 ([ 15 ⋯]')

∞zip : Stream A → List B → List (A × B)
∞zip s [] = []
∞zip s (b ∷ bs) = (head s , b) ∷ ∞zip (tail s) bs

addIndices′ : List A → List (ℕ × A)
addIndices′ as = ∞zip [ 1 ⋯] as

_ : (a b c : A) → addIndices′ (a ∷ b ∷ c ∷ [])
  ≡ (1 , a) ∷ (2 , b) ∷ (3 , c) ∷ []
_ = λ a b c → refl

------------------------------------------------------------------------
-- Input/Output trees

record ∞Tree (I O : Set) (A : Set) : Set
data Tree (I O : Set) (A : Set) : Set where
  pure     : A → Tree I O A
  interact : O → (I → ∞Tree I O A) → Tree I O A

record ∞Tree I O A where
  coinductive
  field force : Tree I O A

open ∞Tree

untilTrue : ℕ → Tree Bool ⊤ ℕ
untilTrue steps = interact _ reply where

  reply : Bool → ∞Tree Bool ⊤ ℕ
  reply false .force = untilTrue (suc steps)
  reply true  .force = pure steps


data Output : Set where
  Skip  : Output
  Print : String → Output

data Input : Set where
  Stop : Input
  Line : String → Input

echo : Tree Input Output ⊤
echo = interact Skip reply where

  reply : Input → ∞Tree Input Output ⊤
  reply Stop       .force = pure _
  reply (Line str) .force = interact (Print str) reply

simulate :
  Tree I O A →
  (I → Tree S T O) →
  Tree S T A
simulate = {!!}


open import IO

io : Tree Input Output ⊤ → IO ⊤
io = {!!}
