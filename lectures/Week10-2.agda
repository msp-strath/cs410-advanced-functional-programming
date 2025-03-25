{-# OPTIONS --guardedness #-}

open import Data.Bool.Base using (Bool; true; false)
open import Data.List.Base using (List; []; _∷_; zip; length)
open import Data.Nat.Base using (ℕ; zero; suc; _≤′_; ≤′-reflexive; ≤′-step)
open import Data.Nat.Properties using (_≤′?_)
open import Data.Product.Base using (_×_; _,_)
open import Data.Unit.Base using (⊤)

open import Function.Base using (_$_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)

variable
  A B C I O S T : Set

------------------------------------------------------------------------
-- Adding indices to a list

[_⋯_] : ℕ → ℕ → List ℕ
[ m ⋯ n ] with m ≤′? n
... | no ¬m≤n = []
... | yes m≤n = go [] _ _ m≤n where

  go : List ℕ → (m n : ℕ) (p : m ≤′ n) → List ℕ
  go acc m m       (≤′-reflexive refl) = m ∷ acc
  go acc m (suc n) (≤′-step p)         = go (suc n ∷ acc) m n p


_ : [ 3 ⋯ 10 ] ≡ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ 10 ∷ []
_ = refl

-- Using zip
addIndices : List A → List (ℕ × A)
addIndices xs = zip [ 1 ⋯ length xs ] xs

_ : (a b c : A) → addIndices (a ∷ b ∷ c ∷ [])
   ≡ (1 , a) ∷ (2 , b) ∷ (3 , c) ∷ []
_ = λ a b c → refl



------------------------------------------------------------------------
-- Adding indices to a list



record Stream (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Stream A
open Stream

[_⋯] : ℕ → Stream ℕ
[ n ⋯] .head = n
[ n ⋯] .tail = [ suc n ⋯]


∞zip : Stream A → List B → List (A × B)
∞zip as []       = []
∞zip as (b ∷ bs) = (as .head , b) ∷ ∞zip (as .tail) bs

addIndices′ : List A → List (ℕ × A)
addIndices′ = ∞zip [ 1 ⋯]

_ : (a b c : A) → addIndices′ (a ∷ b ∷ c ∷ [])
  ≡ (1 , a) ∷ (2 , b) ∷ (3 , c) ∷ []
_ = λ a b c → refl


record ∞IOTree (I O A : Set) : Set
data IOTree (I O : Set) (A : Set) : Set where
  pure : A → IOTree I O A
  ask  : O → (I → ∞IOTree I O A) → IOTree I O A

record ∞IOTree I O A where
  coinductive
  field force : IOTree I O A

open ∞IOTree


untilTrue : ℕ → IOTree Bool ⊤ ℕ
untilTrue steps = ask _ reply where

  reply : Bool → ∞IOTree Bool ⊤ ℕ
  reply true  .force = pure steps
  reply false .force = untilTrue (suc steps)


open import Data.String.Base using (String)

data Output : Set where
  Skip : Output
  Print : String → Output

data Input : Set where
  Line : String → Input

echo : IOTree Input Output ⊤
echo = ask Skip go where

  go : Input → ∞IOTree Input Output ⊤
  go (Line str) .force = ask (Print str) go
