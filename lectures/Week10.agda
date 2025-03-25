{-# OPTIONS --guardedness #-}

open import Data.Nat.Base using (ℕ; suc)
open import Data.Product.Base as Prod using (_×_; _,_; uncurry)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit.Base using (⊤)

open import Function.Base using (id; const)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

variable
  X Y A B : Set

------------------------------------------------------------------------------
-- Universe of descriptions

-- Desc

interleaved mutual

  data Desc : Set₁
  ⟦_⟧ : Desc → Set → Set

  -- parameter
  data Desc where `X : Desc
  ⟦ `X ⟧ X = X

  -- sum
  data Desc where _`+_ : Desc → Desc → Desc
  ⟦ d `+ e ⟧ X = ⟦ d ⟧ X ⊎ ⟦ e ⟧ X

  -- product
  data Desc where _`×_ : Desc → Desc → Desc
  ⟦ d `× e ⟧ X = ⟦ d ⟧ X × ⟦ e ⟧ X

  -- constant
  data Desc where `κ : Set → Desc
  ⟦ `κ A ⟧ _ = A

`Maybe : Desc
`Maybe = `κ ⊤ `+ `X

nothing : ⟦ `Maybe ⟧ X
nothing = inj₁ _

just : X → ⟦ `Maybe ⟧ X
just x = inj₂ x


-- Meaning is functorial

⟦_⟧-functor : (d : Desc) → (X → Y) → (⟦ d ⟧ X → ⟦ d ⟧ Y)
⟦ `X ⟧-functor f x = f x
⟦ d `+ e ⟧-functor f (inj₁ x) = inj₁ (⟦ d ⟧-functor f x)
⟦ d `+ e ⟧-functor f (inj₂ y) = inj₂ (⟦ e ⟧-functor f y)
⟦ d `× e ⟧-functor f (x , y) = (⟦ d ⟧-functor f x , ⟦ e ⟧-functor f y)
⟦ `κ A ⟧-functor f x = x

-- Example: mapping over just

map-Maybe : (X → Y) → ⟦ `Maybe ⟧ X → ⟦ `Maybe ⟧ Y
map-Maybe = ⟦ `Maybe ⟧-functor

_ : ∀ (f : X → Y) → map-Maybe f nothing ≡ nothing
_ = λ f → refl

_ : ∀ (f : X → Y) → (x : X) → map-Maybe f (just x) ≡ just (f x)
_ = λ f x → refl

------------------------------------------------------------------------------
-- Fixpoints of functors

-- Algebras

Alg : Desc → Set → Set
Alg d X = ⟦ d ⟧ X → X -- e.g. List M → M


data μ (d : Desc) : Set where
  mkμ : Alg d (μ d)

_ : μ (`κ ⊤)
_ = mkμ _

open import Data.Empty

μX-elim : μ `X → ⊥
μX-elim (mkμ x) = μX-elim x

data μX : Set where
  mkμX : μX → μX

-- Example: Nat as nested Maybes, zeros, and suc

Nat : Set
Nat = μ `Maybe

z : Nat
z = mkμ (inj₁ _)

s : Nat → Nat
s n = mkμ (inj₂ n)


-- Folds over fixpoints

{-# TERMINATING #-}
fold : {d : Desc} → Alg d X → μ d → X
fold {d = d} φ (mkμ t) = φ (⟦ d ⟧-functor (fold φ) t)

safefold : {d : Desc} → Alg d X → μ d → X
mapsafefold : (d : Desc) {D : Desc} → Alg D X → ⟦ d ⟧ (μ D) → ⟦ d ⟧ X

safefold {d = d} φ (mkμ t) = φ (mapsafefold d φ t)

mapsafefold `X φ t = safefold φ t
mapsafefold (d `+ e) φ (inj₁ x) = inj₁ (mapsafefold d φ x)
mapsafefold (d `+ e) φ (inj₂ y) = inj₂ (mapsafefold e φ y)
mapsafefold (d `× e) φ (x , y) = mapsafefold d φ x , mapsafefold e φ y
mapsafefold (`κ A) φ t = t

-- example: add as a fold

-- example: addAlg replacing 0 with n

addAlg : Nat → Alg `Maybe Nat
addAlg n (inj₁ _)   = n       -- 0       + n = n
addAlg n (inj₂ m+n) = s m+n   -- (suc m) + n = suc (m + n)

add : Nat → Nat → Nat
add m n = safefold (addAlg n) m

_ : add (s (s (s z))) (s (s z)) ≡ (s (s (s (s (s z)))))
_ = refl
