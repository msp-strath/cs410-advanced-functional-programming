module Week09 where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; cong; cong₂; sym; module ≡-Reasoning)

open import Function using (_∘′_; id)

open import Week08 using (Monoid; _=Monoid>_)

-- 🀶🁘🁐 -- OK!
-- 🁋🀳🁁 -- not OK!
-- A category is a fancy monoid:
--  - It has a type of objects
--  - It has a type of morphisms with a source & target object

--
--  - For each object, it has a unit morphism from the object to itself
--  - It has a way to combine two morphisms
--    (provided the target of the first is the source of the second)
--  - Combining morphisms is associative
--  - Combining morphisms has left & right unit laws

---------------------------------------------------------------------------
-- Category
---------------------------------------------------------------------------


open import Level using (Level; _⊔_; 0ℓ)
variable c ℓ : Level

-- DEFINE
record Category c ℓ : Set (Level.suc (c ⊔ ℓ)) where
  field
    -- types
    O : Set c
    M : O → O → Set ℓ
    -- operations
    identity : ∀ {o} → M o o
    _andThen_ : ∀ {s m t} → M s m → M m t → M s t
    -- laws
    andThen-assoc    : ∀ {s lm rm t} (f : M s lm) (g : M lm rm) (h : M rm t) →
                       (f andThen g) andThen h ≡ f andThen (g andThen h)
    identity-andThen : ∀ {s t} {m : M s t} → identity andThen m ≡ m
    andThen-identity : ∀ {s t} {m : M s t} → m andThen identity ≡ m

open Category

Agda : Category (Level.suc 0ℓ) 0ℓ
Agda .O = Set₀
Agda .M S T = S → T
Agda .identity = λ x → x
Agda ._andThen_ = λ f g x → g (f x)
Agda .andThen-assoc = λ f g h → refl
Agda .identity-andThen = refl
Agda .andThen-identity = refl

open import Data.Nat.Base using (ℕ; _≤_)
open import Data.Nat.Properties using (≤-refl; ≤-trans;  ≤-irrelevant)

discrete : (A : Set ℓ) → Category ℓ ℓ
discrete A .O = A
discrete A .M m n = m ≡ n
discrete A .identity = refl
discrete A ._andThen_ = trans
discrete A .andThen-assoc refl refl refl = refl
discrete A .identity-andThen = refl
discrete A .andThen-identity {m = refl} = refl

ℕ≤ : Category 0ℓ 0ℓ
ℕ≤ .O = ℕ
ℕ≤ .M = _≤_
ℕ≤ .identity = ≤-refl
ℕ≤ ._andThen_ = ≤-trans
ℕ≤ .andThen-assoc = λ _ _ _ → ≤-irrelevant _ _
ℕ≤ .identity-andThen = ≤-irrelevant _ _
ℕ≤ .andThen-identity = ≤-irrelevant _ _

-- EXAMPLES: (Set, Nat (discrete & ≤), Kleisli for Maybe?)

open import Data.Maybe using (Maybe; nothing; just; _>>=_)


module _ (funExt : ∀ {A B : Set} (f g : A → B) → (∀ x → (f x ≡ g x)) → f ≡ g) where

  Kleisli : Category (Level.suc 0ℓ) 0ℓ
  Kleisli .O = Set
  Kleisli .M S T = S → Maybe T
  Kleisli .identity = just
  Kleisli ._andThen_ = λ start finish x → start x >>= finish
  Kleisli .andThen-assoc f g h = funExt _ _ λ x → go (f x) where

   go : ∀ fx → (fx >>= g >>= h) ≡ (fx >>= (λ x₁ → g x₁ >>= h))
   go (just x) = refl
   go nothing = refl

  Kleisli .identity-andThen = refl
  Kleisli .andThen-identity {m = m} = funExt _ _ λ x → go (m x) where

    go : ∀ mx → (mx >>= just) ≡ mx
    go (just x) = refl
    go nothing = refl

-- EXAMPLES:
-- Categories are fancy monoids
-- or... every Monoid gives rise to a boring category

open import Data.Unit.Base using (⊤)

Carrier : {A : Set} → Monoid A → Set
Carrier {A = A} _ = A

module _ {A : Set} (m : Monoid A) where

  open Monoid m

  monoid : Category 0ℓ 0ℓ
  monoid .O = ⊤
  monoid .M = λ _ _ → Carrier m
  monoid .identity = neu
  monoid ._andThen_ = _<>_
  monoid .andThen-assoc = <>-assoc
  monoid .identity-andThen = neu-<>
  monoid .andThen-identity = <>-neu












---------------------------------------------------------------------------
-- Category of monoids












---------------------------------------------------------------------------
-- Squish but for categories!



---------------------------------------------------------------------------
-- Proof by reflection


-- DEFINE syntactic representation of lumps of compositions

-- DEFINE semantics via composition
-- DEFINE semantics equivalence

-- DEFINE evaluation
-- DEFINE normalisation

-- DEFINE normalisation equivalence


-- PROVE normalisation preserves semantics



-- PROVE normalisation equivalence implies semantics equivalence



-- USE for proof
