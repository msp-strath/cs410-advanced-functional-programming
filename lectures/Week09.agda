module Week09 where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; cong; cong₂; sym; module ≡-Reasoning)

open import Function using (_∘′_; id)

open import Week08 using (Monoid; _=Monoid>_; monHomEq)

-- 🀶🁘🁐 -- OK!
-- 🁋🀳🁁 -- not OK!
--  ^^--  mismatch
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

-- DEFINE Category
record Category c ℓ : Set (Level.suc (c ⊔ ℓ)) where
  field
    -- types
    O : Set c
    M : O → O → Set ℓ
    -- operations
    identity  {- like neu  -} : ∀ {o} → M o o
    _andThen_ {- like _<>_ -} : ∀ {s m t} → M s m → M m t → M s t
    -- laws
    andThen-assoc    : ∀ {s lm rm t} (f : M s lm) (g : M lm rm) (h : M rm t) →
                       (f andThen g) andThen h ≡ f andThen (g andThen h)
    identity-andThen : ∀ {s t} {m : M s t} → identity andThen m ≡ m
    andThen-identity : ∀ {s t} {m : M s t} → m andThen identity ≡ m

module _ where

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

  open Category

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

  open Category

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

open import Data.Product.Base using (∃; _,_)

module _ where

  open _=Monoid>_

  open Category

  monoids : Category (Level.suc 0ℓ) 0ℓ
  monoids .O = ∃ Monoid
  monoids .M (S , mS) (T , mT) = mS =Monoid> mT
  monoids .identity .hom-fun = id
  monoids .identity .neu-neu = refl
  monoids .identity .<>-<> s0 s1 = refl
  (monoids andThen f) g .hom-fun x = g .hom-fun (f .hom-fun x)
  (monoids andThen f) g .neu-neu rewrite f .neu-neu = g .neu-neu
  (monoids andThen f) g .<>-<> s0 s1 rewrite f .<>-<> s0 s1 = g .<>-<> _ _
  monoids .andThen-assoc f g h = monHomEq _ _ refl
  monoids .identity-andThen = monHomEq _ _ refl
  monoids .andThen-identity = monHomEq _ _ refl


---------------------------------------------------------------------------
-- Crush but for categories!


open import Data.List.Base using (List; []; _∷_)


data Path {A : Set c}
       (R : A  →      A  → Set ℓ)
       (s : A) : (t : A) → Set (c ⊔ ℓ) where
  []  : ----------
        Path R s s

  _∷_ : ∀ {m} → R s m →
        ∀ {t} → Path R m t →
        --------------------
        Path R s t

{-
  _<:_ : ∀ {m} → R m s →
         ∀ {t} → Path R m t →
         Path R s t
-}

module _ {c ℓ} {A : Set c} {R : A → A → Set ℓ} where

  reflexive : ∀ {s : A} → Path R s s
  reflexive = []

  transitive : ∀ {s m t : A} → Path R s m → Path R m t → Path R s t
  transitive []       ys = ys
  transitive (x ∷ xs) ys = x ∷ transitive xs ys

module _ {c ℓ} (C : Category c ℓ) where

  open Category C

  crush : ∀ {s t} → Path M s t → M s t
  crush []       = identity
  crush (f ∷ fs) = f andThen crush fs

  crush-reflexive : ∀ {s} → crush (reflexive {s = s}) ≡ identity
  crush-reflexive = refl

  crush-transitive : ∀ {s m t} (xs : Path M s m) (ys : Path M m t) →
    crush (transitive xs ys) ≡ crush xs andThen crush ys
  crush-transitive []       ys = sym identity-andThen
  crush-transitive (x ∷ xs) ys = let open ≡-Reasoning in begin
    x andThen crush (transitive xs ys)
      ≡⟨ cong (x andThen_) (crush-transitive xs ys) ⟩
    (x andThen (crush xs andThen crush ys))
      ≡⟨ andThen-assoc x (crush xs) (crush ys) ⟨
    ((x andThen crush xs) andThen crush ys)
      ≡⟨⟩
    (crush (x ∷ xs) andThen crush ys) ∎


 -- ...
 -- ...
 -- it's a FUNCTOR!







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
