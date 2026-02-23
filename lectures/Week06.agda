module Week06 where

open import Data.Unit.Base using (⊤)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (ℕ; _+_; _≤_; z≤n)
open import Data.Bool.Base using (Bool; true; false;  if_then_else_)
open import Data.Product.Base using (_,_; ∃; _×_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Food for thoughts wrt last week

-- CHECKING
-- What if we have overloaded constructs e.g. `_+_` for all the
-- numerical types? Inference vs. checking, information propagation

-- UNIQUE TYPES
-- We could have proven that if two typed terms erase to the same
-- raw term then their respective types are equal. Is that always
-- the case? Can we always produce a most general type?

_ : ∃ (0 ≤_)
_ = 2 , z≤n

_ : ℕ × 0 ≤ 3000
_ = 2 , z≤n

-- CLOSED TERMS
-- How computationally interesting is the language we saw last
-- week?


------------------------------------------------------------------------
-- Adding scoped-and-typed variables to the syntax

data Ty : Set where
  `Bool `Nat : Ty
  `Fun : (S T : Ty) → Ty

_ : Ty
_ = `Fun `Nat `Bool

variable
  σ τ : Ty

-- DEFINE contexts Ctx
-- and give examples

infixl 4 _-,_
data Ctx : Set where
  []   : Ctx
  _-,_ : Ctx → Ty → Ctx

variable
  Γ Δ : Ctx

-- [> Ty ] in disguise

_ : Ctx
_ = []

_ : Ctx
_ = [] -, `Bool -, `Nat -, `Bool

-- DEFINE membership
-- and give examples

-- De Bruijn indices aka proof-relevant positions in the Ctx
data Var : Ctx → Ty → Set where
  -- e : Var [] σ : no variables in the empty context!
  zero :           Var (Γ -, σ) σ
  suc  : Var Γ σ → Var (Γ -, τ) σ

-- Any (σ ≡_) Γ in disguise


-- DEFINE typed-and-scoped expressions

data TExpr (Γ : Ctx) : Ty → Set where
  -- old constructors
  aNat  : ℕ → TExpr Γ `Nat
  aBool : Bool → TExpr Γ `Bool
  add   : (m n : TExpr Γ `Nat) → TExpr Γ `Nat
  ifte  : ∀ {T} → (b : TExpr Γ `Bool) (l r : TExpr Γ T) → TExpr Γ T
  -- new constructors
  var   : ∀ {T} → Var Γ T → TExpr Γ T
  lam   : ∀ {S T} → TExpr (Γ -, S) T → TExpr Γ (`Fun S T)
  app   : ∀ {S T} → TExpr Γ (`Fun S T) →
                    (TExpr Γ S → TExpr Γ T)

-- DEFINE boolToNat

boolToNat : TExpr Γ (`Fun `Bool `Nat)
boolToNat = lam (ifte (var zero) (aNat 1) (aNat 0))

-- DEFINE double
double : TExpr Γ (`Fun `Nat `Nat)
double = lam (add (var zero) (var zero)) -- λ x → x + x

-- DEFINE const
const : TExpr Γ (`Fun σ (`Fun τ σ))
const = lam (lam (var (suc zero)))

four : TExpr [] `Nat
four = app double (aNat 2)

------------------------------------------------------------------------
-- Extending the semantics


-- DEFINE TVal
TVal : Ty → Set
TVal `Nat  = ℕ
TVal `Bool = Bool
TVal (`Fun S T) = TVal S → TVal T

-- DEFine CVal
CVal : Ctx → Set
CVal [] = ⊤
CVal (Γ -, S) = CVal Γ × TVal S
-- All TVal Γ in disguise

-- Examples of CVal

_ : CVal ([] -, `Bool -, `Nat)
_ = ((_ , false) , 0)


lookup : forall {T} → Var Γ T → (CVal Γ → TVal T)
lookup zero    (_ , v) = v
lookup (suc x) (env , _) = lookup x env

-- DEFINE teval
teval : forall {Γ T} -> TExpr Γ T -> (CVal Γ → TVal T)
teval (aNat m) env = m
teval (aBool b) env = b
teval (add m n) env = teval m env + teval n env
teval (ifte b l r) env = if teval b env then teval l env else teval r env
teval (var x) env = lookup x env
teval (lam b) env = λ s → teval b (env , s)
teval (app f t) env
  = let fun = teval f env
        arg = teval t env
    in fun arg

-- Examples

_ : teval four _ ≡ 4
_ = refl


------------------------------------------------------------------------
-- Transformations


-- Transformation : Set
-- Transformation = ∀ {Γ T} → TExpr Γ T → TExpr Γ T


-- DEFINE a constant folding operation



-- DEFINE a semantic equivalence _≋_ over typed terms
-- DEFINE Correctness of a transformation


-- PROVE your constant folding operation correct


-- SUGGEST more optimisations
