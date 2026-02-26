module Week07 where

open import Data.Unit.Base using (⊤)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (ℕ; _+_; _≤_; z≤n)
open import Data.Bool.Base using (Bool; true; false;  if_then_else_)
open import Data.Product.Base using (_,_; ∃; _×_)
open import Function.Base using (_$_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

------------------------------------------------------------------------
-- Food for thoughts wrt last week

-- FUNCTIONAL EXTENSIONALITY
-- Not provable; but is it harmful?


------------------------------------------------------------------------
-- Our syntax & semantics

data Ty : Set where
  `Bool `Nat : Ty
  `Fun : (S T : Ty) → Ty

variable
  σ τ : Ty

infixl 4 _-,_
data Ctx : Set where
  []   : Ctx
  _-,_ : Ctx → Ty → Ctx

variable
  Γ Δ : Ctx

data Var : Ctx → Ty → Set where
  -- e : Var [] σ : no variables in the empty context!
  zero :           Var (Γ -, σ) σ
  suc  : Var Γ σ → Var (Γ -, τ) σ

data TExpr (Γ : Ctx) : Ty → Set where
  aNat  : ℕ → TExpr Γ `Nat
  aBool : Bool → TExpr Γ `Bool
  add   : (m n : TExpr Γ `Nat) → TExpr Γ `Nat
  ifte  : ∀ {T} → (b : TExpr Γ `Bool) (l r : TExpr Γ T) → TExpr Γ T
  var   : ∀ {T} → Var Γ T → TExpr Γ T
  lam   : ∀ {S T} → TExpr (Γ -, S) T → TExpr Γ (`Fun S T)
  app   : ∀ {S T} → TExpr Γ (`Fun S T) →
                    (TExpr Γ S → TExpr Γ T)

TVal : Ty → Set
TVal `Nat  = ℕ
TVal `Bool = Bool
TVal (`Fun S T) = TVal S → TVal T

CVal : Ctx → Set
CVal [] = ⊤
CVal (Γ -, S) = CVal Γ × TVal S


lookup : forall {T} → Var Γ T → (CVal Γ → TVal T)
lookup zero    (_ , v) = v
lookup (suc x) (env , _) = lookup x env

teval : forall {Γ T} -> TExpr Γ T -> (CVal Γ → TVal T)
teval (aNat m) env = m
teval (aBool b) env = b
teval (add m n) env = teval m env + teval n env
teval (ifte b l r) env = if teval b env then teval l env else teval r env
teval (var x) env = lookup x env
teval (lam b) env = λ s → teval b (env , s)
teval (app f t) env = (teval f env) (teval t env)

------------------------------------------------------------------------
-- Transformations

Transformation : Set
Transformation = ∀ {Γ T} → TExpr Γ T → TExpr Γ T

addEval : Transformation
addEval (add (aNat m) (aNat n)) = aNat (m + n)
addEval t = t

depth-first : Transformation -> Transformation
depth-first tr (add s t) = tr (add (depth-first tr s) (depth-first tr t))
depth-first tr (ifte b t e) = tr (ifte (depth-first tr b) (depth-first tr t) (depth-first tr e))
depth-first tr (lam t) = tr (lam (depth-first tr t))
depth-first tr (app f s) = tr (app (depth-first tr f) (depth-first tr s))
depth-first tr t = tr t


------------------------------------------------------------------------
-- Program equivalence

Similar : (T : Ty) -> TVal T -> TVal T -> Set
Similar `Bool v w = v ≡ w
Similar `Nat v w = v ≡ w
Similar (`Fun S T) v w = (s0 s1 : TVal S) -> Similar S s0 s1 -> Similar T (v s0) (w s1)

SimEnv : (Γ : Ctx) -> CVal Γ -> CVal Γ -> Set
SimEnv [] _ _ = ⊤
SimEnv (Γ -, S) (env0 , s0) (env1 , s1) = SimEnv Γ env0 env1 × Similar S s0 s1


-- Properties of Similar:
-- reflexive? symmetric? transitive?

-- symmetric : ∀ T {v w} → Similar T v w → Similar T w v
-- transitive : ∀ T {v w z} → Similar T v w → Similar T w z → Similar T v z
-- reflexiveˡ : ∀ T {v w} → Similar T v w → Similar T v v
-- reflexiveʳ : ∀ T {v w} → Similar T v w → Similar T w w


-- Properties of SimEnv?

-- reflexivesˡ : ∀ Γ {env0 env1} → SimEnv Γ env0 env1 → SimEnv Γ env0 env0
-- symmetrics : ∀ Γ {env0 env1} → SimEnv Γ env0 env1 → SimEnv Γ env1 env0
-- reflexivesʳ : ∀ Γ {env0 env1} → SimEnv Γ env0 env1 → SimEnv Γ env1 env1


_≋_ : ∀ {Γ T} (t0 t1 : TExpr Γ T) → Set
_≋_ {Γ}{T} t0 t1 = (env0 env1 : CVal Γ) -> SimEnv Γ env0 env1 → Similar T (teval t0 env0) (teval t1 env1)


-- Properties of _≋_: reflexive?
-- lookupSim, tevalSim, reflexive

------------------------------------------------------------------------
-- Correct of transformations

Correct : Transformation → Set
Correct tr = ∀ {Γ T} (t : TExpr Γ T) → t ≋ tr t

-- correct-addEval : Correct addEval


{-
-- Prove e.g. ifSim if needed

correct-depth-first
  : (tr : Transformation)
  → Correct tr → Correct (depth-first tr)
-}



-- SUGGEST more optimisations
