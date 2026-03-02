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
-- Our syntax, semantics, and transformations

-- Just to show we're not pulling your leg: reuse last week's definitions

open import Week06 using
  ( -- syntax
    Ty; `Bool; `Nat; `Fun; σ; τ
  ; Ctx; []; _-,_; Γ; Δ
  ; Var; zero; suc
  ; TExpr; aNat; aBool; add; ifte; var; lam; app
    -- semantics
  ; TVal; CVal; lookup; teval
    -- transformations
  ; Transformation; addEval; depth-first
  )

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
