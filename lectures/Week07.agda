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

-- For more on this,
-- A Formalised Proof of the Soundness and Completeness of
-- a Simply Typed Lambda-Calculus with Explicit Substitutions
-- by Catarina Coquand
-- https://link.springer.com/article/10.1023/A:1019964114625

Similar : (T : Ty) -> TVal T -> TVal T -> Set
Similar `Bool v w = v ≡ w
Similar `Nat v w = v ≡ w
Similar (`Fun S T) v w = (s0 s1 : TVal S) -> Similar S s0 s1 -> Similar T (v s0) (w s1)

SimEnv : (Γ : Ctx) -> CVal Γ -> CVal Γ -> Set
SimEnv [] _ _ = ⊤
SimEnv (Γ -, S) (env0 , s0) (env1 , s1) = SimEnv Γ env0 env1 × Similar S s0 s1


-- Properties of Similar:
-- reflexive? symmetric? transitive?

{-
reflexive : ∀ (T : Ty) (t : TVal T) → Similar T t t
reflexive `Bool t = refl
reflexive `Nat t = refl
reflexive (`Fun S T) t = {!!}
  -- OOPS, that's (more or less) functional extensionality which we cannot prove!

-- We have a PER (Partial Equivalence Relation)!
-}

symmetric : ∀ T {v w} → Similar T v w → Similar T w v
symmetric `Bool      vq = sym vq
symmetric `Nat       vq = sym vq
symmetric (`Fun S T) vq = λ s0 s1 sq → symmetric T (vq s1 s0 (symmetric S sq))

transitive : ∀ T {v w z} → Similar T v w → Similar T w z → Similar T v z
reflexiveʳ : ∀ T {v w} → Similar T v w → Similar T w w

transitive `Bool      vq wq = trans vq wq
transitive `Nat       vq wq = trans vq wq
transitive (`Fun S T) vq wq = λ s0 s1 sq →
  transitive T (vq s0 s1 sq) (wq s1 s1 (reflexiveʳ S sq))

reflexiveʳ S sq = transitive S (symmetric S sq) sq

reflexiveˡ : ∀ T {v w} → Similar T v w → Similar T v v
reflexiveˡ S sq = reflexiveʳ S (symmetric S sq)


-- Properties of SimEnv?

reflexivesˡ : ∀ Γ {env0 env1} → SimEnv Γ env0 env1 → SimEnv Γ env0 env0
reflexivesˡ []        _          = _
reflexivesˡ (Γ -, T) (envq , tq) = reflexivesˡ Γ envq , reflexiveˡ T tq

symmetrics : ∀ Γ {env0 env1} → SimEnv Γ env0 env1 → SimEnv Γ env1 env0
symmetrics []        _          = _
symmetrics (Γ -, T) (envq , tq) = symmetrics Γ envq , symmetric T tq

reflexivesʳ : ∀ Γ {env0 env1} → SimEnv Γ env0 env1 → SimEnv Γ env1 env1
reflexivesʳ []        _          = _
reflexivesʳ (Γ -, T) (envq , tq) = reflexivesʳ Γ envq , reflexiveʳ T tq


_≋_ : ∀ {Γ T} (t0 t1 : TExpr Γ T) → Set
_≋_ {Γ}{T} t0 t1 = {env0 env1 : CVal Γ} -> SimEnv Γ env0 env1 → Similar T (teval t0 env0) (teval t1 env1)


-- Properties of _≋_: reflexive?
-- lookupSim, tevalSim, reflexive

lookupSim :
  ∀ {Γ T} (x : Var Γ T) →
  {env0 env1 : CVal Γ} -> SimEnv Γ env0 env1 →
  Similar T (lookup x env0) (lookup x env1)
lookupSim zero    (_    , vq) = vq
lookupSim (suc x) (envq , _)  = lookupSim x envq


tevalSim : ∀ {Γ T} (t : TExpr Γ T) → t ≋ t
tevalSim (aNat n)     envq = refl
tevalSim (aBool b)    envq = refl
tevalSim (add m n)    envq
  rewrite tevalSim m envq
        | tevalSim n envq
  = refl
tevalSim (ifte b l r) {env0 = env0} {env1 = env1} envq
  with teval b env0 | teval b env1 | tevalSim b envq
... | true  | .true  | refl = tevalSim l envq
... | false | .false | refl = tevalSim r envq
tevalSim (var x)      envq = lookupSim x envq
tevalSim (lam b)      envq = λ s0 s1 sq → tevalSim b (envq , sq)
tevalSim (app f t)    envq =
  let funSim = tevalSim f envq in
  funSim _ _ (tevalSim t envq)




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
