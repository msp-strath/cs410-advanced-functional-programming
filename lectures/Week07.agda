module Week07 where

open import Data.Unit.Base using (⊤)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (ℕ; _+_; _≤_; z≤n)
open import Data.Bool.Base using (Bool; true; false;  if_then_else_)
open import Data.Product.Base using (_,_; ∃; _×_)
open import Function.Base using (_$_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

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
Similar `Bool      v w = v ≡ w
Similar `Nat       v w = v ≡ w
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
Correct tr = ∀ {Γ T} (t : TExpr Γ T) → tr t ≋ t

correct-addEval : Correct addEval
correct-addEval (aNat x) envq = refl
correct-addEval (aBool x) envq = refl
correct-addEval (add (aNat m) (aNat n)) envq = refl
correct-addEval e@(add (aNat x) (add t₁ t₂)) envq = tevalSim e envq
correct-addEval e@(add (aNat x) (ifte t₁ t₂ t₃)) envq = tevalSim e envq
correct-addEval e@(add (aNat x) (var x₁)) envq = tevalSim e envq
correct-addEval e@(add (aNat x) (app t₁ t₂)) envq = tevalSim e envq
correct-addEval e@(add (add t t₂) t₁) envq = tevalSim e envq
correct-addEval e@(add (ifte t t₂ t₃) t₁) envq = tevalSim e envq
correct-addEval e@(add (var x) t₁) envq = tevalSim e envq
correct-addEval e@(add (app t t₂) t₁) envq = tevalSim e envq
correct-addEval e@(ifte _ _ _) envq = tevalSim e envq
correct-addEval e@(var _) envq = tevalSim e envq
correct-addEval e@(lam _) envq = tevalSim e envq
correct-addEval e@(app _ _) envq = tevalSim e envq


data AddEvalEh? {Γ} : ∀ {T} → TExpr Γ T → Set where
  aye : ∀ {m n} → AddEvalEh? (add (aNat m) (aNat n))
  naw : ∀ {T} {t : TExpr Γ T} → AddEvalEh? t

addEvalEh? : ∀ {Γ T} (t : TExpr Γ T) → AddEvalEh? t
addEvalEh? (add (aNat m) (aNat n)) = aye
addEvalEh? t = naw

addEval' : Transformation
addEval' t with addEvalEh? t
addEval' (.add (.aNat m) (.aNat n)) | aye = aNat (m + n)
addEval' t | naw = t

correct-addEval' : Correct addEval'
correct-addEval' t envq with addEvalEh? t
... | aye = refl
... | naw = tevalSim t envq

-- Prove e.g. ifSim if needed

ifSim : ∀ {T b0 b1 l0 l1 r0 r1} →
  Similar `Bool b0 b1 →
  Similar T l0 l1 →
  Similar T r0 r1 →
  Similar T (if b0 then l0 else r0) (if b1 then l1 else r1)
ifSim {b0 = true}  refl lq rq = lq
ifSim {b0 = false} refl lq rq = rq

correct-depth-first
  : (tr : Transformation)
  → Correct tr → Correct (depth-first tr)
correct-depth-first tr ctr (aNat n) envq = ctr (aNat n) envq
correct-depth-first tr ctr (aBool b) envq = ctr (aBool b) envq
correct-depth-first tr ctr (add m n) envq
  = transitive `Nat
     (ctr (add (depth-first tr m) (depth-first tr n)) envq)
     (cong₂ _+_
            (correct-depth-first tr ctr m (reflexivesʳ _ envq))
            (correct-depth-first tr ctr n (reflexivesʳ _ envq)))
correct-depth-first tr ctr (ifte b l r) envq
  = transitive _
     (ctr (ifte (depth-first tr b) (depth-first tr l) (depth-first tr r)) envq)
     (ifSim
       (correct-depth-first tr ctr b (reflexivesʳ _ envq))
       (correct-depth-first tr ctr l (reflexivesʳ _ envq))
       (correct-depth-first tr ctr r (reflexivesʳ _ envq)))
correct-depth-first tr ctr (var x) envq = ctr (var x) envq
correct-depth-first tr ctr (lam b) envq s0 s1 sq =
  transitive _
    (ctr (lam (depth-first tr b)) (reflexivesˡ _ envq) s0 s0 (reflexiveˡ _ sq))
    (correct-depth-first tr ctr b (envq , sq))
correct-depth-first tr ctr (app f t) envq =
  let funSim = correct-depth-first tr ctr f envq in
  transitive _
    (ctr (app (depth-first tr f) (depth-first tr t)) (reflexivesˡ _ envq))
    (funSim
       (teval (depth-first tr t) _)
       (teval t _)
       (correct-depth-first tr ctr t envq))

correct-allAdds : Correct (depth-first addEval')
correct-allAdds = correct-depth-first addEval' correct-addEval'

open import Function.Base using (id; _∘_)

correct-id : Correct id
correct-id = tevalSim

correct-∘ : ∀ {g f : Transformation} →
  Correct g →
  Correct f →
  Correct (g ∘ f)
correct-∘ g f t envq
  = transitive _ (g _ envq) (f _ (reflexivesʳ _ envq))

-- SUGGEST more optimisations

data IfEvalEh? {Γ} : ∀ {T} → TExpr Γ T → Set where
  aye : ∀ {T b} {l r : TExpr Γ T} → IfEvalEh? (ifte (aBool b) l r)
  naw : ∀ {T} {t : TExpr Γ T} → IfEvalEh? t

ifEvalEh? : ∀ {Γ T} (t : TExpr Γ T) → IfEvalEh? t
ifEvalEh? (ifte (aBool b) l r) = aye
ifEvalEh? t = naw

ifEval : Transformation
ifEval t with ifEvalEh? t
ifEval (.ifte (.aBool b) l r) | aye = if b then l else r
ifEval t | naw = t

correct-ifEval : Correct ifEval
correct-ifEval t with ifEvalEh? t
correct-ifEval (ifte (aBool true) l r) | aye = tevalSim l
correct-ifEval (ifte (aBool false) l r) | aye = tevalSim r
... | naw = tevalSim t
