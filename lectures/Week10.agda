module Week10 where

open import Level using (_⊔_) -- typed \lub

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; cong; cong₂; sym; module ≡-Reasoning)

open import Function using (_∘′_; id)

open import Week08 using (Monoid; _=Monoid>_; monHomEq)
open import Week09 using
  ( Category; Agda; ℕ≤; monoids
  ; Path; []; _∷_; reflexive; transitive
  ; crush; crush-reflexive; crush-transitive
  )

--------------------------------------------------------------------------
-- Admin

-- Gender Equity, Diversity, and Inclusion (GEDI) Survey for students
-- https://strathsci.qualtrics.com/jfe/form/SV_ePr7PGBR6cSCAui


---------------------------------------------------------------------------
-- Functors

module _ {c ℓ} {A : Set c} (R : A → A → Set ℓ) where

  open Category

  path : Category c (c ⊔ ℓ)
  path .O = A
  path .M = Path R
  path .identity = reflexive
  path ._andThen_ = transitive
  path .andThen-assoc [] ys zs = refl
  path .andThen-assoc (x ∷ xs) ys zs = cong (x ∷_) (path .andThen-assoc xs ys zs)
  path .identity-andThen = refl
  path .andThen-identity {m = []} = refl
  path .andThen-identity {m = x ∷ xs} = cong (x ∷_) (path .andThen-identity)


module _ {c1 c2 ℓ1 ℓ2} (S : Category c1 ℓ1) (T : Category c2 ℓ2) where

  private
    module S = Category S
    module T = Category T

  -- Functor: structure-preserving transformation
  record _=Category>_ : Set (c1 ⊔ c2 ⊔ ℓ1 ⊔ ℓ2) where
    field
      -- functions
      obj-fun : S.O → T.O -- what do we do with objects?
      hom-fun : {s t : S.O} → S.M s t → T.M (obj-fun s) (obj-fun t)
      -- properties
      identity-identity : ∀ {o} → hom-fun (S.identity {o}) ≡ T.identity
      andThen-andThen : ∀ {s m t} (f : S.M s m) (g : S.M m t) →
        hom-fun (f S.andThen g) ≡ (hom-fun f) T.andThen (hom-fun g)


module _ {c ℓ} (S : Category c ℓ) where

  open _=Category>_

  ID : S =Category> S
  ID .obj-fun = id
  ID .hom-fun = id
  ID .identity-identity = refl
  ID .andThen-andThen = λ f g → refl


module _
  {cs cm ct ls lm lt}
  {S : Category cs ls} {M : Category cm lm} {T : Category ct lt}
  (F : S =Category> M) (G : M =Category> T)
  where

  private
    module F = _=Category>_ F
    module G = _=Category>_ G
    open _=Category>_

  ANDTHEN : S =Category> T
  ANDTHEN .obj-fun = λ s → G .obj-fun (F .obj-fun s)
  ANDTHEN .hom-fun = λ f → G .hom-fun (F .hom-fun f)
  ANDTHEN .identity-identity {o}
    rewrite F.identity-identity {o} = G.identity-identity
  ANDTHEN .andThen-andThen f g
    rewrite F.andThen-andThen f g = G.andThen-andThen (F.hom-fun f) (F.hom-fun g)

-- Crush is a Functor
module _ {c ℓ} (C : Category c ℓ) where

  open Category C
  open _=Category>_

  CRUSH : path M =Category> C
  CRUSH .obj-fun = id
  CRUSH .hom-fun = crush C
  CRUSH .identity-identity = crush-reflexive C
  CRUSH .andThen-andThen = crush-transitive C

module _
  {a b la lb} {A : Set a} {B : Set b}
  {Ra : A → A → Set la} {Rb : B → B → Set lb}
  (f : A → B) (prff : ∀ {x y} → Ra x y → Rb (f x) (f y))
  where

  open _=Category>_

  MAP : path Ra =Category> path Rb
  MAP .obj-fun = f
  MAP .hom-fun [] = []
  MAP .hom-fun (x ∷ xs) = prff x ∷ MAP .hom-fun xs
  MAP .identity-identity = refl
  MAP .andThen-andThen [] ys = refl
  MAP .andThen-andThen (x ∷ xs) ys = cong (prff x ∷_) (MAP .andThen-andThen xs ys)



module _
  {c1 c2 ℓ1 ℓ2}
  {A : Set c1}
  {R : A → A → Set ℓ1} {T : Category c2 ℓ2}
  (fun : path R =Category> T) where

  module F = _=Category>_ fun
  module T = Category T

  edgeMap : ∀ {s t} → R s t → T.M (F.obj-fun s) (F.obj-fun t)
  edgeMap r = F.hom-fun (r ∷ [])







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
