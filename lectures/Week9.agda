{-# OPTIONS --type-in-type #-}

module Week9 where

open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; refl; sym; cong; cong₂)
open Eq.≡-Reasoning

open import Function.Base using (_∘′_; id)
open import Data.List.Base
open import Data.List.Properties

postulate
  funext : {S T : Set} → {f g : S → T} → ((x : S) → f x ≡ g x) → f ≡ g

---------------------------------------------------------------------------
-- Category
---------------------------------------------------------------------------

record Category : Set₁ where
  field
  -- Types and operations
    Object : Set
    Morphism : (source target : Object) → Set
    _then_   : ∀ {s m t} → Morphism s m → Morphism m t → Morphism s t
    identity : ∀ {s} → Morphism s s

  field
    then-assoc  : ∀ {s m₁ m₂ t} (x : Morphism s m₁) (y : Morphism m₁ m₂) (z : Morphism m₂ t)
                → ((x then y) then z) ≡ (x then (y then z))

    then-identity : ∀ {s t} (x : Morphism s t) → (x then identity) ≡ x
    identity-then : ∀ {s t} (x : Morphism s t) → (identity then x) ≡ x


---------------------------------------------------------------------------
-- Functor
---------------------------------------------------------------------------

record Functor (C D : Category) : Set where
  module C = Category C
  module D = Category D
  field
    -- operations
    onObject   : C.Object → D.Object
    onMorphism : ∀ {s t} →
      C.Morphism           s            t →
      D.Morphism (onObject s) (onObject t)

    -- properties
    onIdentity : ∀ {s} → onMorphism (C.identity {s})
                       ≡ D.identity {onObject s}

    onThen : ∀ {s m t} (f : C.Morphism s m) (g : C.Morphism m t) →
             onMorphism (f C.then g) ≡ onMorphism f D.then onMorphism g

-- example

SET : Category
SET .Category.Object = Set
SET .Category.Morphism S T = S -> T
SET .Category._then_ f g = λ x → g (f x)
SET .Category.identity = λ x → x
SET .Category.then-assoc f g h = refl
SET .Category.then-identity f = refl
SET .Category.identity-then f = refl

List-functor : Functor SET SET
List-functor .Functor.onObject X = List X
List-functor .Functor.onMorphism f xs = map f xs
List-functor .Functor.onIdentity = funext foo
  where
   foo : ∀ xs → map (λ x → x) xs ≡ xs
   foo [] = refl
   foo (x ∷ xs) = cong (x ∷_) (foo xs)
List-functor .Functor.onThen f g = funext map-∘

-- e.g. Vec≤


open import Data.Nat.Base using (ℕ; _≤_)
import Data.Nat.Properties as ℕ

ℕ≤-cat : Category
ℕ≤-cat .Category.Object = ℕ
ℕ≤-cat .Category.Morphism = _≤_
ℕ≤-cat .Category._then_ = ℕ.≤-trans
ℕ≤-cat .Category.identity = ℕ.≤-refl
ℕ≤-cat .Category.then-assoc = λ _ _ _ → ℕ.≤-irrelevant _ _
ℕ≤-cat .Category.then-identity = λ _ → ℕ.≤-irrelevant _ _
ℕ≤-cat .Category.identity-then = λ _ → ℕ.≤-irrelevant _ _

open import Data.Vec.Base as Vec using (Vec)
import Data.Vec.Properties as Vec

Vec-Functor : (n : ℕ) → Functor SET SET
Vec-Functor n .Functor.onObject = λ A → Vec A n
Vec-Functor n .Functor.onMorphism = Vec.map
Vec-Functor n .Functor.onIdentity = funext Vec.map-id
Vec-Functor n .Functor.onThen = λ f g → funext (Vec.map-∘ g f)

OP : Category → Category
OP cat .Category.Object = Category.Object cat
OP cat .Category.Morphism = λ s t → Category.Morphism cat t s
OP cat .Category._then_ = λ g f → Category._then_ cat f g
OP cat .Category.identity = Category.identity cat
OP cat .Category.then-assoc = λ f g h → sym (Category.then-assoc cat h g f)
OP cat .Category.then-identity = Category.identity-then cat
OP cat .Category.identity-then = Category.then-identity cat

Vec≤-Functor : (A : Set) → Functor (OP ℕ≤-cat) SET
Vec≤-Functor A .Functor.onObject n = Vec A n
Vec≤-Functor A .Functor.onMorphism = Vec.truncate
Vec≤-Functor A .Functor.onIdentity = funext Vec.truncate-refl
Vec≤-Functor A .Functor.onThen =
  λ n≤p m≤n → funext (Vec.truncate-trans m≤n n≤p)


-- Forget & free

open import Week7 using (Monoid; HomoMorphism)

postulate
  monHomEq : {M N : Monoid} → (f g : HomoMorphism M N)
         → HomoMorphism.function f ≡ HomoMorphism.function g
         → f ≡ g

monoid-cat : Category
monoid-cat .Category.Object = Monoid
monoid-cat .Category.Morphism M N = HomoMorphism M N
(monoid-cat .Category._then_ f g) .HomoMorphism.function
  = HomoMorphism.function g ∘′ HomoMorphism.function f
(Category._then_ monoid-cat f) g .HomoMorphism.mempty-resp rewrite HomoMorphism.mempty-resp f | HomoMorphism.mempty-resp g = refl
(Category._then_ monoid-cat f) g .HomoMorphism.<>-resp x y rewrite HomoMorphism.<>-resp f x y = HomoMorphism.<>-resp g _ _
monoid-cat .Category.identity .HomoMorphism.function = id
monoid-cat .Category.identity .HomoMorphism.mempty-resp = refl
monoid-cat .Category.identity .HomoMorphism.<>-resp x y = refl
monoid-cat .Category.then-assoc f g h = monHomEq _ _ refl
monoid-cat .Category.then-identity f = monHomEq _ _ refl
monoid-cat .Category.identity-then f = monHomEq _ _ refl

module _ where

  open Monoid

  List-Monoid : Set -> Monoid
  List-Monoid X .Carrier = List X
  List-Monoid X ._<>_ xs ys = xs ++ ys
  List-Monoid X .mempty = []
  List-Monoid X .<>-assoc [] ys zs = refl
  List-Monoid X .<>-assoc (x ∷ xs) ys zs =
    cong (x ∷_) (List-Monoid X .<>-assoc xs ys zs)
  List-Monoid X .<>-mempty [] = refl
  List-Monoid X .<>-mempty (x ∷ xs) =
    cong (x ∷_) (List-Monoid X .<>-mempty xs)
  List-Monoid X .mempty-<> xs = refl

Forget : Functor monoid-cat SET
Forget .Functor.onObject = Monoid.Carrier
Forget .Functor.onMorphism = HomoMorphism.function
Forget .Functor.onIdentity = refl
Forget .Functor.onThen = λ f g → refl

Free : Functor SET monoid-cat
Free .Functor.onObject = List-Monoid
Free .Functor.onMorphism f .HomoMorphism.function = map f
Free .Functor.onMorphism f .HomoMorphism.mempty-resp = refl
Free .Functor.onMorphism f .HomoMorphism.<>-resp [] ys = refl
Free .Functor.onMorphism f .HomoMorphism.<>-resp (x ∷ xs) ys =
  cong (_ ∷_) (Free .Functor.onMorphism f .HomoMorphism.<>-resp xs ys)
Free .Functor.onIdentity = monHomEq _ _ (funext map-id)
Free .Functor.onThen f g = monHomEq _ _ (funext map-∘)




-- CAT

module _ where

  open Functor

  ID : ∀ {C} → Functor C C
  ID .onObject = λ z → z
  ID .onMorphism = λ z → z
  ID .onIdentity = refl
  ID .onThen = λ f g → refl

  THEN : ∀ {C D E} → Functor C D → Functor D E → Functor C E
  THEN F G .onObject = λ x → G .onObject (F .onObject x)
  THEN F G .onMorphism = λ f → G .onMorphism (F .onMorphism f)
  THEN {C} {D} {E} F G .onIdentity = begin
    G .onMorphism (F .onMorphism (Category.identity C))
      ≡⟨ cong (G .onMorphism) (F .onIdentity) ⟩
    G .onMorphism (Category.identity D)
      ≡⟨ G .onIdentity ⟩
    Category.identity E ∎
  THEN {C} {D} {E} F G .onThen f g = begin
    G .onMorphism (F .onMorphism ((C Category.then f) g))
      ≡⟨ cong (G .onMorphism) (F .onThen f g) ⟩
    G .onMorphism ((D Category.then F .onMorphism f) (F .onMorphism g))
      ≡⟨ G .onThen (F .onMorphism f) (F .onMorphism g) ⟩
    (E Category.then G .onMorphism (F .onMorphism f))
      (G .onMorphism (F .onMorphism g)) ∎
{-
  somewhatEq :
    ∀ {C} {s t s' t' : Category.Object C} →
    s ≡ s' → t ≡ t' →
    (f : Category.Morphism C s t) →
    (g : Category.Morphism C s' t') →
    Set
  somewhatEq refl refl f g = f ≡ g

  functorEq : ∀ {C D} (F G : Functor C D) →
    (eqOnObject : ∀ {s} → F .onObject s ≡ G .onObject s) →
    (∀ {s t} (f : Category.Morphism C s t) →
       somewhatEq eqOnObject eqOnObject (F .onMorphism f) (G .onMorphism f)) →
    F ≡ G
  functorEq = {!!}

  CAT : Category
  CAT .Category.Object = Category
  CAT .Category.Morphism = Functor
  CAT .Category._then_ = THEN
  CAT .Category.identity = ID
  CAT .Category.then-assoc = {!!}
  CAT .Category.then-identity = {!!}
  CAT .Category.identity-then = {!!}
-}












---------------------------------------------------------------------------
-- Revisiting syntax & semantics
---------------------------------------------------------------------------
