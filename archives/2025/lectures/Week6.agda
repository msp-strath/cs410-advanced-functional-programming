module Week6 where

open import Data.Empty using (⊥)
open import Data.Nat.Base using (ℕ; _+_)
open import Data.Bool.Base using (Bool; true; false;  if_then_else_)
open import Data.List.Base using (List; []; _∷_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data Ty : Set where
  bool nat : Ty



infix 0 _∈_
data _∈_ {A : Set} (a : A) : List A → Set where
--  nonsense : a ∈ []
  here  : ∀ {xs}            → a ∈ (a ∷ xs)
  there : ∀ {x xs} → a ∈ xs → a ∈ (x ∷ xs)

_ : 0 ∈ [] → ⊥
_ = λ ()

_ : 0 ∈ (0 ∷ 0 ∷ [])
_ = here


data TExpr (Γ : List Ty) : Ty -> Set where
  var : ∀ {σ} → σ ∈ Γ → TExpr Γ σ
  ------------------------ old same
  nat : ℕ -> TExpr Γ nat
  bool : Bool -> TExpr Γ bool
  add : TExpr Γ nat -> TExpr Γ nat ->
        -------------------------------------
        TExpr Γ nat
  ifte : forall {T} ->
         TExpr Γ bool ->
         TExpr Γ T -> TExpr Γ T ->
         ------------------------------------
         TExpr Γ T

boolToNat : TExpr (bool ∷ []) nat
boolToNat = ifte (var here) (nat 1) (nat 0)

double : ∀ {Γ} → nat ∈ Γ → TExpr Γ nat
double x = add (var x) (var x)

TVal : Ty → Set
TVal bool = Bool
TVal nat = ℕ

Env : (Γ : List Ty) → Set
Env Γ = (x : Ty) → x ∈ Γ → TVal x

myBool : Env (bool ∷ [])
myBool x here = false

myNats : Env (nat ∷ bool ∷ nat ∷ [])
myNats x here = 10
myNats x (there here) = false
myNats x (there (there here)) = 21

teval : forall {T Γ} ->
        TExpr Γ T ->         -- syntax
        (Env Γ → TVal T)     -- meaning
teval {T} (var x) ρ = ρ T x
teval (nat n) ρ = n
teval (bool b) ρ = b
teval (add en em) ρ = teval en ρ + teval em ρ
teval (ifte eb et ee) ρ = if teval eb ρ then teval et ρ else teval ee ρ

_ : teval boolToNat myBool ≡ 0
_ = refl

_ : teval (double here) myNats ≡ 20
_ = refl

_ : teval (double (there (there here))) myNats ≡ 21 + 21
_ = refl

boringIf : ∀ {Γ} → TExpr Γ nat
boringIf = ifte (bool true) (nat 0) (nat 1)

Transformation : Set
Transformation = ∀ {Γ T} → TExpr Γ T → TExpr Γ T


foldIf : Transformation
foldIf (var x) = var x
foldIf (nat n) = nat n
foldIf (bool b) = bool b
foldIf (add m n) = add (foldIf m) (foldIf n)
foldIf (ifte b l r) with foldIf b
... | bool lb = if lb then foldIf l else foldIf r  -- static -> if ... then ... else ...
... | b′      = ifte b′ (foldIf l) (foldIf r)      -- dynamic -> ifte

_≋_ : ∀ {Γ T} → TExpr Γ T → TExpr Γ T → Set
s ≋ t = (ρ : Env _) → teval s ρ ≡ teval t ρ

Correct : Transformation → Set
Correct transformation = ∀ {Γ T} (t : TExpr Γ T) → t ≋ transformation t

foldIf-correct : Correct foldIf
foldIf-correct (var x) ρ = refl
foldIf-correct (nat n) ρ = refl
foldIf-correct (bool b) ρ = refl
foldIf-correct (add m n) ρ rewrite foldIf-correct m ρ | foldIf-correct n ρ  = refl
foldIf-correct (ifte b l r) ρ with foldIf b | foldIf-correct b ρ
foldIf-correct (ifte b l r) ρ | bool lb | refl with teval b ρ
... | false = foldIf-correct r ρ
... | true = foldIf-correct l ρ
foldIf-correct (ifte b l r) ρ | var x | qq
  rewrite qq | foldIf-correct l ρ | foldIf-correct r ρ = refl
foldIf-correct (ifte b l r) ρ | ifte p p₁ p₂ | qq
  rewrite qq | foldIf-correct l ρ | foldIf-correct r ρ = refl


foldAdd : Transformation
foldAdd = {!!}

foldAdd-correct : Correct foldAdd
foldAdd-correct = {!!}
