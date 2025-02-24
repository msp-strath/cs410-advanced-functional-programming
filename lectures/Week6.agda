module Week6 where

open import Data.Nat.Base using (ℕ; _+_)
open import Data.Bool.Base using (Bool; if_then_else_)
open import Data.List.Base using (List; []; _∷_)

data Ty : Set where
  bool nat : Ty



infix 0 _∈_
data _∈_ {A : Set} (a : A) : List A → Set where
--  nonsense : a ∈ []
  here  : ∀ {xs} → a ∈ (a ∷ xs)
  there : ∀ {x xs} → a ∈ xs → a ∈ (x ∷ xs)

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

TVal : Ty → Set
TVal bool = Bool
TVal nat = ℕ

Env : (Γ : List Ty) → Set
Env Γ = (x : Ty) → x ∈ Γ → TVal x

teval : forall {T Γ} -> Env Γ → TExpr Γ T -> TVal T
teval {T} ρ (var x) = ρ T x
teval ρ (nat n) = n
teval ρ (bool b) = b
teval ρ (add en em) = teval ρ en + teval ρ em
teval ρ (ifte eb et ee) = if teval ρ eb then teval ρ et else teval ρ ee
