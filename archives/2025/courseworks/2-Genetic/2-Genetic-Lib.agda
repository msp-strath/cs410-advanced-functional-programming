------------------------------------------------------------------------
-- This is a supporting library for the 2-Genetic project.
-- Turns out the standard library did not quite have enough things.

module 2-Genetic-Lib where

open import Algebra.Bundles.Raw using (RawRing)
open import Algebra.Bundles using (Ring)

open import Data.Bool.Base using (true; false)
open import Data.Integer.Base as ℤ using (ℤ; +_; -[1+_])
open import Data.Nat.Base as ℕ using (ℕ; zero; suc)
import Data.Nat.Properties as ℕ

open import Level using (0ℓ)

open import Relation.Nullary using (does; ofⁿ; ofʸ)

module Injection {c e} (R : RawRing c e) where

  open RawRing R

  fromℕ′ : ℕ → Carrier
  fromℕ′ zero = 0#
  fromℕ′ (suc n) = 1# + fromℕ′ n

  fromℤ′ : ℤ → Carrier
  fromℤ′ (+ n) = fromℕ′ n
  fromℤ′ -[1+ n ] = - (1# + fromℕ′ n)


module InjectionCorrect {c e} (R : Ring c e) where

  open Ring R
  open Injection rawRing

  open import Algebra.Properties.Group +-group
  open import Relation.Binary.Reasoning.Setoid setoid

  fromℕ′-+-homo : ∀ m n → fromℕ′ (m ℕ.+ n) ≈ fromℕ′ m + fromℕ′ n
  fromℕ′-+-homo zero n = sym (+-identityˡ (fromℕ′ n))
  fromℕ′-+-homo (suc m) n = begin
    fromℕ′ (suc m ℕ.+ n)       ≡⟨⟩
    1# + fromℕ′  (m ℕ.+ n)     ≈⟨ +-congˡ (fromℕ′-+-homo m n) ⟩
    1# + (fromℕ′ m + fromℕ′ n) ≈⟨ sym (+-assoc 1# (fromℕ′ m) (fromℕ′ n)) ⟩
    1# + fromℕ′ m + fromℕ′ n   ≡⟨⟩
    fromℕ′ (suc m) + fromℕ′ n  ∎

  fromℕ′-∸-homo : ∀ {m n} → n ℕ.≤ m → fromℕ′ (m ℕ.∸ n) ≈ fromℕ′ m - fromℕ′ n
  fromℕ′-∸-homo {m} ℕ.z≤n = begin
    fromℕ′ (m ℕ.∸ 0)    ≡⟨⟩
    fromℕ′ m            ≈⟨ sym (+-identityʳ (fromℕ′ m)) ⟩
    fromℕ′ m + 0#       ≈⟨ +-congˡ (uniqueˡ-⁻¹ 0# 0# (+-identityʳ 0#)) ⟩
    fromℕ′ m + - 0#     ≡⟨⟩
    fromℕ′ m - fromℕ′ 0 ∎
  fromℕ′-∸-homo {m = suc m} {n = suc n} (ℕ.s≤s m≤n) = begin
    fromℕ′ (suc m ℕ.∸ suc n)
      ≡⟨⟩
    fromℕ′ (m ℕ.∸ n)
      ≈⟨ fromℕ′-∸-homo m≤n ⟩
    fromℕ′ m - fromℕ′ n
      ≈⟨ +-congˡ (sym (+-identityˡ (- fromℕ′ n))) ⟩
    fromℕ′ m + (0# - fromℕ′ n)
      ≈⟨ +-congˡ (+-congʳ (sym (-‿inverseʳ 1#))) ⟩
    fromℕ′ m + ((1# - 1#) + - fromℕ′ n)
      ≈⟨ +-congˡ (+-assoc 1# (- 1#) (- fromℕ′ n)) ⟩
    fromℕ′ m + (1# + (- 1# + - fromℕ′ n))
      ≈⟨ sym (+-assoc (fromℕ′ m) 1# (- 1# + - fromℕ′ n)) ⟩
    (fromℕ′ m + 1#) + (- 1# + - fromℕ′ n)
      ≈⟨ +-congˡ (+-comm (- 1#) (- fromℕ′ n)) ⟩
    (fromℕ′ m + 1#) + (- fromℕ′ n + - 1#)
      ≈⟨ +-cong (+-comm (fromℕ′ m) 1#) (sym (⁻¹-anti-homo-∙ 1# (fromℕ′ n))) ⟩
    (1# + fromℕ′ m) + - (1# + fromℕ′ n)
      ≡⟨⟩
    fromℕ′ (suc m) - fromℕ′ (suc n)
      ∎

  fromℤ′‿-‿homo : ∀ i → fromℤ′ (ℤ.- i) ≈ - (fromℤ′ i)
  fromℤ′‿-‿homo (+  zero) = sym ε⁻¹≈ε
  fromℤ′‿-‿homo (+ suc n) = refl
  fromℤ′‿-‿homo -[1+ n ]  = sym (⁻¹-involutive (fromℕ′ (suc n)))

  fromℤ′-⊖ : ∀ m n → fromℤ′ (m ℤ.⊖ n) ≈ fromℕ′ m - fromℕ′ n
  fromℤ′-⊖ m n with m ℕ.<ᵇ n | ℕ.<ᵇ-reflects-< m n
  ... | false | ofⁿ ¬p = fromℕ′-∸-homo (ℕ.≮⇒≥ ¬p)
  ... | true  | ofʸ p  = begin
    fromℤ′ (ℤ.- (+ (n ℕ.∸ m))) ≈⟨ fromℤ′‿-‿homo (+ (n ℕ.∸ m)) ⟩
    - fromℤ′ (+ (n ℕ.∸ m))     ≈⟨ -‿cong (fromℕ′-∸-homo (ℕ.<⇒≤ p)) ⟩
    - (fromℕ′ n - fromℕ′ m)    ≈⟨ ⁻¹-anti-homo-// (fromℕ′ n) (fromℕ′ m) ⟩
    fromℕ′ m - fromℕ′ n        ∎

  fromℤ′-+-homo : ∀ i j → fromℤ′ (i ℤ.+ j) ≈ fromℤ′ i + fromℤ′ j
  fromℤ′-+-homo (+ m)    (+ n)    = fromℕ′-+-homo m n
  fromℤ′-+-homo (+ m)    -[1+ n ] = begin
    fromℤ′ (+ m ℤ.+ -[1+ n ])      ≡⟨⟩
    fromℤ′ (m ℤ.⊖ suc n)           ≈⟨ fromℤ′-⊖ m (suc n) ⟩
    fromℕ′ m + - fromℕ′ (suc n)    ≡⟨⟩
    fromℤ′ (+ m) + fromℤ′ -[1+ n ] ∎
  fromℤ′-+-homo -[1+ m ] (+ n)    = begin
    fromℤ′ (-[1+ m ] ℤ.+ + n)      ≡⟨⟩
    fromℤ′ (n ℤ.⊖ suc m)           ≈⟨ fromℤ′-⊖ n (suc m) ⟩
    fromℕ′ n - fromℕ′ (suc m)      ≈⟨ +-comm (fromℕ′ n) (- fromℕ′ (suc m)) ⟩
    - fromℕ′ (suc m) + fromℕ′ n    ≡⟨⟩
    fromℤ′ -[1+ m ] + fromℤ′ (+ n) ∎
  fromℤ′-+-homo -[1+ m ] -[1+ n ] = begin
    fromℤ′ (-[1+ m ] ℤ.+ -[1+ n ])
      ≡⟨⟩
    - (1# + (1# + fromℕ′ (m ℕ.+ n)))
      ≈⟨ -‿cong (+-congˡ (+-congˡ (fromℕ′-+-homo m n))) ⟩
    - (1# + (1# + (fromℕ′ m + fromℕ′ n)))
      ≈⟨ -‿cong (+-congˡ (sym (+-assoc 1# (fromℕ′ m) (fromℕ′ n)))) ⟩
    - (1# + (1# + fromℕ′ m + fromℕ′ n))
      ≡⟨⟩
    - (1# + (fromℕ′ (suc m) + fromℕ′ n))
      ≈⟨ -‿cong (sym (+-assoc 1# (fromℕ′ (suc m)) (fromℕ′ n))) ⟩
    - (1# + fromℕ′ (suc m) + fromℕ′ n)
      ≈⟨ -‿cong (+-congʳ (+-comm 1# (fromℕ′ (suc m)))) ⟩
    - (fromℕ′ (suc m) + 1# + fromℕ′ n)
      ≈⟨ -‿cong (+-assoc (fromℕ′ (suc m)) 1# (fromℕ′ n)) ⟩
    - (fromℕ′ (suc m) + (1# + fromℕ′ n))
      ≡⟨⟩
    - (fromℕ′ (suc m) + fromℕ′ (suc n))
      ≈⟨ ⁻¹-anti-homo-∙ (fromℕ′ (suc m)) (fromℕ′ (suc n)) ⟩
    - fromℕ′ (suc n) + - fromℕ′ (suc m)
      ≈⟨ +-comm (- fromℕ′ (suc n)) (- fromℕ′ (suc m)) ⟩
    - fromℕ′ (suc m) + - fromℕ′ (suc n)
      ≡⟨⟩
    fromℤ′ -[1+ m ] + fromℤ′ -[1+ n ] ∎
