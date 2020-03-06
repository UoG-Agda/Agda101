open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality 
open ≡-Reasoning
open import Data.Nat.Properties using (+-assoc; +-comm)

module Exercises.One where

_*_ : ℕ → ℕ → ℕ
zero * y = zero
suc x * y = y + (x * y)

-- Prove that multiplication is commutative
*-idʳ : ∀ x → x * 0 ≡ 0
*-idʳ zero = refl
*-idʳ (suc x) = *-idʳ x

*-suc : ∀ x y → x + (x * y) ≡ (x * suc y)
*-suc zero y = refl
*-suc (suc x) y
  rewrite sym (+-assoc x y (x * y)) | +-comm x y |
          +-assoc y x (x * y) | *-suc x y = refl

*-comm : ∀ x y → x * y ≡ y * x
*-comm zero y rewrite *-idʳ y = refl
*-comm (suc x) y rewrite *-comm x y | *-suc y x = refl

-- Prove that if x + x ≡ y + y then x ≡ y (taken from CodeWars)
suc-injective : ∀ x y → suc x ≡ suc y → x ≡ y
suc-injective zero zero p = refl
suc-injective (suc x) (suc .x) refl = refl

xxyy : ∀ x y → x + x ≡ y + y → x ≡ y
xxyy zero zero refl = refl
xxyy (suc x) (suc y) p rewrite +-comm x (suc x) | +-comm y (suc y) =
  cong suc (xxyy x y (suc-injective _ _ (suc-injective _ _ p)))
