open import Lectures.One
open import Lectures.Three

module Exercises.One where

_*_ : ℕ → ℕ → ℕ
zero * y = zero
suc x * y = y + (x * y)

-- Prove that multiplication is commutative
*-idʳ : ∀ x → x * 0 ≡ x
*-suc : ∀ x y → x + (x * y) ≡ (x * suc y)
*-comm : ∀ x y → x * y ≡ y * x

-- Prove that if x + x ≡ y + y then x ≡ y (taken from CodeWars)
suc-injective : ∀ x y → suc x ≡ suc y → x ≡ y
xxyy : ∀ x y → x + x ≡ y + y → x ≡ y
