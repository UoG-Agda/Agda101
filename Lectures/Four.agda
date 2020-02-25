module Lectures.Four where

open import Lectures.One public
open import Lectures.Two public
open import Lectures.Three public

_∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
(f ∘ g) x = f (g x)

record _↔_ (A B : Set) : Set where
  constructor Isomorphism
  field
    to : A → B
    from : B → A
    from∘to : ∀ x → (from ∘ to) x ≡ x
    to∘from : ∀ y → (to ∘ from) y ≡ y

open List

foldr-List : {A B : Set} → (A → B → B) → B → List A → B
foldr-List f z [] = z
foldr-List f z (x ∷ xs) = f x (foldr-List f z xs)

foldr-ℕ : {A : Set} → (A → A) → A → ℕ → A
foldr-ℕ f z zero = z
foldr-ℕ f z (suc n) = f (foldr-ℕ f z n)

ℕ↔List⊤ : ℕ ↔ List ⊤
ℕ↔List⊤ = Isomorphism to from from∘to to∘from
  where

  to : ℕ → List ⊤
  from : List ⊤ → ℕ -- use a lambda
  from∘to : ∀ x → (from ∘ to) x ≡ x -- by cong
  to∘from : ∀ x → (to ∘ from) x ≡ x -- by cong, importance of pattern matching on x ↦ tt

ℕ↔Even : ℕ ↔ Σ ℕ _isEven
ℕ↔Even = Isomorphism to from from∘to to∘from
  where

  to : ℕ → Σ ℕ _isEven -- with with
  from : (Σ ℕ _isEven) → ℕ -- lambda pattern match
  from∘to : ∀ x → (from ∘ to) x ≡ x -- introduce rewrite
  to∘from : ∀ x → (to ∘ from) x ≡ x -- comment on equality on record types

-- For next time:
-- Fin
-- Constructive leq
