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
  to = foldr-ℕ (tt ∷_) []

  from : List ⊤ → ℕ
  from = foldr-List (λ _ → suc) 0

  from∘to : ∀ x → (from ∘ to) x ≡ x
  from∘to zero = refl
  from∘to (suc x) = cong suc (from∘to x)

  to∘from : ∀ x → (to ∘ from) x ≡ x
  to∘from [] = refl
  to∘from (tt ∷ xs) = cong (tt ∷_) (to∘from xs)

ℕ↔Even : ℕ ↔ Σ ℕ _isEven
ℕ↔Even = Isomorphism to from from∘to to∘from
  where

  to : ℕ → Σ ℕ _isEven
  to zero = zero , tt
  to (suc n) with to n
  to (suc n) | (2n , 2nEven) = (suc (suc 2n) , 2nEven)

  from : (Σ ℕ _isEven) → ℕ
  from (n , nEven) = half n nEven

  from∘to : ∀ x → (from ∘ to) x ≡ x
  from∘to zero = refl
  from∘to (suc n) with to n | from∘to n
  from∘to (suc .(half (proj₁ q) (proj₂ q))) | q | refl = refl

  to∘from : ∀ x → (to ∘ from) x ≡ x
  to∘from (zero , tt) = refl
  to∘from (suc (suc n) , nEven) rewrite to∘from (n , nEven) = refl

data Fin : ℕ → Set where
  zero : ∀ {n} → Fin (suc n)
  suc : ∀ {n} → Fin n → Fin (suc n)

noFin0 : Fin 0 → ⊥
noFin0 ()

open Vec
lookup : ∀ {n} {A : Set} → Vec A n → Fin n → A
lookup (x ∷ xs) zero = x
lookup (x ∷ xs) (suc i) = lookup xs i

-- For next time:
-- Fin
-- Constructive leq
