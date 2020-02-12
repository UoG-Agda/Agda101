module Lectures.Three where

open import Lectures.One
open import Lectures.Two

-- Introduce propositional equality

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

-- Comment on precendences
infix 10 _≡_

record Equivalence (_~_ : ∀ {A : Set} → A → A → Set) : Set₁ where
  field
    reflexive  : ∀ {A} {a : A} → a ~ a
    symmetric  : ∀ {A} {a b : A} → a ~ b → b ~ a
    transitive : ∀ {A} {a b c : A} → a ~ b → b ~ c → a ~ c

open Equivalence

sym : ∀ {A} {a b : A} → a ≡ b → b ≡ a
sym eq = {!!}

trans : ∀ {A} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans eq qe = {!!}

-- Comment on copatterns
≡-Equivalence : Equivalence _≡_
reflexive ≡-Equivalence = refl
symmetric ≡-Equivalence = sym
transitive ≡-Equivalence = trans

cong : ∀ {A B} {a b : A} → (f : A → B) → a ≡ b → f a ≡ f b
cong f eq = {!!}

-- Leibniz equality?
subst : ∀ {A} {x y : A} {P : A → Set} → P x → x ≡ y → P y
subst p eq = {!!}

_ : _+_ ≡ _+_
_ = refl

_ : _+_ ≡ λ x y → y + x
_ = {!refl!}

-- Comment on postulates
postulate
  extensionality : {A B : Set} {f g : A → B} → (∀ x → f x ≡ g x) → f ≡ g

+-idʳ : ∀ x → x ≡ x + 0
+-idʳ x = {!!}

+-suc : ∀ x y → suc (x + y) ≡ x + suc y
+-suc x y = {!!}

+-comm : ∀ x y → x + y ≡ y + x
+-comm x y = {!!}

_∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
(f ∘ g) x = f (g x)

record Isomorphism (A B : Set) : Set where
  constructor _↔_
  field
    to : A → B
    from : B → A
    from∘to : ∀ {x} → (from ∘ to) x ≡ x
    to∘from : ∀ {y} → (to ∘ from) y ≡ y

open Isomorphism
open List

ℕ↔List⊤ : Isomorphism ℕ (List ⊤)
to ℕ↔List⊤ = {!!}
from ℕ↔List⊤ = {!!}
from∘to ℕ↔List⊤ = {!!}
to∘from ℕ↔List⊤ = {!!}

ℕ↔Even : Isomorphism ℕ (Σ ℕ _isEven)
to ℕ↔Even = {!!}
from ℕ↔Even = {!!}
from∘to ℕ↔Even = {!!}
to∘from ℕ↔Even = {!!}

-- For next time:
-- Fin
-- Constructive leq
