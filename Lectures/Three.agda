module Lectures.Three where

open import Lectures.One
open import Lectures.Two

-- Introduce propositional equality

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

-- Comment on precendences
infix 10 _≡_

record Equivalence (_~_ : ∀ {A : Set} → A → A → Set) : Set₁ where
  field
    reflexive  : ∀ {A} {a : A} → a ~ a
    symmetric  : ∀ {A} {a b : A} → a ~ b → b ~ a
    transitive : ∀ {A} {a b c : A} → a ~ b → b ~ c → a ~ c

open Equivalence

sym : ∀ {A} {a b : A} → a ≡ b → b ≡ a
sym refl = refl

trans : ∀ {A} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl refl = refl

-- Comment on copatterns
≡-Equivalence : Equivalence _≡_
reflexive ≡-Equivalence = refl
symmetric ≡-Equivalence = sym
transitive ≡-Equivalence = trans

cong : ∀ {A B} {a b : A} → (f : A → B) → a ≡ b → f a ≡ f b
cong f refl = refl

-- Leibniz equality?
subst : ∀ {A} {x y : A} {P : A → Set} → P x → x ≡ y → P y
subst p refl = p

_ : _+_ ≡ _+_
_ = refl

-- _ : _+_ ≡ λ x y → y + x
-- _ = {!refl!}

-- Comment on postulates
postulate
  extensionality : {A B : Set} {f g : A → B} → (∀ x → f x ≡ g x) → f ≡ g

+-idʳ : ∀ x → x ≡ x + 0
+-idʳ zero = refl
+-idʳ (suc x) = cong suc (+-idʳ _)

+-suc : ∀ x y → suc (x + y) ≡ x + suc y
+-suc zero y = refl
+-suc (suc x) y = cong suc (+-suc _ _)

+-comm : ∀ x y → x + y ≡ y + x
+-comm zero y = +-idʳ _
+-comm (suc x) y = trans (cong suc (+-comm x y)) (+-suc _ _)

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
