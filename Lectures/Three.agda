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

