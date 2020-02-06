module Lectures.Two where

-- Introduce imports
open import Lectures.One

-- Introduce type parameters

module List-types where

  data List (A : Set₁) : Set₁ where
    []  : List A
    _∷_ : A → List A → List A

  _ : List Set
  _ = ⊥ ∷ (ℕ ∷ (⊤ ∷ []))

module List where

  data List (A : Set) : Set where
    [] : List A
    _∷_ : A → List A → List A

  _ : List ℕ
  _ = 0 ∷ (1 ∷ (2 ∷ []))

  _++_ : {A : Set} → List A → List A → List A
  xs ++ ys = {!!}

  map : {A B : Set} → (A → B) → List A → List B
  map f xs = {!!}

-- Introduce type families

module Vec where
  data Vec (A : Set) : ℕ → Set where
    []  : Vec A 0
    _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

  head : ∀ {A : Set} {n} → Vec A (suc n) → A
  head xs = {!!}

  _++_ : ∀ {A : Set} {n m} → Vec A n → Vec A m → Vec A (n + m)
  xs ++ ys = {!!}

  map : ∀ {A B : Set} {n} → (A → B) → Vec A n → Vec B n
  map f xs = {!!}

  zipWith : ∀ {A B C : Set} {n} (f : A → B → C)
          → Vec A n → Vec B n → Vec C n
  zipWith f xs ys = {!!}

-- For next time

-- Records
-- Σ & ⊎ (no lem, lem irrefutable, decidability)
-- Propositional hom equality
-- ≡-trans, ≡-sym, ≡-cong
-- Lists of units and nats are isomorphic
-- Fin
-- Constructive leq
