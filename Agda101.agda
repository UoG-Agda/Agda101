module Agda101 where

-- Check background color
-- Check fontsize
-- Ask questions at *any* time

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

-- Introduce most common key bindings
-- Briefly introduce syntax
-- Introduce Set 0

modus-ponens : {P Q : Set} → P → (P → Q) → Q
modus-ponens P P→Q = P→Q P

-- Introduce misfix operators

¬_ : Set → Set
¬ P = P → ⊥

contra-elim : {P : Set} → P → ¬ P → ⊥
contra-elim = modus-ponens

no-dne : {P : Set} → ¬ ¬ P → P
no-dne ¬¬P = {!!}

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
m + n = {!!}

_isEven : ℕ → Set
n isEven = {!!}

half : (n : ℕ) (p : n isEven) → ℕ
half n = {!!}

_ : ℕ
_ = half 8 {!!}

-- Introduce type parameters

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

_++_ : {A : Set} → List A → List A → List A
xs ++ ys = {!!}

-- Comment on termination checking

brexit : ⊥
brexit = brexit

-- Introduce type families

data Vec (A : Set) : ℕ → Set where
  []  : Vec A 0
  -- Introduce foralls
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

zipWith : ∀ {A B C : Set} {n} (f : A → B → C)
        → Vec A n → Vec B n → Vec C n
zipWith f xs ys = {!!}


-- For next time

-- Records
-- Σ & ⊎ (no lem, lem irrefutable)
-- Propositional hom equality
-- ≡-trans, ≡-sym, ≡-cong
-- Lists of units and nats are isomorphic
-- Fin
-- Constructive leq
