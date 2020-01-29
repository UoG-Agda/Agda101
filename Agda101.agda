module Agda101 where

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

-- Introduce most common key bindings

modus-ponens : ∀ {P Q : Set} → P → (P → Q) → Q
modus-ponens P P→Q = P→Q P

¬_ : Set → Set
¬ P = P → ⊥

contra-elim : ∀ {P : Set} → P → ¬ P → ⊥
contra-elim = modus-ponens

no-dne : ∀ {P : Set} → ¬ ¬ P → P
no-dne ¬¬P = {!!}

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
m + n = {!!}

_isEven : ℕ → Set
zero isEven = ⊤
(suc zero) isEven = ⊥
(suc (suc n)) isEven = n isEven

half : (n : ℕ) (p : n isEven) → ℕ
half zero tt = zero
half (suc zero) () -- we don't need this
half (suc (suc n)) p = suc (half n p)

_ : ℕ
_ = half 8 tt

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

_++_ : ∀ {A : Set} → List A → List A → List A
xs ++ ys = {!!}

brexit : ⊥
brexit = brexit

data Vec (A : Set) : ℕ → Set where
  []  : Vec A 0
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)
  
zipWith : ∀ {A B C : Set} {n} (f : A → B → C)
        → Vec A n → Vec B n → Vec C n
zipWith f xs ys = {!!}

-- Σ & ⊎ (no lem, lem irrefutable)

-- Propositional hom equality

-- ≡-trans, ≡-sym

-- Lists of units and nats are isomorphic

-- Fin

-- Constructive leq
