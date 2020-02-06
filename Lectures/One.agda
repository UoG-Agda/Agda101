module Lectures.One where

-- Check background color
-- Check fontsize
-- Ask questions at *any* time

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

absurd : ⊥ → {P : Set} → P
absurd ()

-- Introduce most common key bindings
-- C-c C-l     load
-- C-c C-,     show context
-- C-c C-.     show context + type
-- C-c C-SPACE input
-- C-c C-A     auto
-- C-c C-r     refine
-- C-c C-d     type inference
-- C-c C-c     pattern match

-- Briefly introduce syntax
-- Introduce Set 0

modus-ponens : {P Q : Set} → P → (P → Q) → Q
modus-ponens p f = f p

-- Introduce misfix operators

¬_ : Set → Set
¬ P = P → ⊥

contra-elim : {P : Set} → P → ¬ P → ⊥
contra-elim = modus-ponens

-- no-dne : {P : Set} → ¬ ¬ P → P
-- no-dne ¬¬P = {!!}

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

_isEven : ℕ → Set
zero isEven = ⊤
suc zero isEven = ⊥
suc (suc n) isEven = n isEven

half : (n : ℕ) → n isEven → ℕ
half zero tt = zero
half (suc (suc n)) p = suc (half n p)

_ : ℕ
_ = half 8 tt

-- Comment on termination checking

-- brexit : ⊥
-- brexit = brexit
