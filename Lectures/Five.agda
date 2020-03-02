{-# OPTIONS --safe #-}
module Five where

open import Relation.Binary.PropositionalEquality
open import Data.Nat.Properties
open import Data.List.Properties
open import Data.Nat public
open import Data.List public
open import Data.Product

data Expr : Set where
  const : ℕ → Expr
  plus : Expr → Expr → Expr

eval-expr : Expr → ℕ
eval-expr (const n) = n
eval-expr (plus e1 e2) = eval-expr e1 + eval-expr e2

eval-expr-tail' : Expr → ℕ → ℕ
eval-expr-tail' (const n) acc = n + acc
eval-expr-tail' (plus e1 e2) acc = eval-expr-tail' e2 (eval-expr-tail' e1 acc)

eval-expr-tail : Expr → ℕ
eval-expr-tail e = eval-expr-tail' e 0

data Instr : Set where
  push : ℕ → Instr
  add : Instr

Prog = List Instr

Stack = List ℕ

run : Prog → Stack → Stack
run [] s = s
run (push n ∷ p) s = run p (n ∷ s)
run (add ∷ p) (a1 ∷ a2 ∷ s) = run p (a1 + a2 ∷ s)
run (add ∷ p) s = run p s

compile : Expr → Prog
compile (const n) = push n ∷ []
compile (plus e1 e2) = compile e1 ++ compile e2 ++ add ∷ []

-- Task 1. Prove that eval-expr-tail is equivalent to eval-expr.
eval-expr-tail-correct-lemma : ∀ e acc → eval-expr-tail' e 0 + acc ≡ eval-expr-tail' e acc
eval-expr-tail-correct-lemma = {!!}

eval-expr-tail-correct : ∀ e → eval-expr-tail e ≡ eval-expr e
eval-expr-tail-correct = {!!}

-- Task 2. Prove that you get the expected result when you compile and run the program.
compile-correct-split : ∀ p q s → run (p ++ q) s ≡ run q (run p s)
compile-correct-split = {!!}

compile-correct-exist : ∀ e s → Σ ℕ (λ m → run (compile e) s ≡ m ∷ s)
compile-correct-exist = {!!}

compile-correct-gen : ∀ e s → run (compile e) s ≡ run (compile e) [] ++ s
compile-correct-gen = {!!}

compile-correct : ∀ e → run (compile e) [] ≡ eval-expr e ∷ []
compile-correct = {!!}
