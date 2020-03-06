module Five where

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

import Data.Nat as ℕ
import Data.Nat.Properties as ℕₚ
import Data.List as List
import Data.List.Properties as Listₚ
import Data.Product as Product

open List using (List; []; _∷_; _++_)
open ℕ using (ℕ; zero; suc; _+_)
open Product using (Σ; _,_)

-- Our language consists of constants and addition
data Expr : Set where
  const : ℕ → Expr
  plus : Expr → Expr → Expr

-- Straightforward semantics
eval-expr : Expr → ℕ
eval-expr (const n) = n
eval-expr (plus e1 e2) = eval-expr e1 + eval-expr e2

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

-- Task 2. Prove that you get the expected result when you compile and run the program.
compile-correct-split : ∀ p q s → run (p ++ q) s ≡ run q (run p s)
compile-correct-split = {!!}

compile-correct-exist : ∀ e s → Σ ℕ (λ m → run (compile e) s ≡ m ∷ s)
compile-correct-exist = {!!}

compile-correct-gen : ∀ e s → run (compile e) s ≡ run (compile e) [] ++ s
compile-correct-gen = {!!}

compile-correct : ∀ e → run (compile e) [] ≡ eval-expr e ∷ []
compile-correct = {!!}
