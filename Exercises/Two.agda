module Two where

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

import Data.Nat as ℕ
import Data.Nat.Properties as ℕₚ

open ℕ using (ℕ; zero; suc; _+_)

-- Our language consists of constants and addition
data Expr : Set where
  const : ℕ → Expr
  plus : Expr → Expr → Expr

-- Straightforward semantics
eval-expr : Expr → ℕ
eval-expr (const n) = n
eval-expr (plus e1 e2) = eval-expr e1 + eval-expr e2

-- Tail recursive semantics
eval-expr-tail' : Expr → ℕ → ℕ
eval-expr-tail' (const n) acc = n + acc
eval-expr-tail' (plus e1 e2) acc = eval-expr-tail' e2 (eval-expr-tail' e1 acc)

eval-expr-tail : Expr → ℕ
eval-expr-tail e = eval-expr-tail' e 0

--
-- Task: prove that eval-expr-tail is equivalent to eval-expr.
--

-- The tail recursive evaluation does not depend on its accumulator
eval-expr-tail-correct-lemma : ∀ e acc → eval-expr-tail' e acc ≡ eval-expr-tail' e 0 + acc
eval-expr-tail-correct-lemma e acc = ?

-- The tail recursive evaluation agrees with the straightforward evaluation
eval-expr-tail-correct : ∀ e → eval-expr-tail e ≡ eval-expr e
eval-expr-tail-correct e = ?
