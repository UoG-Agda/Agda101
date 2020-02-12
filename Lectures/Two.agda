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

module List {ℓ} where

  data List (A : Set ℓ) : Set ℓ where
    [] : List A
    _∷_ : A → List A → List A

  _++_ : {A : Set ℓ} → List A → List A → List A
  [] ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

  map : {A B : Set ℓ} → (A → B) → List A → List B
  map f [] = []
  map f (x ∷ xs) = f x ∷ map f xs

open List using (List; []; _∷_)

_ : List ℕ
_ = 0 ∷ (1 ∷ (2 ∷ []))

-- Introduce type families

module Vec where
  data Vec (A : Set) : ℕ → Set where
    []  : Vec A zero
    _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

  head : ∀ {A n} → Vec A (suc n) → A
  head (x ∷ xs) = x

  _++_ : ∀ {A n m} → Vec A n → Vec A m → Vec A (n + m)
  [] ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

  map : ∀ {A B n} → (A → B) → Vec A n → Vec B n
  map f [] = []
  map f (x ∷ xs) = f x ∷ map f xs

  zipWith : ∀ {A B C : Set} {n} (f : A → B → C)
          → Vec A n → Vec B n → Vec C n
  zipWith f [] [] = []
  zipWith f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWith f xs ys

--  \u+
data _⊎_ (A : Set) (B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

Dec : Set → Set
Dec B = B ⊎ (¬ B)

data _×'_ (A : Set) (B : Set) : Set where
  _,'_ : A → B → A ×' B

record _×''_ (A : Set) (B : Set) : Set where
  constructor _,''_
  field
    proj₁ : A
    proj₂ : B

-- \Sigma
record Σ {ℓ} (A : Set ℓ) (B : A → Set ℓ) : Set ℓ where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

_ : Σ ℕ _isEven
_ = 0 , tt

_×_ : Set → Set → Set
A × B = Σ A λ _ → B
