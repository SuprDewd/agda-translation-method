------------------------------------------------------------------------
-- The Translate library
--
-- Translating Fibonacci-related identities
------------------------------------------------------------------------

module Translate.Fibonacci where

open import Translate.Base
open import Translate.Support

-- Enumeration

ℕfib : ℕ → ℕ
ℕfib 0 = 1
ℕfib 1 = 1
ℕfib (ℕsuc (ℕsuc n)) = ℕfib (ℕsuc n) ℕ+ ℕfib n

-- Combinatorial interpretation

data FibStr : ℕ → Set where
  [] : FibStr ℕzero
  _∷1 : ∀ {n} → FibStr n → FibStr (ℕsuc n)
  _∷2 : ∀ {n} → FibStr n → FibStr (ℕsuc (ℕsuc n))

-- Expressions

:fib : ∀ {n} → :Expr n → :Expr n
:fib n = record
  { :value = λ Γ → ♯ ℕfib (:value n Γ)
  ; :lift = λ Γ → ♯ FibStr (:value n Γ)
  }

fib : ℕ → Expr
fib n = record
  { value = ♯ ℕfib n
  ; lift = ♯ FibStr n
  }

-- Axioms

fib-def : ∀ {n} → fib (ℕsuc (ℕsuc n)) ≡ fib (ℕsuc n) + fib n
fib-def {n} = axiom Prefl (mkBij to from)
  where
    to : lift (fib (ℕsuc (ℕsuc n))) → lift (fib (ℕsuc n) + fib n)
    to (xs ∷1) = inj₁ xs
    to (xs ∷2) = inj₂ xs

    from : lift (fib (ℕsuc n) + fib n) → lift (fib (ℕsuc (ℕsuc n)))
    from (inj₁ xs) = xs ∷1
    from (inj₂ xs) = xs ∷2
