------------------------------------------------------------------------
-- The Translate library
--
-- Expressions for various combinatorial structures
------------------------------------------------------------------------

module Translate.Combinatorics where

open import Translate.Base
open import Translate.Semiring
open import Translate.Support
open import Translate.Types
open import Function
import Data.Fin as F

infixr 7 _^_
-- TODO: infix? ? ∷

------------------------------------------------------------------------
-- Fibonacci strings

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

fib : ℕ → Expr
fib n = record
  { value = ♯ ℕfib n
  ; lift = FibStr n
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

------------------------------------------------------------------------
-- Binary strings

-- Enumeration

ℕ2^ : ℕ → ℕ
ℕ2^ 0 = 1
ℕ2^ (ℕsuc n) = ℕ2^ n ℕ+ ℕ2^ n

-- Combinatorial interpretation

data BinStr : ℕ → Set where
  [] : BinStr ℕzero
  _∷_ : ∀ {n} → Fin 2 → BinStr n → BinStr (ℕsuc n)

-- Expressions

2^ : ℕ → Expr
2^ n = record
  { value = ♯ ℕ2^ n
  ; lift = BinStr n
  }

-- Axioms

2^-def : ∀ {n} → 2^ (ℕsuc n) ≡ 2^ n + 2^ n
2^-def {n} = axiom Prefl $ mkBij
  (λ { (Fzero ∷ xs) → inj₁ xs
     ; (Fsuc Fzero ∷ xs) → inj₂ xs
     ; (Fsuc (Fsuc ()) ∷ _)
     })
  (λ { (inj₁ xs) → Fzero ∷ xs
     ; (inj₂ xs) → Fsuc Fzero ∷ xs
     })

------------------------------------------------------------------------
-- K-ary strings

-- Enumeration

_ℕ^_ : ℕ → ℕ → ℕ
k ℕ^ ℕzero = 1
k ℕ^ ℕsuc n = k ℕ* (k ℕ^ n)

-- Combinatorial interpretation

data K-aryStr (k : ℕ) : ℕ → Set where
  [] : K-aryStr k ℕzero
  _∷_ : ∀ {n} → Fin k → K-aryStr k n → K-aryStr k (ℕsuc n)

-- Expressions

_^_ : ℕ → ℕ → Expr
k ^ n = record
  { value = ♯ (k ℕ^ n)
  ; lift = K-aryStr k n
  }

-- Axioms

^-def : ∀ {n} k → k ^ (ℕsuc n) ≡ (fin k) * (k ^ n)
^-def {n} k = axiom Prefl $ mkBij
  (λ { (x ∷ xs) → x , xs })
  (λ { (x , xs) → x ∷ xs })

------------------------------------------------------------------------
-- Binary strings with a given number of ones

-- Enumeration

-- TODO: Make a decidable version of this?
try-lower : ∀ {n} → Fin (ℕsuc n) → Maybe (Fin n)
try-lower {ℕzero} Fzero = nothing -- There is nothing in Fin 0
try-lower {ℕzero} (Fsuc ())
try-lower {ℕsuc n} Fzero = just Fzero
try-lower {ℕsuc n} (Fsuc k) with try-lower {n} k
try-lower {ℕsuc n} (Fsuc k) | just x = just (Fsuc x)
try-lower {ℕsuc n} (Fsuc k) | nothing = nothing

ℕbin : (n : ℕ) → (k : Fin (ℕsuc n)) → ℕ
ℕbin _ Fzero = 1
ℕbin ℕzero (Fsuc ())
ℕbin (ℕsuc n) (Fsuc k) with try-lower (Fsuc k)
ℕbin (ℕsuc n) (Fsuc k) | just x = ℕbin n k ℕ+ ℕbin n x
ℕbin (ℕsuc n) (Fsuc k) | nothing = ℕbin n k

-- Combinatorial interpretation

data Binomial : (n : ℕ) → (k : Fin (ℕsuc n)) → Set where
  [] : Binomial ℕzero Fzero
  0∷_ : ∀ {n k} → Binomial n k → Binomial (ℕsuc n) (F.inject₁ k)
  1∷_ : ∀ {n k} → Binomial n k → Binomial (ℕsuc n) (F.raise 1 k)

-- Expressions

bin : (n : ℕ) → (k : Fin (ℕsuc n)) → Expr
bin n k = record
  { value = ♯ ℕbin n k
  ; lift = Binomial n k
  }

-- Axioms

-- TODO: How should we implement this?
-- bin-def : ∀ n k → ?
-- bin-def n k = ?

------------------------------------------------------------------------
-- Dyck paths

-- Enumeration

-- TODO: How should we implement this?
-- ℕcat : ℕ → ℕ
-- ℕcat n = {!!}

-- Combinatorial interpretation

-- data DyckPath : ℕ → Set where
--   empty : DyckPath ℕzero
--   right : ∀ {n} → DyckPath n → DyckPath (ℕsuc n)
--   up : ∀ {n k} → DyckPath n → DyckPath k → DyckPath (2 ℕ+ n ℕ+ k)

-- Expressions

-- cat : ℕ → Expr
-- cat n = record
--   { value = ♯ ℕcat n
--   ; lift = DyckPath n
--   }

-- Axioms

-- TODO: How should we implement this?
-- cat : ∀ n k → ?
-- cat n k = ?

