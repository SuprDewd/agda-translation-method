
module Translate.Types where

open import Translate.Support
open import Function
open import Coinduction

-- mutual

  -- An expression
  -- record Expr : Set₁ where
  --   inductive
  --   field
  --     value : ∞ ℕ
  --     lift : Set
  --     -- expand : ∞ Polynomial

  -- data Polynomial : Set₁ where
  --   ∗atom : (x : Expr) → Polynomial
  --   -- ∗var : Fin ℕzero → Polynomial
  --   ∗zero : Polynomial
  --   ∗suc : (x : Polynomial) → Polynomial
  --   _∗+_ : (x y : Polynomial) → Polynomial
  --   _∗*_ : (x y : Polynomial) → Polynomial

-- An environment with n variables
-- Env : ∀ n → Set₁
-- Env n = Vec Expr n

-- Some shortcuts for ♭

-- value : Expr → ℕ
-- value e = ♭ $ Expr.value e

-- lift : Expr → Set
-- lift e = Expr.lift e

-- expand : Expr → Polynomial
-- expand e = ♭ $ Expr.expand e

-- Helpers for converting between zero-variable Expressions and Polynomials

-- mutual

  -- expr : :Expr ℕzero → Expr
  -- expr x = record
  --   { value = ♯ :value x []
  --   ; lift = ♯ :lift x []
  --   ; expand = ♯ polynomial (:expand x)
  --   }

  -- :expr : Expr → :Expr ℕzero
  -- :expr x = record
  --   { :value = λ Γ → ♯ value x
  --   ; :lift = λ Γ → ♯ lift x
  --   ; :expand = ♯ (:polynomial (expand x))
  --   ; :semantics = λ Γ → ♯ x
  --   }

  -- polynomial : :Polynomial ℕzero → Polynomial
  -- polynomial (∗atom x) = ∗atom (expr x)
  -- polynomial (∗var ())
  -- polynomial ∗zero = ∗zero
  -- polynomial (∗suc x) = ∗suc (polynomial x)
  -- polynomial (x ∗+ y) = (polynomial x) ∗+ (polynomial y)
  -- polynomial (x ∗* y) = (polynomial x) ∗* (polynomial y)

  -- :polynomial : Polynomial → :Polynomial ℕzero
  -- :polynomial (∗atom x) = ∗atom (:expr x)
  -- :polynomial ∗zero = ∗zero
  -- :polynomial (∗suc x) = ∗suc (:polynomial x)
  -- :polynomial (x ∗+ y) = (:polynomial x) ∗+ (:polynomial y)
  -- :polynomial (x ∗* y) = (:polynomial x) ∗* (:polynomial y)


infixl 6 _*_
infixl 5 _+_

data Fun : Set where
  fib' : (n : ℕ) → Fun
  2^' : (n : ℕ) → Fun

data Expr : Set where
  zero : Expr
  suc : (x : Expr) → Expr
  _+_ : (l r : Expr) → Expr
  _*_ : (l r : Expr) → Expr
  fun : (f : Fun) → Expr

fib : ℕ → Expr
fib n = fun (fib' n)

2^ : ℕ → Expr
2^ n = fun (2^' n)

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

------------------------------------------------------------------------
-- Evaluating and lifting

valueF : Fun → ℕ
valueF (fib' n) = ℕfib n
valueF (2^' n) = ℕ2^ n

liftF : Fun → Set
liftF (fib' n) = FibStr n
liftF (2^' n) = BinStr n

value : Expr → ℕ
value zero = ℕzero
value (suc x) = ℕsuc (value x)
value (l + r) = value l ℕ+ value r
value (l * r) = value l ℕ* value r
value (fun f) = valueF f

lift : Expr → Set
lift zero = Fin (ℕzero)
lift (suc x) = Maybe (lift x)
lift (l + r) = lift l ⊎ lift r
lift (l * r) = lift l × lift r
lift (fun f) = liftF f

