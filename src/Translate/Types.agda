
module Translate.Types where

open import Translate.Support
open import Function
open import Coinduction

mutual

  -- An expression
  record Expr : Set₁ where
    inductive
    field
      value : ∞ ℕ
      lift : Set
      -- expand : ∞ Polynomial

  -- data Polynomial : Set₁ where
  --   ∗atom : (x : Expr) → Polynomial
  --   -- ∗var : Fin ℕzero → Polynomial
  --   ∗zero : Polynomial
  --   ∗suc : (x : Polynomial) → Polynomial
  --   _∗+_ : (x y : Polynomial) → Polynomial
  --   _∗*_ : (x y : Polynomial) → Polynomial

-- An environment with n variables
Env : ∀ n → Set₁
Env n = Vec Expr n

-- Some shortcuts for ♭

value : Expr → ℕ
value e = ♭ $ Expr.value e

lift : Expr → Set
lift e = Expr.lift e

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

