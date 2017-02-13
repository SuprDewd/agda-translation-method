------------------------------------------------------------------------
-- The Translate library
--
-- Main building blocks for expressions
------------------------------------------------------------------------

module Translate.Semiring where

open import Translate.Base
open import Translate.Support
open import Translate.Types

infixl 6 _*_
infixl 5 _+_

zero : Expr
zero = record
  { value = ♯ ℕzero
  ; lift = Fin (ℕzero)
  }

suc : Expr → Expr
suc a = record
  { value = ♯ (ℕsuc (value a))
  ; lift = (Maybe (lift a))
  }

_+_ : Expr → Expr → Expr
a + b = record
  { value = ♯ (value a ℕ+ value b)
  ; lift = (lift a ⊎ lift b)
  }

_*_ : Expr → Expr → Expr
a * b = record
  { value = ♯ (value a ℕ* value b)
  ; lift = (lift a × lift b)
  }

-- A quicker way to jump from nats to an expr

fin : ℕ → Expr
fin n = record
  { value = ♯ n
  ; lift = Fin n
  }

