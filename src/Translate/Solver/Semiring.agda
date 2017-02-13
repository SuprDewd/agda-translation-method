------------------------------------------------------------------------
-- The Translate library
--
-- Solver expressions corresponding to those in Translate.Semiring
------------------------------------------------------------------------

module Translate.Solver.Semiring where

open import Translate.Support
open import Translate.Semiring
open import Translate.Solver.Types
open import Coinduction
import Data.List as L

infixl 6 _:*_
infixl 5 _:+_

:zero : ∀ {n} → :Expr n
:zero = record
  { polynomial = ♯ ∗zero
  ; semantics = λ Γ → zero
  -- ; quoted = ♯ (quote :zero , inj₁ L[])
  }

:suc : ∀ {n} → :Expr n → :Expr n
:suc a = record
  { polynomial = ♯ ∗suc (polynomial a)
  ; semantics = λ Γ → suc (semantics a Γ)
  -- ; quoted = ♯ (quote :suc , inj₁ (a L∷ L[]))
  }

_:+_ : ∀ {n} → :Expr n → :Expr n → :Expr n
a :+ b = record
  { polynomial = ♯ (polynomial a ∗+ polynomial b)
  ; semantics = λ Γ → (semantics a Γ + semantics b Γ)
  -- ; quoted = ♯ (quote _:+_ , inj₁ (a L∷ b L∷ L[]))
  }

_:*_ : ∀ {n} → :Expr n → :Expr n → :Expr n
a :* b = record
  { polynomial = ♯ (polynomial a ∗* polynomial b)
  ; semantics = λ Γ → (semantics a Γ * semantics b Γ)
  -- ; quoted = ♯ (quote _:*_ , inj₁ (a L∷ b L∷ L[]))
  }
