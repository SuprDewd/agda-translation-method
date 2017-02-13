------------------------------------------------------------------------
-- The Translate library
--
-- Main building blocks for expressions
------------------------------------------------------------------------

module Translate.Solver.Types where

open import Translate.Support
open import Translate.Types
open import Coinduction
open import Function
open import Data.Vec
import Data.List as L
open import Data.Bool

infixl 6 _∗*_
infixl 5 _∗+_


-- postulate Name : Set
-- {-# BUILTIN QNAME Name #-}

-- primitive
--   primQNameEquality : Name → Name → Bool
--   primQNameLess     : Name → Name → Bool


mutual

  -- An expression on n variables
  record :Expr (n : ℕ) : Set₁ where
    inductive
    field
      polynomial : ∞ (Polynomial n)
      semantics : (Γ : Env n) → Expr
      -- quoted : Name × (L.List (:Expr n) ⊎ Fin n)

      -- polynomial : ∞ (Polynomial n)
      -- semantics : (Γ : Env n) → ∞ Expr
      -- quoted : ∞ (Name × (L.List (:Expr n) ⊎ Fin n))

  data Polynomial (n : ℕ) : Set₁ where
    ∗atom : :Expr n → Polynomial n -- TODO: Maybe this should be (fun (Expr → ... → Expr) → Vec Expr m ­> Polynomial n)
    -- ∗var : Fin n → Polynomial n
    ∗zero : Polynomial n
    ∗suc : (x : Polynomial n) → Polynomial n
    _∗+_ : (x y : Polynomial n) → Polynomial n
    _∗*_ : (x y : Polynomial n) → Polynomial n

semantics : ∀ {n} → :Expr n → Env n → Expr
semantics e Γ = :Expr.semantics e Γ

polynomial : ∀ {n} → :Expr n → Polynomial n
polynomial e = ♭ $ :Expr.polynomial e

-- quoted : ∀ {n} → :Expr n → Name × (L.List (:Expr n) ⊎ Fin n)
-- quoted e = :Expr.quoted e

------------------------------------------------------------------------
-- :Expr constructions

:var : ∀ {n} → Fin n → :Expr n
:var x = record
  { polynomial = ♯ ∗atom (:var x) -- TODO: Normalize x?
  ; semantics = λ Γ → lookup x Γ
  -- ; quoted = (quote :var , inj₂ x)
  }

-- Other constructions in Translate.Solver.Semiring

------------------------------------------------------------------------
-- Intermediate representations used by the solver

data Constant : Set where
  ∗zero : Constant
  ∗suc : Constant → Constant
  _∗+_ : Constant → Constant → Constant
  _∗*_ : Constant → Constant → Constant

-- TODO: Move other types in here?

