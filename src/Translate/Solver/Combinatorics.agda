------------------------------------------------------------------------
-- The Translate library
--
-- Solver expressions corresponding to those in Translate.Combinatorics
------------------------------------------------------------------------

module Translate.Solver.Combinatorics where

open import Translate.Support
open import Translate.Combinatorics
open import Translate.Types
open import Translate.Solver.Types
open import Translate.Solver.Semiring
open import Coinduction

-- uncon : ?
-- uncon = ?

-- normalize : ?
-- normalize = ?

-- :fib : ∀ {n} → :Expr n → :Expr n
-- :fib n = record
--   { polynomial = ♯ ∗atom (:fib n)
--   ; semantics = λ Γ → fib (value (semantics n Γ))
--   -- ; quoted = ♯ (quote :fib , inj₁ (n L∷ L[]))

--   -- TODO: This is roughly what polynomial should do:

-- -- ; polynomial = ♯ (case uncon (normalize n) of λ
-- --     { (∗zero , ∗zero) → ∗suc ∗zero
-- --     ; (∗suc ∗zero , ∗zero) → ∗suc ∗zero
-- --     ; (∗zero , x) → ∗atom (:fib (normalize x))
-- --     ; (∗suc ∗zero , x) → ∗atom (:fib (normalize (∗suc ∗zero ∗+ x)))
-- --     ; (∗suc (∗suc n′) , x) → :expand (:fib (∗suc n′)) ∗+ :expand (:fib n′)
-- --     }
-- --   )

--   }

-- -- TODO: Implement rest of structures from Translate.Combinatorics

