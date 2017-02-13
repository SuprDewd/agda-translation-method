------------------------------------------------------------------------
-- The Translate library
--
-- Semantics for different Solver data types
------------------------------------------------------------------------

module Translate.Solver.Semantics where

open import Translate.Types
open import Translate.Semiring
open import Data.Vec

⟦_⟧P : ∀ {n} → :Polynomial n → Env n → Expr
⟦ ∗atom x ⟧P Γ = :semantics x Γ
⟦ ∗var x ⟧P Γ = lookup x Γ
⟦ ∗zero ⟧P Γ = {!zero!}
⟦ ∗suc x ⟧P Γ = {!!}
⟦ x ∗+ y ⟧P Γ = {!!}
⟦ x ∗* y ⟧P Γ = {!!}

