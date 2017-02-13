------------------------------------------------------------------------
-- The Translate library
--
-- Main building blocks for creating expressions and translating them
------------------------------------------------------------------------

module Translate.Base where

open import Function
open import Coinduction
open import Translate.Support
open import Translate.Types

infix 4 _≡_

------------------------------------------------------------------------
-- Expressions



------------------------------------------------------------------------
-- Equivalence of expressions

-- TODO: Make it possible to delay defining base cases. One way to achieve this
-- may be to simply take in the base cases as parameters, and then we can add
-- some functionality on top of that to experiment with different base cases.
-- This may also be useful for the semiring solver (as otherwise it would have
-- to find base cases by itself).
data _≡_ : Expr → Expr → Set₂ where
  refl : ∀ {a} → a ≡ a
  sym : ∀ {a b} → a ≡ b → b ≡ a
  trans : ∀ {a b c} → a ≡ b → b ≡ c → a ≡ c
  axiom : ∀ {a b}
        → value a P≡ value b
        → lift a B≡ lift b
        → a ≡ b

-- The main translation methods

toEquality : ∀ {a b} → a ≡ b → value a P≡ value b
toEquality refl = Prefl
toEquality (sym a≡b) = Psym (toEquality a≡b)
toEquality (trans a≡b c≡d) = Ptrans (toEquality a≡b) (toEquality c≡d)
toEquality (axiom prf _) = prf

toBijection : ∀ {a b} → a ≡ b → lift a B≡ lift b
toBijection refl = mkBij (λ x → x) (λ x → x)
toBijection (sym a≡b) = Bsym (toBijection a≡b)
toBijection (trans a≡b c≡d) = Btrans (toBijection a≡b) (toBijection c≡d)
toBijection (axiom _ bij) = bij

