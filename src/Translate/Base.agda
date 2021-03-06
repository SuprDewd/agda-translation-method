------------------------------------------------------------------------
-- The Translate library
--
-- Main building blocks for creating expressions and translating them
------------------------------------------------------------------------

module Translate.Base where

open import Function
open import Coinduction
open import Translate.Common
open import Translate.Types

infix 4 _≡_

------------------------------------------------------------------------
-- Equivalence of expressions

-- TODO: Make it possible to delay defining base cases. One way to achieve this
-- may be to simply take in the base cases as parameters, and then we can add
-- some functionality on top of that to experiment with different base cases.
-- This may also be useful for the semiring solver (as otherwise it would have
-- to find base cases by itself).
data _≡_ (a b : Expr) : Set₂ where
  proof : value a P≡ value b
        → lift a ≅ lift b
        → a ≡ b

equality : ∀ {a b} → a ≡ b → value a P≡ value b
equality (proof prf _) = prf

bijection : ∀ {a b} → a ≡ b → lift a ≅ lift b
bijection (proof _ bij) = bij

refl : ∀ {a} → a ≡ a
refl = proof Prefl Brefl

sym : ∀ {a b} → a ≡ b → b ≡ a
sym (proof a=b a≅b) = proof (Psym a=b) (Bsym a≅b)

trans : ∀ {a b c} → a ≡ b → b ≡ c → a ≡ c
trans (proof a=b a≅b) (proof b=c b≅c) = proof (Ptrans a=b b=c) (Btrans a≅b b≅c)
