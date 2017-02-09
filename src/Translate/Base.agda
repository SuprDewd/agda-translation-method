------------------------------------------------------------------------
-- The Translate library
--
-- Main building blocks for creating expressions and translating them
------------------------------------------------------------------------

module Translate.Base where

open import Function
open import Coinduction
open import Translate.Support

infixl 6 _*_ _:*_
infixl 5 _+_ _:+_
infix 4 _≡_

------------------------------------------------------------------------
-- Expressions

-- An expression
record Expr : Set₁ where
  field
    value : ∞ ℕ
    lift : ∞ Set

-- An environment with n variables
Env : ∀ n → Set₁
Env n = Vec Expr n

-- An expression on n variables
record :Expr (n : ℕ) : Set₁ where
  field
    :value : (Γ : Env n) → ∞ ℕ
    :lift : (Γ : Env n) → ∞ Set

value : Expr → ℕ
value e = ♭ $ Expr.value e

lift : Expr → Set
lift e = ♭ $ Expr.lift e

:value : ∀ {n} → :Expr n → Env n → ℕ
:value e Γ = ♭ $ :Expr.:value e Γ

:lift : ∀ {n} → :Expr n → Env n → Set
:lift e Γ = ♭ $ :Expr.:lift e Γ

-- Helpers for converting between Expr and :Expr 0

drop: : :Expr ℕzero → Expr
drop: x = record
  { value = ♯ :value x []
  ; lift = ♯ :lift x []
  }

add: : Expr → :Expr ℕzero
add: x = record
  { :value = λ Γ → ♯ value x
  ; :lift = λ Γ → ♯ lift x
  }

------------------------------------------------------------------------
-- Main building blocks for expressions

:zero : ∀ {n} → :Expr n
:zero = record
  { :value = λ Γ → ♯ ℕzero
  ; :lift = λ Γ → ♯ Fin (ℕzero)
  }

zero : Expr
zero = drop: :zero

:suc : ∀ {n} → :Expr n → :Expr n
:suc a = record
  { :value = λ Γ → ♯ ℕsuc (:value a Γ)
  ; :lift = λ Γ → ♯ Maybe (:lift a Γ)
  }

suc : Expr → Expr
suc n = drop: (:suc (add: n))

_:+_ : ∀ {n} → :Expr n → :Expr n → :Expr n
a :+ b = record
  { :value = λ Γ → ♯ (:value a Γ ℕ+ :value b Γ)
  ; :lift = λ Γ → ♯ (:lift a Γ ⊎ :lift b Γ)
  }

_+_ : Expr → Expr → Expr
a + b = drop: ((add: a) :+ (add: b))

_:*_ : ∀ {n} → :Expr n → :Expr n → :Expr n
a :* b = record
  { :value = λ Γ → ♯ (:value a Γ ℕ* :value b Γ)
  ; :lift = λ Γ → ♯ (:lift a Γ × :lift b Γ)
  }

_*_ : Expr → Expr → Expr
a * b = drop: ((add: a) :* (add: b))

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

