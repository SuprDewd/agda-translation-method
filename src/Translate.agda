------------------------------------------------------------------------
-- The Translate library
--
-- Main building blocks for creating expressions and translating them
------------------------------------------------------------------------

module Translate where

-- TODO: Re-export imports that make sense, and clean up commented-out imports

open import Translate.Base public
open import Translate.Semiring public
open import Translate.Types public
-- open import Translate.Bijection as B public
-- open import Translate.Bijection public
-- open import Translate.Bijection using (_≡_) public
-- open import Relation.Binary.PropositionalEquality as P


-- TODO: Do we still need this definition?
-- infixr 4 _,_
-- infixr 2 _×_
-- data _×_ : Set → Set → Set where
--   _,_ : ∀ {A B} → A → B → A × B


-- TODO: Do we want to include these helpers somewhere?

-- one : Expr
-- one = suc zero

-- two : Expr
-- two = suc one

-- three : Expr
-- three = suc two

-- four : Expr
-- four = suc three

-- five : Expr
-- five = suc four

-- six : Expr
-- six = suc five

-- seven : Expr
-- seven = suc six

-- eight : Expr
-- eight = suc seven

-- nine : Expr
-- nine = suc eight

-- ten : Expr
-- ten = suc nine

