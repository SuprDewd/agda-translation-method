------------------------------------------------------------------------
-- The Translate library
--
-- Bijections and their properties
------------------------------------------------------------------------

module Translate.Bijection where

infix 4 _≡_

-- TODO: Carry proof of bijectivity
-- TODO: Use builtin bijection?

data _≡_ : Set → Set → Set₂ where
  mkBij : ∀ {a b} → (to : a → b) → (from : b → a) → a ≡ b

refl : ∀ {a} → a ≡ a
refl = mkBij (λ z → z) (λ z → z)

sym : ∀ {a b} → a ≡ b → b ≡ a
sym (mkBij a→b b→a) = mkBij b→a a→b

trans : ∀ {a b c} → a ≡ b → b ≡ c → a ≡ c
trans (mkBij a→b b→a) (mkBij c→d d→c) = mkBij (λ z → c→d (a→b z)) (λ z → b→a (d→c z))

-- Helper functions

getTo : ∀ {a b} → a ≡ b -> a -> b
getTo (mkBij to from) = to

getFrom : ∀ {a b} → a ≡ b -> b -> a
getFrom (mkBij to from) = from

