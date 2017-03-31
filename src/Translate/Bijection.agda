------------------------------------------------------------------------
-- The Translate library
--
-- Bijections and their properties
------------------------------------------------------------------------

module Translate.Bijection where

open import Relation.Binary.PropositionalEquality
  using (_≡_)
  renaming ( refl to Prefl
           ; sym to Psym
           ; trans to Ptrans
           ; cong to Pcong
           )

infix 4 _≅_

-- TODO: Use builtin bijection?

data _≅_ : Set → Set → Set₂ where
  mkBij : ∀ {a b}
        → (to : a → b)
        → (from : b → a)
        → (∀ y → to (from y) ≡ y)
        → (∀ x → from (to x) ≡ x)
        → a ≅ b

refl : ∀ {a} → a ≅ a
refl = mkBij (λ z → z) (λ z → z) (λ y → Prefl) (λ x → Prefl)

sym : ∀ {a b} → a ≅ b → b ≅ a
sym (mkBij a→b b→a to-from from-to) = mkBij b→a a→b from-to to-from

trans : ∀ {a b c} → a ≅ b → b ≅ c → a ≅ c
trans (mkBij a→b b→a to-from₁ from-to₁)
      (mkBij c→d d→c to-from₂ from-to₂)
  = mkBij (λ z → c→d (a→b z))
          (λ z → b→a (d→c z))
          (λ y → Ptrans (Pcong c→d (to-from₁ (d→c y))) (to-from₂ y))
          (λ x → Ptrans (Pcong b→a (from-to₂ (a→b x))) (from-to₁ x))

-- Helper functions

getTo : ∀ {a b} → a ≅ b → a → b
getTo (mkBij to _ _ _) = to

getFrom : ∀ {a b} → a ≅ b → b → a
getFrom (mkBij _ from _ _) = from

getToFrom : ∀ {a b} → (p : a ≅ b) → ∀ y → getTo p (getFrom p y) ≡ y
getToFrom (mkBij _ _ to-from _) = to-from

getFromTo : ∀ {a b} → (p : a ≅ b) → ∀ x → getFrom p (getTo p x) ≡ x
getFromTo (mkBij _ _ _ from-to) = from-to

