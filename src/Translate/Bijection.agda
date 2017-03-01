------------------------------------------------------------------------
-- The Translate library
--
-- Bijections and their properties
------------------------------------------------------------------------

module Translate.Bijection where

open import Relation.Binary.PropositionalEquality
  using ()
  renaming (_≡_ to _P≡_
           ; refl to Prefl
           ; sym to Psym
           ; trans to Ptrans
           ; cong to Pcong
           )

infix 4 _≡_

-- TODO: Use builtin bijection?

data _≡_ : Set → Set → Set₂ where
  mkBij : ∀ {a b}
        → (to : a → b)
        → (from : b → a)
        → (∀ y → to (from y) P≡ y)
        → (∀ x → from (to x) P≡ x)
        → a ≡ b

refl : ∀ {a} → a ≡ a
refl = mkBij (λ z → z) (λ z → z) (λ y → Prefl) (λ x → Prefl)

sym : ∀ {a b} → a ≡ b → b ≡ a
sym (mkBij a→b b→a toFrom fromTo) = mkBij b→a a→b fromTo toFrom

trans : ∀ {a b c} → a ≡ b → b ≡ c → a ≡ c
trans (mkBij a→b b→a toFrom₁ fromTo₁)
      (mkBij c→d d→c toFrom₂ fromTo₂)
  = mkBij (λ z → c→d (a→b z))
          (λ z → b→a (d→c z))
          (λ y → Ptrans (Pcong c→d (toFrom₁ (d→c y))) (toFrom₂ y))
          (λ x → Ptrans (Pcong b→a (fromTo₂ (a→b x))) (fromTo₁ x))

-- Helper functions

getTo : ∀ {a b} → a ≡ b -> a -> b
getTo (mkBij to _ _ _) = to

getFrom : ∀ {a b} → a ≡ b -> b -> a
getFrom (mkBij _ from _ _) = from

getToFrom : ∀ {a b} → (p : a ≡ b) → ∀ y → getTo p (getFrom p y) P≡ y
getToFrom (mkBij _ _ toFrom _) = toFrom

getFromTo : ∀ {a b} → (p : a ≡ b) → ∀ x → getFrom p (getTo p x) P≡ x
getFromTo (mkBij _ _ _ fromTo) = fromTo

