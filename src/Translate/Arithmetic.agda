------------------------------------------------------------------------
-- The Translate library
--
-- A set of axioms for reasoning with expressions
------------------------------------------------------------------------

-- TODO: Should these be called something else? Laws?
module Translate.Arithmetic where

import Data.Nat.Properties.Simple as NPS

module NP where
  open import Relation.Binary.PropositionalEquality
  open import Data.Nat
  open import Data.Nat.Properties
  open NPS
  open Relation.Binary.PropositionalEquality.≡-Reasoning

  *-right-identity : ∀ {a} → a * suc zero ≡ a
  *-right-identity {zero} = refl
  *-right-identity {suc a} = cong (λ x → suc x) (*-right-identity {a})

  +-comm-2 : ∀ a b c d → a + c ≡ b + d → c + a ≡ d + b
  +-comm-2 a b c d p = begin
    c + a ≡⟨ +-comm c a ⟩
    a + c ≡⟨ p ⟩
    b + d ≡⟨ +-comm b d ⟩
    d + b ∎

  +-cancel : ∀ a b c d → a + c ≡ b + d → c ≡ d → a ≡ b
  +-cancel a b c _ p refl = cancel-+-left c (+-comm-2 a b c c p)

  distribˡ-*-+ : ∀ m n o → m * (n + o) ≡ m * n + m * o
  distribˡ-*-+ m n o = begin
    m * (n + o) ≡⟨ *-comm m (n + o) ⟩
    (n + o) * m ≡⟨ distribʳ-*-+ m n o ⟩
    n * m + o * m ≡⟨ cong (λ x → x + o * m) (*-comm n m) ⟩
    m * n + o * m ≡⟨ cong (λ x → m * n + x) (*-comm o m) ⟩
    m * n + m * o ∎

open import Translate.Base
open import Translate.Common
open import Translate.Types

+-assoc : ∀ {a b c} → (a + b) + c ≡ a + (b + c)
+-assoc {a} {b} {c} = proof (NPS.+-assoc (value a) (value b) (value c)) (mkBij to from to-from from-to)
  where
    -- TODO: is it cleaner to have these as lambdas?
    to : lift ((a + b) + c) → lift (a + (b + c))
    to (inj₁ (inj₁ x)) = inj₁ x
    to (inj₁ (inj₂ x)) = inj₂ (inj₁ x)
    to (inj₂ x) = inj₂ (inj₂ x)

    from : lift (a + (b + c)) → lift ((a + b) + c)
    from (inj₁ x) = inj₁ (inj₁ x)
    from (inj₂ (inj₁ x)) = inj₁ (inj₂ x)
    from (inj₂ (inj₂ x)) = inj₂ x

    to-from : ∀ y → to (from y) P≡ y
    to-from (inj₁ x) = Prefl
    to-from (inj₂ (inj₁ x)) = Prefl
    to-from (inj₂ (inj₂ y)) = Prefl

    from-to : ∀ x → from (to x) P≡ x
    from-to (inj₁ (inj₁ x)) = Prefl
    from-to (inj₁ (inj₂ y)) = Prefl
    from-to (inj₂ y) = Prefl

+-right-identity : ∀ {a} → a + zero ≡ a
+-right-identity {a} = proof (NPS.+-right-identity (value a)) (mkBij to from to-from from-to)
  where
    to : lift (a + zero) → lift a
    to (inj₁ x) = x
    to (inj₂ ())

    from : lift a → lift (a + zero)
    from x = inj₁ x

    to-from : ∀ y → to (from y) P≡ y
    to-from y = Prefl

    from-to : ∀ x → from (to x) P≡ x
    from-to (inj₁ x) = Prefl
    from-to (inj₂ ())

+-suc : ∀ {a b} → a + suc b ≡ suc (a + b)
+-suc {a} {b} = proof (NPS.+-suc (value a) (value b)) (mkBij to from to-from from-to)
  where
    to : lift (a + suc b) → lift (suc (a + b))
    to (inj₁ x) = just (inj₁ x)
    to (inj₂ nothing) = nothing
    to (inj₂ (just x)) = just (inj₂ x)

    from : lift (suc (a + b)) → lift (a + suc b)
    from nothing = inj₂ nothing
    from (just (inj₁ x)) = inj₁ x
    from (just (inj₂ x)) = inj₂ (just x)

    to-from : ∀ y → to (from y) P≡ y
    to-from (just (inj₁ x)) = Prefl
    to-from (just (inj₂ y)) = Prefl
    to-from nothing = Prefl

    from-to : ∀ x → from (to x) P≡ x
    from-to (inj₁ x) = Prefl
    from-to (inj₂ (just x)) = Prefl
    from-to (inj₂ nothing) = Prefl

+-comm : ∀ {a b} → a + b ≡ b + a
+-comm {a} {b} = proof (NPS.+-comm (value a) (value b)) (mkBij to from to-from from-to)
  where
    to : lift (a + b) → lift (b + a)
    to (inj₁ x) = inj₂ x
    to (inj₂ x) = inj₁ x

    from : lift (b + a) → lift (a + b)
    from (inj₁ y) = inj₂ y
    from (inj₂ y) = inj₁ y

    to-from : ∀ y → to (from y) P≡ y
    to-from (inj₁ x) = Prefl
    to-from (inj₂ y) = Prefl

    from-to : ∀ x → from (to x) P≡ x
    from-to (inj₁ x) = Prefl
    from-to (inj₂ y) = Prefl

+-*-suc : ∀ {a b} → a * suc b ≡ a + a * b
+-*-suc {a} {b} = proof (NPS.+-*-suc (value a) (value b)) (mkBij to from to-from from-to)
  where
    to : lift (a * suc b) → lift (a + a * b)
    to (l , nothing) = inj₁ l
    to (l , (just r)) = inj₂ (l , r)

    from : lift (a + a * b) → lift (a * suc b)
    from (inj₁ l) = l , nothing
    from (inj₂ (l , r)) = l , (just r)

    to-from : ∀ y → to (from y) P≡ y
    to-from (inj₁ x) = Prefl
    to-from (inj₂ (l , r)) = Prefl

    from-to : ∀ x → from (to x) P≡ x
    from-to (l , just x) = Prefl
    from-to (l , nothing) = Prefl

*-right-zero : ∀ {a} → a * zero ≡ zero
*-right-zero {a} = proof (NPS.*-right-zero (value a)) (mkBij to from to-from from-to)
  where
    to : lift (a * zero) → lift zero
    to (l , ())

    from : lift zero → lift (a * zero)
    from ()

    to-from : ∀ y → to (from y) P≡ y
    to-from ()

    from-to : ∀ x → from (to x) P≡ x
    from-to (l , ())

*-right-identity : ∀ {a} → a * suc zero ≡ a
*-right-identity {a} = proof NP.*-right-identity (mkBij to from to-from from-to)
  where
    to : lift (a * suc zero) → lift a
    to (l , nothing) = l
    to (_ , (just ()))

    from : lift a → lift (a * suc zero)
    from l = (l , nothing)

    to-from : ∀ y → to (from y) P≡ y
    to-from y = Prefl

    from-to : ∀ x → from (to x) P≡ x
    from-to (l , just ())
    from-to (l , nothing) = Prefl

*-comm : ∀ {a b} → a * b ≡ b * a
*-comm {a} {b} = proof (NPS.*-comm (value a) (value b)) (mkBij to from to-from from-to)
  where
    to : lift (a * b) → lift (b * a)
    to (l , r) = r , l

    from : lift (b * a) → lift (a * b)
    from (l , r) = r , l

    to-from : ∀ y → to (from y) P≡ y
    to-from (l , r) = Prefl

    from-to : ∀ x → from (to x) P≡ x
    from-to (l , r) = Prefl

distribʳ-*-+ : ∀ {a b c} → (b + c) * a ≡ b * a + c * a
distribʳ-*-+ {a} {b} {c} = proof (NPS.distribʳ-*-+ (value a) (value b) (value c)) (mkBij to from to-from from-to)
  where
    to : lift ((b + c) * a) → lift (b * a + c * a)
    to ((inj₁ l) , r) = inj₁ (l , r)
    to ((inj₂ l) , r) = inj₂ (l , r)

    from : lift (b * a + c * a) → lift ((b + c) * a)
    from (inj₁ (l , r)) = (inj₁ l) , r
    from (inj₂ (l , r)) = (inj₂ l) , r

    to-from : ∀ y → to (from y) P≡ y
    to-from (inj₁ (l , r)) = Prefl
    to-from (inj₂ (l , r)) = Prefl

    from-to : ∀ x → from (to x) P≡ x
    from-to (inj₁ x , r) = Prefl
    from-to (inj₂ y , r) = Prefl

distribˡ-*-+ : ∀ {a b c} → a * (b + c) ≡ a * b + a * c
distribˡ-*-+ {a} {b} {c} = proof (NP.distribˡ-*-+ (value a) (value b) (value c)) (mkBij to from to-from from-to)
  where
    to : lift (a * (b + c)) → lift (a * b + a * c)
    to (l , (inj₁ r)) = inj₁ (l , r)
    to (l , (inj₂ r)) = inj₂ (l , r)

    from : lift (a * b + a * c) → lift (a * (b + c))
    from (inj₁ (l , r)) = l , (inj₁ r)
    from (inj₂ (l , r)) = l , (inj₂ r)

    to-from : ∀ y → to (from y) P≡ y
    to-from (inj₁ (l , r)) = Prefl
    to-from (inj₂ (l , r)) = Prefl

    from-to : ∀ x → from (to x) P≡ x
    from-to (l , inj₁ x) = Prefl
    from-to (l , inj₂ y) = Prefl

*-assoc : ∀ {a b c} → (a * b) * c ≡ a * (b * c)
*-assoc {a} {b} {c} = proof (NPS.*-assoc (value a) (value b) (value c)) (mkBij to from to-from from-to)
  where
    to : lift ((a * b) * c) → lift (a * (b * c))
    to ((x , y) , z) = x , (y , z)

    from : lift (a * (b * c)) → lift ((a * b) * c)
    from (x , (y , z)) = (x , y) , z

    to-from : ∀ y → to (from y) P≡ y
    to-from (a , b , c) = Prefl

    from-to : ∀ x → from (to x) P≡ x
    from-to ((a , b) , c) = Prefl

+-cong : ∀ {a b c d} → a ≡ b → c ≡ d → a + c ≡ b + d
+-cong {a} {b} {c} {d} a≡b c≡d
  = lemma (equality a≡b) (bijection a≡b) (equality c≡d) (bijection c≡d)
  where
    lemma : value a P≡ value b
          → lift a ≅ lift b
          → value c P≡ value d
          → lift c ≅ lift d
          → a + c ≡ b + d
    lemma a≡b (mkBij a→b b→a to-from₁ from-to₁) c≡d (mkBij c→d d→c to-from₂ from-to₂) = proof prf (mkBij to from to-from from-to)
      where
        prf : value (a + c) P≡ value (b + d)
        prf = Ptrans (Pcong (λ y → y ℕ+ value c) a≡b) (Pcong (λ y → value b ℕ+ y) c≡d)

        to : lift (a + c) → lift (b + d)
        to (inj₁ x) = inj₁ (a→b x)
        to (inj₂ x) = inj₂ (c→d x)

        from : lift (b + d) → lift (a + c)
        from (inj₁ x) = inj₁ (b→a x)
        from (inj₂ x) = inj₂ (d→c x)

        to-from : ∀ y → to (from y) P≡ y
        to-from (inj₁ x) = Pcong inj₁ (to-from₁ x)
        to-from (inj₂ y) = Pcong inj₂ (to-from₂ y)

        from-to : ∀ x → from (to x) P≡ x
        from-to (inj₁ x) = Pcong inj₁ (from-to₁ x)
        from-to (inj₂ y) = Pcong inj₂ (from-to₂ y)

*-cong : ∀ {a b c d} → a ≡ b → c ≡ d → a * c ≡ b * d
*-cong {a} {b} {c} {d} a≡b c≡d
  = lemma (equality a≡b) (bijection a≡b) (equality c≡d) (bijection c≡d)
  where
    lemma : value a P≡ value b
          → lift a ≅ lift b
          → value c P≡ value d
          → lift c ≅ lift d
          → a * c ≡ b * d
    lemma a≡b (mkBij a→b b→a to-from₁ from-to₁) c≡d (mkBij c→d d→c to-from₂ from-to₂) = proof prf (mkBij to from to-from from-to)
      where
        prf : value (a * c) P≡ value (b * d)
        prf = Ptrans (Pcong (λ y → y ℕ* value c) a≡b) (Pcong (λ y → value b ℕ* y) c≡d)

        to : lift (a * c) → lift (b * d)
        to (x , y) = (a→b x) , (c→d y)

        from : lift (b * d) → lift (a * c)
        from (x , y) = (b→a x) , (d→c y)

        to-from : ∀ y → to (from y) P≡ y
        to-from (l , r) = Ptrans (Pcong (λ t → (t , c→d (d→c r))) (to-from₁ l)) (Pcong (λ t → (l , t)) (to-from₂ r))

        from-to : ∀ x → from (to x) P≡ x
        from-to (l , r) = Ptrans (Pcong (λ t → (t , d→c (c→d r))) (from-to₁ l)) (Pcong (λ t → (l , t)) (from-to₂ r))

