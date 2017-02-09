module features where

open import Function

open import Translate
open import Translate.Fibonacci
open import Translate.Support
open import Translate.EqReasoning
open import Translate.Axioms
open import Translate.Bijection using (getTo)

-- Vanilla proof

-- TODO
ex1 : ∀ a b c → a + (b + c) ≡ c + (b + a)
ex1 = {!!}


-- Proof using EqReasoning

ex2 : ∀ a b c → a + (b + c) ≡ c + (b + a)
ex2 a b c =
  begin
    a + (b + c)
    ≈⟨ +-comm ⟩
    (b + c) + a
    ≈⟨ +-cong +-comm refl ⟩
    (c + b) + a
    ≈⟨ +-assoc ⟩
    c + (b + a)
    ∎

-- Proof using solver

-- TODO
-- ex3 : ∀ a b c → a + (b + c) ≡ c + (b + a)
-- ex3 a b c =
--   (solve 3 (λ p q r → p :+ (q :+ r) := r :+ (q :+ p)) P.refl) a b c

