module features where

open import Function

open import Translate
-- open import Translate.Fibonacci
open import Translate.Support
open import Translate.EqReasoning
open import Translate.Axioms
open import Translate.Bijection using (getTo)

-- Vanilla proof

ex1 : ∀ a b c → a + (b + c) ≡ c + (b + a)
ex1 a b c = trans +-comm (trans (+-cong +-comm refl) +-assoc)

-- Proof using EqReasoning

ex2 : ∀ a b c → a + (b + c) ≡ c + (b + a)
ex2 a b c = begin
  a + (b + c)
  ≈⟨ +-comm ⟩
  (b + c) + a
  ≈⟨ +-cong +-comm refl ⟩
  (c + b) + a
  ≈⟨ +-assoc ⟩
  c + (b + a) ∎

-- Proof using solver

open import Translate.Solver
-- open import Translate.Solver.Types

-- TODO
ex3 : ∀ a b c → a + (b + c) ≡ c + (b + a)
ex3 a b c =
  (solve 3 (λ p q r → p :+ (q :+ r) := r :+ (q :+ p)) refl) a b c

MyFin : ℕ → Set
MyFin ℕzero = ⊥
MyFin (ℕsuc n) = Maybe (MyFin n)

fin : ℕ → Expr
fin ℕzero = zero
fin (ℕsuc n) = suc (fin n)

meow : (MyFin 3) ⊎ ((MyFin 2) ⊎ (MyFin 4)) → (MyFin 4) ⊎ ((MyFin 2) ⊎ (MyFin 3))
meow = getTo (toBijection (ex3 (fin 3) (fin 2) (fin 4)))

