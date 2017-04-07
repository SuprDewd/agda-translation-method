
open import Data.Nat using (_+_; _*_; ℕ)
open import Relation.Binary.Core using (_≡_; refl)
import Data.Nat.Properties
open Data.Nat.Properties.SemiringSolver
  using (prove; solve; _:=_; con; var; _:+_; _:*_; :-_; _:-_)

lem7 : ∀ a b → (a + b) * (a + b) ≡ a * a + 2 * a * b + b * b
lem7 = solve 2 (λ x y → (x :+ y) :* (x :+ y) := x :* x :+ con 2 :* x :* y :+ y :* y) refl

