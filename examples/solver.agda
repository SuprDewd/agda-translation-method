
module solver where

open import Translate
open import Translate.Solver
open import Translate.Bijection using (getTo)

-- open SemiringSolver2 SemiringSolver.≡-commutativeSemiring _≟0
-- -- open Data.Nat.Properties.SemiringSolver
--   using (prove; solve; _:=_; con; var; _:+_; _:*_;
--           expand)

one : Expr
one = suc zero

two : Expr
two = suc one

three : Expr
three = suc two

four : Expr
four = suc three

five : Expr
five = suc four

six : Expr
six = suc five

seven : Expr
seven = suc six

eight : Expr
eight = suc seven

nine : Expr
nine = suc eight

ten : Expr
ten = suc nine

:one : ∀ {n} → :Expr n
:one = :suc :zero

:two : ∀ {n} → :Expr n
:two = :suc :one

:three : ∀ {n} → :Expr n
:three = :suc :two

:four : ∀ {n} → :Expr n
:four = :suc :three

:five : ∀ {n} → :Expr n
:five = :suc :four

:six : ∀ {n} → :Expr n
:six = :suc :five

:seven : ∀ {n} → :Expr n
:seven = :suc :six

:eight : ∀ {n} → :Expr n
:eight = :suc :seven

:nine : ∀ {n} → :Expr n
:nine = :suc :eight

:ten : ∀ {n} → :Expr n
:ten = :suc :nine

meow' : ∀ a b c → a + (b + c) ≡ c + (b + a)
meow' = solve 3 (λ x y z → x :+ (y :+ z) := z :+ (y :+ x)) refl

lem2 : (four + six ≡ ten)
lem2 = solve 0 (:four :+ :six := :ten) refl

open import Translate.Common
lem2-bij : lift (four + six) → lift (ten)
lem2-bij = getTo (bijection lem2)

lem3 : ∀ x → (two * (x + four) ≡ eight + two * x)
lem3 = solve 1 (λ x’ → :two :* (x’ :+ :four) := :eight :+ :two :* x’) refl

-- This is a non-example (i.e. the identity is false).
-- lem4 : ∀ x y z → (∀ a b c → (a + zero) + (b + zero + zero) ≡ (a + zero) + ((b + zero) + ((c + (c + zero) + zero)))) → x + y ≡ z * two + (y + x)
-- lem4 x y z eq = solve 3 (λ x y z → x :+ y := z :* :two :+ (y :+ x)) {!!} x y z

lem5 : ∀ x y z → z + (x + y) ≡ x + zero + zero + z + zero + y
lem5 = solve 3 (λ x y z → z :+ (x :+ y) := x :+ :zero :+ :zero :+ z :+ :zero :+ y) refl

lem6 : ∀ a b c d e f g h i → a * (b + (c * (d + (e * (f + (g * (h + i))))))) ≡ a * (b + (c * (d + (e * (f + (g * (h))))))) + a * (c * one * e) * g * i
lem6 = solve 9 (λ a b c d e f g h i → a :* (b :+ (c :* (d :+ (e :* (f :+ (g :* (h :+ i))))))) := a :* (b :+ (c :* (d :+ (e :* (f :+ (g :* h)))))) :+ a :* (c :* :one :* e) :* g :* i) refl

-- meow' : {!!}
-- meow' = expand {1} (var F.zero :* (var F.zero :+ var F.zero))

lem7 : ∀ a b → (a + b) * (a + b) ≡ a * a + nat 2 * a * b + b * b
lem7 = solve 2 (λ x y → (x :+ y) :* (x :+ y) := x :* x :+ :nat 2 :* x :* y :+ y :* y) refl

import Data.List as L

inps : List (lift ((nat 1 + nat 2) * (nat 1 + nat 2)))
inps = (inj₁ nothing , inj₁ nothing) L∷
       (inj₁ nothing , inj₂ nothing) L∷
       (inj₁ nothing , inj₂ (just nothing)) L∷
       (inj₂ nothing , inj₁ nothing) L∷
       (inj₂ nothing , inj₂ nothing) L∷
       (inj₂ nothing , inj₂ (just nothing)) L∷
       (inj₂ (just nothing) , inj₁ nothing) L∷
       (inj₂ (just nothing) , inj₂ nothing) L∷
       (inj₂ (just nothing) , inj₂ (just nothing)) L∷
       L[]

-- meow : ∀ {a b c} → a * (b + c) ≡ a * b + a * c
-- meow = begin 3 (λ x y z →
--     x :* (y :+ z)
--   ≈⟨ Prefl ⟩
--     x :* (y :+ z)
--   ≈'⟨ Prefl ⟩
--     x :* (y :+ z)
--   ≈⟨ ? ⟩
--     x :* y :+ x :* z
--   ∎)

