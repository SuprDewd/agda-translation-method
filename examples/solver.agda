
module solver where

open import Translate
open import Translate.Solver

open SemiringSolver2 SemiringSolver.≡-commutativeSemiring _≟0
-- open Data.Nat.Properties.SemiringSolver
  using (prove; solve; _:=_; con; var; _:+_; _:*_;
          expand)

meow' : ∀ a b c → a + (b + c) ≡ c + (b + a)
meow' = solve 3 (λ x y z → x :+ (y :+ z) := z :+ (y :+ x)) refl

lem2 : (four + six ≡ ten)
lem2 = solve 0 (con four :+ con six := con ten) {!!}

lem3 : ∀ x → (two * (x + four) ≡ eight + two * x)
lem3 = solve 1 (λ x’ → con two :* (x’ :+ con four) := con eight :+ con two :* x’) {!!}

-- This is a non-example (i.e. the identity is false).
-- lem4 : (x y z : ℕ)
-- → ((a b c : ℕ)
-- → (a + 0) + (b + 0 + 0) ≡ (a + 0) + ((b + 0) + ((c + (c + 0) + 0))))
-- → x + y ≡ z * 2 + (y + x)
-- lem4 x y z eq =
-- solve 3 (λ x y z → x :+ y := z :* con 2 :+ (y :+ x))
-- (λ {x y z} → eq x y z) x y z

lem5 : ∀ x y z → z + (x + y) ≡ x + zero + zero + z + zero + y
lem5 = solve 3 (λ x y z → z :+ (x :+ y) := x :+ con zero :+ con zero :+ z :+ con zero :+ y) refl

lem6 : ∀ a b c d e f g h i → a * (b + (c * (d + (e * (f + (g * (h + i))))))) ≡ a * (b + (c * (d + (e * (f + (g * (h))))))) + a * (c * one * e) * g * i
lem6 = solve 9 (λ a b c d e f g h i → a :* (b :+ (c :* (d :+ (e :* (f :+ (g :* (h :+ i))))))) := a :* (b :+ (c :* (d :+ (e :* (f :+ (g :* h)))))) :+ a :* (c :* con one :* e) :* g :* i) {!!}

-- meow' : {!!}
-- meow' = expand {1} (var F.zero :* (var F.zero :+ var F.zero))
