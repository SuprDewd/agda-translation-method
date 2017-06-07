module Worpitzky where

-- open import Translate
-- open import Translate.Support
-- open import Translate.Combinatorics

-- lemma : ∀ k x n → nat (k ℕ+ 1) * (x ℕ+ k ℕ- (n ℕ+ 1)) choose (n ℕ+ 1)

open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Nat.Properties.Simple
open ≡-Reasoning


n≤n : (n : ℕ) → n ≤ n
n≤n zero = z≤n
n≤n (suc n) = s≤s (n≤n n)

incr≤ : ∀ {a b} → a ≤ b → a ≤ suc b
incr≤ {zero} {b} p = z≤n
incr≤ {suc a} {zero} ()
incr≤ {suc a} {suc b} (s≤s p) = s≤s (incr≤ {a} {b} p)

choose : ℕ → ℕ → ℕ
choose zero zero = 1
choose zero (suc k) = 0
choose (suc n) zero = 1
choose (suc n) (suc k) = choose n (suc k) + choose n k

choose-zero : (n : ℕ) → (k : ℕ) → (n < k) → choose n k ≡ 0
choose-zero zero (suc k) (s≤s p) = refl
choose-zero (suc n) (suc k) (s≤s p) =
  begin
    choose n (suc k) + choose n k
  ≡⟨ cong (λ e → choose n (suc k) + e) (choose-zero n k p) ⟩
    choose n (suc k) + 0
  ≡⟨ cong (λ e → e + 0) (choose-zero n (suc k) (incr≤ p)) ⟩
    0 + 0
  ≡⟨ refl ⟩
    0
  ∎

euler : ℕ → ℕ → ℕ
-- n elements, k ascents
-- euler zero zero = 1
euler zero (suc k) = 0
euler zero zero = 1
-- euler (suc n) k = (k + 1) * euler n k + (suc n ∸ k) * euler n (k ∸ 1)
euler (suc n) zero = euler n zero
euler (suc n) (suc k) = (k + 2) * euler n (suc k) + (n ∸ k) * euler n k

euler-zero₂ : ∀ n k → n < k → euler n k ≡ 0
euler-zero₂ zero (suc k) (s≤s p) = refl
euler-zero₂ (suc n) (suc k) (s≤s p) =
  begin
    (k + 2) * euler n (suc k) + (n ∸ k) * euler n k
  ≡⟨ cong (λ e → (k + 2) * euler n (suc k) + (n ∸ k) * e) (euler-zero₂ n k p) ⟩
    (k + 2) * euler n (suc k) + (n ∸ k) * 0
  ≡⟨ cong (λ e → (k + 2) * e + (n ∸ k) * 0) (euler-zero₂ n (suc k) (lem n k p)) ⟩
    (k + 2) * 0 + (n ∸ k) * 0
  ≡⟨ cong (λ e → e + (n ∸ k) * 0) (*-right-zero (k + suc (suc zero))) ⟩
    0 + (n ∸ k) * 0
  ≡⟨ cong (λ e → 0 + e) (*-right-zero (n ∸ k)) ⟩
    0 + 0
  ≡⟨⟩
    0
  ∎
  where
    lem : ∀ n k → suc n ≤ k → n < suc k
    lem zero (suc k) (s≤s p₁) = s≤s z≤n
    lem (suc n) (suc k) (s≤s p) = s≤s (lem n k p)

euler-zero : ∀ n → euler (suc n) (suc n) ≡ 0
euler-zero zero = refl
euler-zero (suc n) =
  begin
    euler (suc (suc n)) (suc (suc n))
  ≡⟨⟩
    (suc n + 2) * euler (suc n) (suc (suc n)) + ((suc n) ∸ (suc n)) * euler (suc n) (suc n)
  ≡⟨ cong (λ e → (suc n + 2) * euler (suc n) (suc (suc n)) + e * euler (suc n) (suc n)) (lem (suc n)) ⟩
    (suc n + 2) * euler (suc n) (suc (suc n)) + 0 * euler (suc n) (suc n)
  ≡⟨ cong (λ e → (suc n + 2) * euler (suc n) (suc (suc n)) + e) refl ⟩
    (suc n + 2) * euler (suc n) (suc (suc n)) + 0
  ≡⟨ +-right-identity _ ⟩
    (suc n + 2) * euler (suc n) (suc (suc n))
  ≡⟨ cong (λ e → (suc n + 2) * e) (euler-zero₂ (suc n) (suc (suc n)) (lem2 n)) ⟩
    (suc n + 2) * 0
  ≡⟨ *-right-zero (suc n + 2) ⟩
    0
  ∎
  where
    lem : ∀ x → x ∸ x ≡ 0
    lem zero = refl
    lem (suc x) = lem x

    lem2 : ∀ n → suc n < suc (suc n)
    lem2 zero = s≤s (s≤s z≤n)
    lem2 (suc n) = s≤s (lem2 n)

-- Sum : (lo : ℕ) → (hi : ℕ) → lo ≤ hi → ((i : ℕ) → lo ≤ i → i ≤ hi → ℕ) → ℕ
-- Sum .0 zero z≤n f = f 0 z≤n z≤n
-- Sum .0 (suc hi) z≤n f = f (suc hi) z≤n (n≤n (suc hi)) + Sum 0 hi z≤n (λ i p1 p2 → f i p1 (incr≤ i hi p2))
-- Sum (suc lo) (suc hi) (s≤s prf) f = f (suc hi) (s≤s prf) (n≤n (suc hi)) + Sum (suc lo) hi {!!} (λ i p1 p2 → {!!})

-- n<sn : (n : ℕ) → n < suc n
-- n<sn zero = s≤s z≤n
-- n<sn (suc n) = {!!}

Sum : (n : ℕ) → ((i : ℕ) → i < n → ℕ) → ℕ
Sum zero f = 0
Sum (suc n) f = f n (n≤n (suc n)) + Sum n (λ i p → f i (incr≤ p))

Sum-cong : (n : ℕ) → (f : (i : ℕ) → i < n → ℕ) → (g : (i : ℕ) → i < n → ℕ) → ((i : ℕ) → (p : i < n) → f i p ≡ g i p) → Sum n f ≡ Sum n g
Sum-cong zero f g p = refl
Sum-cong (suc n) f g p = begin
    f n (s≤s (n≤n n)) + Sum n (λ i p₁ → f i (incr≤ p₁))
  ≡⟨ cong (λ t → t + Sum n (λ i p₁ → f i (incr≤ p₁))) (p n (s≤s (n≤n n))) ⟩
    g n (s≤s (n≤n n)) + Sum n (λ i p₁ → f i (incr≤ p₁))
  ≡⟨ cong (λ t → g n (n≤n (suc n)) + t) (Sum-cong n (λ i p2 → f i (incr≤ p2)) (λ i p2 → g i (incr≤ p2)) (λ i p2 → p i (incr≤ p2))) ⟩
    g n (n≤n (suc n)) + Sum n (λ i p₁ → g i (incr≤ p₁))
  ∎

Sum-pop : (n : ℕ) → (f : (i : ℕ) → i < suc n → ℕ) → Sum (suc n) f ≡ f 0 (s≤s z≤n) + Sum n (λ i p → f (suc i) (s≤s p))
Sum-pop zero f = refl
Sum-pop (suc n) f =
  begin
    Sum (suc (suc n)) f
  ≡⟨⟩
    f (suc n) (n≤n (suc (suc n))) + Sum ((suc n)) (λ i p → f i (incr≤ p))
  ≡⟨ cong (λ e → f (suc n) (n≤n (suc (suc n))) + e) (Sum-pop n (λ i p → f i (incr≤ p))) ⟩
    f (suc n) (n≤n (suc (suc n))) + (f 0 (s≤s z≤n) + Sum n (λ i p → (λ i p → f i (incr≤ p)) (suc i) (s≤s p)))
  ≡⟨ sym (+-assoc (f (suc n) (n≤n (suc (suc n)))) (f 0 (s≤s z≤n)) (Sum n (λ i p → (λ i p → f i (incr≤ p)) (suc i) (s≤s p)))) ⟩
    (f (suc n) (n≤n (suc (suc n))) + f 0 (s≤s z≤n)) + Sum n (λ i p → (λ i p → f i (incr≤ p)) (suc i) (s≤s p))
  ≡⟨ cong (λ e → e + Sum n (λ i p → (λ i p → f i (incr≤ p)) (suc i) (s≤s p))) (+-comm (f (suc n) (s≤s (s≤s (n≤n n)))) (f zero (s≤s z≤n))) ⟩
    (f 0 (s≤s z≤n) + f (suc n) (n≤n (suc (suc n)))) + Sum n (λ i p → (λ i p → f i (incr≤ p)) (suc i) (s≤s p))
  ≡⟨ +-assoc (f 0 (s≤s z≤n)) (f (suc n) (n≤n (suc (suc n)))) (Sum n (λ i z → f (suc i) (s≤s (incr≤ z)))) ⟩
    f 0 (s≤s z≤n) + Sum (suc n) (λ i p → f (suc i) (s≤s p))
  ∎

Sum-zero : (n : ℕ) → Sum n (λ i p → 0) ≡ 0
Sum-zero zero = refl
Sum-zero (suc n) = Sum-zero n

Sum-split : (n : ℕ) → (f : (i : ℕ) → i < n → ℕ) → (g : (i : ℕ) → i < n → ℕ) → Sum n (λ i p → f i p + g i p) ≡ Sum n (λ i p → f i p) + Sum n (λ i p → g i p)
Sum-split zero f g = refl
Sum-split (suc n) f g = begin
    f n (s≤s (n≤n n)) + g n (s≤s (n≤n n)) + Sum n (λ i p → f i (incr≤ p) + g i (incr≤ p))
  ≡⟨ cong (λ e → f n (s≤s (n≤n n)) + g n (s≤s (n≤n n)) + e) (Sum-split n (λ i p → f i (incr≤ p)) (λ i p → g i (incr≤ p))) ⟩
    (f n (s≤s (n≤n n)) + g n (s≤s (n≤n n))) + (Sum n (λ i p → f i (incr≤ p)) + Sum n (λ i p → g i (incr≤ p)))
  ≡⟨ +-assoc (f n (s≤s (n≤n n))) (g n (s≤s (n≤n n))) (Sum n (λ i p → f i (incr≤ p)) + Sum n (λ i p → g i (incr≤ p))) ⟩
    f n (s≤s (n≤n n)) + (g n (s≤s (n≤n n)) + (Sum n (λ i p → f i (incr≤ p)) + Sum n (λ i p → g i (incr≤ p))))
  ≡⟨ cong (λ x → f n (s≤s (n≤n n)) + x) (+-comm (g n (s≤s (n≤n n))) (Sum n (λ i p → f i (incr≤ p)) + Sum n (λ i p → g i (incr≤ p)))) ⟩
    f n (s≤s (n≤n n)) + ((Sum n (λ i p → f i (incr≤ p)) + Sum n (λ i p → g i (incr≤ p))) + g n (s≤s (n≤n n)))
  ≡⟨ cong (λ x → f n (s≤s (n≤n n)) + x) (+-assoc (Sum n (λ i p → f i (incr≤ p))) (Sum n (λ i p → g i (incr≤ p))) (g n (s≤s (n≤n n)))) ⟩
    f n (s≤s (n≤n n)) + (Sum n (λ i p → f i (incr≤ p)) + (Sum n (λ i p → g i (incr≤ p)) + g n (s≤s (n≤n n))))
  ≡⟨ sym (+-assoc (f n (s≤s (n≤n n))) (Sum n (λ i p → f i (incr≤ p))) (Sum n (λ i p → g i (incr≤ p)) + g n (s≤s (n≤n n)))) ⟩
    (f n (s≤s (n≤n n)) + Sum n (λ i p → f i (incr≤ p))) + (Sum n (λ i p → g i (incr≤ p)) + g n (s≤s (n≤n n)))
  ≡⟨ cong (λ x → (f n (s≤s (n≤n n)) + Sum n (λ i p → f i (incr≤ p))) + x) (+-comm (Sum n (λ i p → g i (incr≤ p))) (g n (s≤s (n≤n n)))) ⟩
    f n (s≤s (n≤n n)) + Sum n (λ i p → f i (incr≤ p)) + (g n (s≤s (n≤n n)) + Sum n (λ i p → g i (incr≤ p)))
  ∎

pow : ℕ → ℕ → ℕ
pow x zero = 1
pow x (suc n) = x * pow x n

open import Data.Sum
case≤ : ∀ a b → a ≤ b → (a ≡ b) ⊎ (a < b)
case≤ .0 zero z≤n = inj₁ refl
case≤ .0 (suc b) z≤n = inj₂ (s≤s z≤n)
case≤ (suc a) (suc b) (s≤s p) with case≤ a b p
case≤ (suc a) (suc b) (s≤s p) | inj₁ x = inj₁ (cong suc x)
case≤ (suc a) (suc b) (s≤s p) | inj₂ y = inj₂ (s≤s y)

-- suc-inj : ∀ n m → suc n ≡ suc m → n ≡ m
-- suc-inj n m = ?

worpitzky : ∀ x n → Sum (suc n) (λ i p → euler n i * choose (x + i) n) ≡ pow x n
worpitzky zero zero = refl
worpitzky zero (suc n) =
  begin
    Sum (suc (suc n)) (λ i p → euler (suc n) i * choose (zero + i) (suc n))
  ≡⟨ Sum-cong (suc (suc n)) (λ i p → euler (suc n) i * choose (zero + i) (suc n)) (λ i p → 0) lem ⟩
    Sum (suc (suc n)) (λ i p → 0)
  ≡⟨ Sum-zero (suc (suc n)) ⟩
    0
  ≡⟨⟩
    pow zero (suc n)
  ∎
  where
    lem : ∀ i → i < suc (suc n) → euler (suc n) i * choose i (suc n) ≡ 0
    lem i (s≤s q) with case≤ (i) ((suc n)) q
    lem i (s≤s q) | inj₁ refl = begin
        euler (suc n) i * choose i (suc n)
      ≡⟨ cong (λ e → e * choose i (suc n)) (euler-zero n) ⟩
        0 * choose i (suc n)
      ≡⟨⟩
        0
      ∎
    lem i (s≤s q) | inj₂ y =
      begin
        euler (suc n) i * choose i (suc n)
      ≡⟨ cong (λ e → euler (suc n) i * e) (choose-zero i (suc n) y) ⟩
        euler (suc n) i * 0
      ≡⟨ *-right-zero (euler (suc n) i) ⟩
        0
      ∎
worpitzky (suc x) zero = refl
worpitzky x (suc n) =
  begin
    Sum (suc (suc n)) (λ i p → euler (suc n) i * choose (x + i) (suc n))
  ≡⟨ Sum-pop (suc n) (λ i p → euler (suc n) i * choose (x + i) (suc n)) ⟩
    euler (suc n) 0 * choose (x + 0) (suc n) + Sum (suc n) (λ i p → euler (suc n) (suc i) * choose (x + suc i) (suc n))
  ≡⟨ cong (λ e → euler (suc n) 0 * choose (x + 0) (suc n) + e) refl ⟩
    euler (suc n) 0 * choose (x + 0) (suc n) + Sum (suc n) (λ i p → ((i + 2) * euler n (suc i) + (n ∸ i) * euler n i) * choose (x + suc i) (suc n))
    ≡⟨ cong (λ e → euler (suc n) 0 * choose (x + 0) (suc n) + e) (Sum-cong (suc n) (λ i p → ((i + 2) * euler n (suc i) + (n ∸ i) * euler n i) * choose (x + suc i) (suc n)) (λ i p → (((i + 2) * euler n (suc i)) * choose (x + suc i) (suc n) + ((n ∸ i) * euler n i) * choose (x + suc i) (suc n))) (λ i p → distribʳ-*-+ (choose (x + suc i) (suc n)) ((i + 2) * euler n (suc i)) ((n ∸ i) * euler n i))) ⟩
    euler (suc n) 0 * choose (x + 0) (suc n) + Sum (suc n) (λ i p → (((i + 2) * euler n (suc i)) * choose (x + suc i) (suc n) + ((n ∸ i) * euler n i) * choose (x + suc i) (suc n)))
  ≡⟨ cong (λ e → euler (suc n) 0 * choose (x + 0) (suc n) + e) (Sum-split (suc n) ((λ i p → ((i + 2) * euler n (suc i)) * choose (x + suc i) (suc n))) ((λ i p → ((n ∸ i) * euler n i) * choose (x + suc i) (suc n)))) ⟩
    euler (suc n) 0 * choose (x + 0) (suc n) + (Sum (suc n) (λ i p → ((i + 2) * euler n (suc i)) * choose (x + suc i) (suc n))
                                             + Sum (suc n) (λ i p → ((n ∸ i) * euler n i) * choose (x + suc i) (suc n)))
  ≡⟨ {!cong (λ e → e + Sum (suc n) (λ i p → ((n ∸ i) * euler n i) * choose (x + suc i) (suc n))))!} ⟩
    Sum (suc (suc n)) (λ i p → ((i + 1) * euler n i) * choose (x + i) (suc n)) + Sum (suc n) (λ i p → ((n ∸ i) * euler n i) * choose (x + suc i) (suc n))
  ≡⟨ {!!} ⟩
    pow x (suc n)
  ∎

-- worpitzky zero zero = refl
-- worpitzky (suc x) zero = refl
-- worpitzky x (suc n) = begin
--     Sum (suc n) (λ i p → euler (suc n) i * choose (x + i) (suc n))
--   ≡⟨ {!!} ⟩
--     Sum (suc n) (λ i p → euler (suc n) i * choose (x + i) (suc n))
--   ≡⟨ {!!} ⟩
--     pow x (suc n)
--   ∎

choose-lem-1 : ∀ x → choose (suc x) 1 ≡ suc x
choose-lem-1 zero = refl
choose-lem-1 (suc x) = begin
    choose (suc (suc x)) 1
  ≡⟨ refl ⟩
    choose (suc x) 1 + choose (suc x) 0
  ≡⟨ refl ⟩
    choose (suc x) 1 + 1
  ≡⟨ cong (λ e → e + 1) (choose-lem-1 x) ⟩
    suc x + 1
  ≡⟨ +-comm (suc x) 1 ⟩
    (suc (suc x))
  ∎

subtract : (x y : ℕ) → (y ≤ x) → ℕ
subtract x zero prf = x
subtract zero (suc y) ()
subtract (suc x) (suc y) (s≤s prf) = subtract x y prf

*-right-identity : ∀ x → x * 1 ≡ x
*-right-identity zero = refl
*-right-identity (suc x) = cong suc (*-right-identity x)

distribˡ-*-+ : ∀ m n o → m * (n + o) ≡ m * n + m * o
distribˡ-*-+ m n o =
  begin
    m * (n + o)
  ≡⟨ *-comm m (n + o) ⟩
    (n + o) * m
  ≡⟨ distribʳ-*-+ m n o ⟩
    n * m + o * m
  ≡⟨ cong (λ e → e + o * m) (*-comm n m) ⟩
    m * n + o * m
  ≡⟨ cong (λ e → m * n + e) (*-comm o m) ⟩
    m * n + m * o
  ∎

lemma0 : ∀ x n
      → choose x (n + 1) + n * choose (x + 1) (n + 1)
      ≡ x * choose x n
lemma0 zero zero = refl
lemma0 zero (suc n) rewrite +-comm n 1 = *-right-zero n
lemma0 (suc x) zero =
  begin
    choose (suc x) 1 + 0 * choose (suc x + 1) 1
  ≡⟨ refl ⟩
    choose (suc x) 1 + 0
  ≡⟨ +-right-identity _ ⟩
    choose (suc x) 1
  ≡⟨ choose-lem-1 x ⟩
    suc x
  ≡⟨ sym (*-right-identity (suc x)) ⟩
    (suc x) * 1
  ≡⟨ refl ⟩
    (suc x) * choose (suc x) 0
  ∎
lemma0 (suc x) (suc n) =
  begin
    choose (suc x) (suc (n + 1)) + (suc n) * choose (suc (x + 1)) (suc (n + 1))
  ≡⟨ refl ⟩
    (choose x (suc (n + 1)) + choose x (n + 1)) + (choose (suc (x + 1)) (suc (n + 1)) + n * choose (suc (x + 1)) (suc (n + 1)))
  ≡⟨ cong (λ e → (choose x (suc (n + 1)) + choose x (n + 1)) + e) (+-comm (choose (suc (x + 1)) (suc (n + 1))) _) ⟩
    (choose x (suc (n + 1)) + choose x (n + 1)) + (n * choose (suc (x + 1)) (suc (n + 1)) + choose (suc (x + 1)) (suc (n + 1)))
  ≡⟨ sym (+-assoc ((choose x (suc (n + 1)) + choose x (n + 1))) _ _) ⟩
    ((choose x (suc (n + 1)) + choose x (n + 1)) + n * choose (suc (x + 1)) (suc (n + 1))) + choose (suc (x + 1)) (suc (n + 1))
  ≡⟨ cong (λ e → e + choose (suc (x + 1)) (suc (n + 1))) (+-assoc (choose x (suc (n + 1))) _ _) ⟩
    (choose x (suc (n + 1)) + (choose x (n + 1) + n * choose (suc (x + 1)) (suc (n + 1)))) + choose (suc (x + 1)) (suc (n + 1))
  ≡⟨ cong (λ e → e + choose (suc (x + 1)) (suc (n + 1))) (+-comm (choose x (suc (n + 1))) _) ⟩
    ((choose x (n + 1) + n * choose (suc (x + 1)) (suc (n + 1))) + choose x (suc (n + 1))) + choose (suc (x + 1)) (suc (n + 1))
  ≡⟨ +-assoc ((choose x (n + 1) + n * choose (suc (x + 1)) (suc (n + 1)))) _ _ ⟩
    (choose x (n + 1) + n * choose (suc (x + 1)) (suc (n + 1))) + (choose x (suc (n + 1)) + choose (suc (x + 1)) (suc (n + 1)))
  ≡⟨ refl ⟩
    (choose x (n + 1) + n * (choose (x + 1) (suc (n + 1)) + choose (x + 1) ((n + 1)))) + (choose x (suc (n + 1)) + choose (suc (x + 1)) (suc (n + 1)))
  ≡⟨ cong (λ e → (choose x (n + 1) + e) + (choose x (suc (n + 1)) + choose (suc (x + 1)) (suc (n + 1)))) (distribˡ-*-+ n _ _) ⟩
    (choose x (n + 1) + (n * choose (x + 1) (suc (n + 1)) + n * choose (x + 1) ((n + 1)))) + (choose x (suc (n + 1)) + choose (suc (x + 1)) (suc (n + 1)))
  ≡⟨ cong (λ e → (choose x (n + 1) + e) + (choose x (suc (n + 1)) + choose (suc (x + 1)) (suc (n + 1)))) (+-comm (n * choose (x + 1) (suc (n + 1))) _) ⟩
    (choose x (n + 1) + (n * choose (x + 1) ((n + 1)) + n * choose (x + 1) (suc (n + 1)))) + (choose x (suc (n + 1)) + choose (suc (x + 1)) (suc (n + 1)))
  ≡⟨ cong (λ e → e + (choose x (suc (n + 1)) + choose (suc (x + 1)) (suc (n + 1)))) (sym (+-assoc (choose x (n + 1)) _ _)) ⟩
    ((choose x (n + 1) + n * choose (x + 1) ((n + 1))) + n * choose (x + 1) (suc (n + 1))) + (choose x (suc (n + 1)) + choose (suc (x + 1)) (suc (n + 1)))
  ≡⟨ +-assoc ((choose x (n + 1) + n * choose (x + 1) ((n + 1)))) _ _ ⟩
    (choose x (n + 1) + n * choose (x + 1) (n + 1)) + (n * choose (x + 1) (suc (n + 1)) + (choose x (suc (n + 1)) + choose (suc (x + 1)) (suc (n + 1))))
  ≡⟨ cong (λ e → e + (n * choose (x + 1) (suc (n + 1)) + (choose x (suc (n + 1)) + choose (suc (x + 1)) (suc (n + 1))))) (lemma0 x n) ⟩
    x * choose x n + (n * choose (x + 1) (suc (n + 1)) + (choose x (suc (n + 1)) + choose (suc (x + 1)) (suc (n + 1))))
  ≡⟨ cong (λ e → x * choose x n + e) (begin
        n * choose (x + 1) (suc (n + 1)) + (choose x (suc (n + 1)) + choose (suc (x + 1)) (suc (n + 1)))
      ≡⟨ sym (+-assoc (n * choose (x + 1) (suc (n + 1))) _ _) ⟩
        (n * choose (x + 1) (suc n + 1) + choose x (suc n + 1)) + choose (suc (x + 1)) (suc (n + 1))
      ≡⟨ refl ⟩
        (n * choose (x + 1) (suc n + 1) + choose x (suc n + 1)) + (choose (x + 1) (suc n + 1) + choose (x + 1) (n + 1))
      ≡⟨ sym (+-assoc (n * choose (x + 1) (suc n + 1) + choose x (suc n + 1)) _ _) ⟩
        ((n * choose (x + 1) (suc n + 1) + choose x (suc n + 1)) + choose (x + 1) (suc n + 1)) + choose (x + 1) (n + 1)
      ≡⟨ cong (λ e → e + choose (x + 1) (n + 1)) (+-comm (n * choose (x + 1) (suc n + 1) + choose x (suc n + 1)) _) ⟩
        (choose (x + 1) (suc n + 1) + (n * choose (x + 1) (suc n + 1) + choose x (suc n + 1))) + choose (x + 1) (n + 1)
      ≡⟨ cong (λ e → e + choose (x + 1) (n + 1)) (sym (+-assoc (choose (x + 1) (suc n + 1)) _ _)) ⟩
        ((choose (x + 1) (suc n + 1) + n * choose (x + 1) (suc n + 1)) + choose x (suc n + 1)) + choose (x + 1) (n + 1)
      ≡⟨ cong (λ e → ((e + n * choose (x + 1) (suc n + 1)) + choose x (suc n + 1)) + choose (x + 1) (n + 1)) (sym (trans (*-comm 1 (choose (x + 1) (suc n + 1))) (*-right-identity (choose (x + 1) (suc n + 1))))) ⟩
        ((1 * choose (x + 1) (suc n + 1) + n * choose (x + 1) (suc n + 1)) + choose x (suc n + 1)) + choose (x + 1) (n + 1)
      ≡⟨ cong (λ e → (e + choose x (suc n + 1)) + choose (x + 1) (n + 1)) (sym (distribʳ-*-+ (choose (x + 1) (suc n + 1)) 1 n)) ⟩
        (((1 + n) * choose (x + 1) (suc n + 1)) + choose x (suc n + 1)) + choose (x + 1) (n + 1)
      ≡⟨ refl ⟩
        (((suc n) * choose (x + 1) (suc n + 1)) + choose x (suc n + 1)) + choose (x + 1) (n + 1)
      ≡⟨ cong (λ e → e + choose (x + 1) (n + 1)) (+-comm (((suc n) * choose (x + 1) (suc n + 1))) _) ⟩
        (choose x (suc n + 1) + ((suc n) * choose (x + 1) (suc n + 1))) + choose (x + 1) (n + 1)
      ≡⟨ cong (λ e → e + choose (x + 1) (n + 1)) (lemma0 x (suc n)) ⟩
        (x * choose x (suc n)) + choose (x + 1) (n + 1)
      ≡⟨ cong (λ e → (x * choose x (suc n)) + choose (x + 1) e) (+-comm n 1) ⟩
        x * choose x (suc n) + choose (x + 1) (suc n)
      ≡⟨ cong (λ e → x * choose x (suc n) + choose e (suc n)) (+-comm x 1) ⟩
        x * choose x (suc n) + choose (suc x) (suc n)
      ∎) ⟩
    x * choose x n + (x * choose x (suc n) + choose (suc x) (suc n))
  ≡⟨ sym (+-assoc (x * choose x n) _ _) ⟩
    (x * choose x n + x * choose x (suc n)) + choose (suc x) (suc n)
  ≡⟨ cong (λ e → e + choose (suc x) (suc n)) (+-comm (x * choose x n) _) ⟩
    (x * choose x (suc n) + x * choose x n) + choose (suc x) (suc n)
  ≡⟨ cong (λ e → e + choose (suc x) (suc n)) (sym (distribˡ-*-+ x _ _)) ⟩
    x * (choose x (suc n) + choose x n) + choose (suc x) (suc n)
  ≡⟨ +-comm (x * (choose x (suc n) + choose x n)) _ ⟩
    choose (suc x) (suc n) + x * (choose x (suc n) + choose x n)
  ≡⟨ refl ⟩
    choose (suc x) (suc n) + x * (choose x (suc n) + choose x n)
  ≡⟨ refl ⟩
    choose (suc x) (suc n) + x * choose (suc x) (suc n)
  ≡⟨ refl ⟩
    (suc x) * choose (suc x) (suc n)
  ∎

lemma : ∀ x n k
        → (prf : k ≤ n)
        → (k + 1) * choose (x + k) (n + 1) + (subtract n k prf) * choose (x + k + 1) (n + 1)
        ≡ x * choose (x + k) n
lemma x n zero prf rewrite +-right-identity x =
  begin
    (0 + 1) * choose x (n + 1) + (subtract n 0 prf) * choose (x + 1) (n + 1)
  ≡⟨ refl ⟩
    1 * choose x (n + 1) + n * choose (x + 1) (n + 1)
  ≡⟨ cong (λ e → e + n * choose (x + 1) (n + 1)) (trans (*-comm 1 (choose x (n + 1))) (*-right-identity (choose x (n + 1)))) ⟩
    choose x (n + 1) + n * choose (x + 1) (n + 1)
  ≡⟨ lemma0 x n ⟩
    x * choose x n
  ∎
lemma zero zero (suc k) ()
lemma zero (suc n) (suc k) (s≤s prf) =
  begin
    (suc k + 1) * choose (0 + suc k) (suc n + 1) + (subtract n k prf) * choose (0 + suc k + 1) (suc n + 1)
  ≡⟨ refl ⟩
    (suc k + 1) * choose (suc k) (suc n + 1) + (subtract n k prf) * choose (suc k + 1) (suc n + 1)
  ≡⟨ {!!} ⟩
    0
  ≡⟨ refl ⟩
    0 * choose (0 + suc k) (suc n)
  ∎
-- lemma (suc zero) zero zero z≤n = refl
-- lemma (suc (suc x)) zero zero z≤n rewrite +-right-identity x =
--   begin
--     choose (suc x) 1 + 1 + 0 + 0
--   ≡⟨ +-right-identity _ ⟩
--     choose (suc x) 1 + 1 + 0
--   ≡⟨ +-right-identity _ ⟩
--     choose (suc x) 1 + 1
--   ≡⟨ cong  (λ e → e + 1)(choose-lem-1 x) ⟩
--     (suc x) + 1
--   ≡⟨ +-comm (suc x) 1 ⟩
--     suc (suc x)
--   ≡⟨ cong (λ e → suc (suc e)) (sym (*-right-identity x)) ⟩
--     suc (suc x * 1)
--   ∎
-- lemma (suc x) zero (suc k) ()
-- lemma (suc x) (suc n) zero z≤n rewrite +-right-identity x =
--   begin
--     1 * choose (suc x) (suc n + 1) + (suc n) * choose (suc x + 1) (suc n + 1)
--   ≡⟨ cong (λ e → e + (subtract (suc n) 0 z≤n) * choose (suc x + 1) (suc n + 1)) (trans (*-comm 1 (choose (suc x) (suc n + 1))) (*-right-identity (choose (suc x) (suc n + 1)))) ⟩
--     choose (suc x) (suc (n + 1)) + (suc n) * choose (suc (x + 1)) (suc (n + 1))
--   ≡⟨ refl ⟩
--     (choose x (suc (n + 1)) + choose x (n + 1)) + (suc n) * choose (suc (x + 1)) (suc (n + 1))
--   ≡⟨ refl ⟩
--     (choose x (suc (n + 1)) + choose x (n + 1)) + (choose (suc (x + 1)) (suc (n + 1)) + n * choose (suc (x + 1)) (suc (n + 1)))
--   ≡⟨ refl ⟩
--     (choose x (suc (n + 1)) + choose x (n + 1)) + (choose (suc (x + 1)) (suc (n + 1)) + n * (choose (x + 1) (suc (n + 1)) + choose (x + 1) (n + 1)))
--   ≡⟨ cong (λ e → (choose x (suc (n + 1)) + choose x (n + 1)) + (choose (suc (x + 1)) (suc (n + 1)) + e)) (distribˡ-*-+ n _ _) ⟩
--     (choose x (suc (n + 1)) + choose x (n + 1)) + (choose (suc (x + 1)) (suc (n + 1)) + (n * choose (x + 1) (suc (n + 1)) + n * choose (x + 1) (n + 1)))
--   ≡⟨ +-assoc (choose x (suc (n + 1))) _ _  ⟩
--     choose x (suc (n + 1)) + (choose x (n + 1) + (choose (suc (x + 1)) (suc (n + 1)) + (n * choose (x + 1) (suc (n + 1)) + n * choose (x + 1) (n + 1))))
--   ≡⟨ cong (λ e → choose x (suc (n + 1)) + e) (+-comm (choose x (n + 1)) _) ⟩
--     choose x (suc (n + 1)) + ((choose (suc (x + 1)) (suc (n + 1)) + (n * choose (x + 1) (suc (n + 1)) + n * choose (x + 1) (n + 1))) + choose x (n + 1))
--   ≡⟨ cong (λ e → choose x (suc (n + 1)) + e) (+-assoc (choose (suc (x + 1)) (suc (n + 1))) _ _) ⟩
--     choose x (suc (n + 1)) + (choose (suc (x + 1)) (suc (n + 1)) + ((n * choose (x + 1) (suc (n + 1)) + n * choose (x + 1) (n + 1)) + choose x (n + 1)))
--   ≡⟨ cong (λ e → choose x (suc (n + 1)) + (choose (suc (x + 1)) (suc (n + 1)) + e)) ((+-assoc (n * choose (x + 1) (suc (n + 1))) _ _)) ⟩
--     choose x (suc (n + 1)) + (choose (suc (x + 1)) (suc (n + 1)) + (n * choose (x + 1) (suc (n + 1)) + (n * choose (x + 1) (n + 1) + choose x (n + 1))))
--   ≡⟨ cong (λ e → choose x (suc (n + 1)) + (choose (suc (x + 1)) (suc (n + 1)) + (n * choose (x + 1) (suc (n + 1)) + e))) (+-comm (n * choose (x + 1) (n + 1)) _) ⟩
--     choose x (suc (n + 1)) + (choose (suc (x + 1)) (suc (n + 1)) + (n * choose (x + 1) (suc (n + 1)) + (choose x (n + 1) + n * choose (x + 1) (n + 1))))
--   ≡⟨ cong (λ e → choose x (suc (n + 1)) + (choose (suc (x + 1)) (suc (n + 1)) + (n * choose (x + 1) (suc (n + 1)) + e))) {!lemma x n zero z≤n!} ⟩
--     choose x (suc (n + 1)) + (choose (suc (x + 1)) (suc (n + 1)) + (n * choose (x + 1) (suc (n + 1)) + (x * choose x n)))
--   ≡⟨ {!!} ⟩
--     choose (suc x) (suc n) + (x * choose x (suc n) + x * choose x n)
--   ≡⟨ cong (λ e → choose (suc x) (suc n) + e) (sym (distribˡ-*-+ x _ _)) ⟩
--     choose (suc x) (suc n) + x * (choose x (suc n) + choose x n)
--   ≡⟨ refl ⟩
--     choose (suc x) (suc n) + x * choose (suc x) (suc n)
--   ≡⟨ refl ⟩
--     (suc x) * choose (suc x) (suc n)
--   ∎
lemma (suc x) (suc n) (suc k) (s≤s prf) =
  begin
    (suc k + 1) * choose (suc x + suc k) (suc n + 1) + (subtract n k prf) * choose (suc x + suc k + 1) (suc n + 1)
  ≡⟨ {!!} ⟩
    (suc x) * choose (suc x + suc k) (suc n)
  ∎

