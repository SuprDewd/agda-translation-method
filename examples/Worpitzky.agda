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

choose : ℕ → ℕ → ℕ
choose zero zero = 1
choose zero (suc k) = 0
choose (suc n) zero = 1
choose (suc n) (suc k) = choose n (suc k) + choose n k

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

