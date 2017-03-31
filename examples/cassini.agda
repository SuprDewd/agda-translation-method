module cassini where

open import Function

open import Translate
open import Translate.Solver
-- open import Translate.Fibonacci
open import Translate.Combinatorics
open import Translate.Common
open import Translate.EqReasoning
open import Translate.Arithmetic
open import Translate.Bijection using (getTo)
open import Translate.Tools

open import Data.Product

one = suc zero
two = suc one
three = suc two

:one :two :three : ∀ {n} → :Expr n
:one = :suc :zero
:two = :suc :one
:three = :suc :two

fin : ℕ → Expr
fin ℕzero = zero
fin (ℕsuc n) = suc (fin n)

fin-value : ∀ n → n P≡ value (fin n)
fin-value ℕzero = Prefl
fin-value (ℕsuc n) rewrite Psym (fin-value n) = Prefl

import Data.Nat.Properties.Simple as NPS
import Data.Nat.Properties
open Data.Nat.Properties.SemiringSolver
  using (con)
  renaming (solve to ℕsolve
           ; _:+_ to _:ℕ+_
           ; _:*_ to _:ℕ*_
           -- ; :zero to :ℕzero
           -- ; :suc to :ℕsuc
           )

private
  lem1 : ∀ k → k ℕ+ (1 ℕ+ (k ℕ+ ℕzero)) ℕ+ 2 P≡ 1 ℕ+ (k ℕ+ (k ℕ+ ℕzero) ℕ+ 2)
  lem1 = ℕsolve 1 (λ k → k :ℕ+ (con 1 :ℕ+ (k :ℕ+ con 0)) :ℕ+ con 2 , con 1 :ℕ+ (k :ℕ+ (k :ℕ+ con 0) :ℕ+ con 2)) Prefl

  lem2 : ∀ a b → a ℕ* (ℕsuc b) P≡ a ℕ* b ℕ+ a
  lem2 a b = Ptrans (NPS.*-comm a (ℕsuc b)) (Ptrans (NPS.+-comm a (b ℕ* a)) (Pcong (λ x → x ℕ+ a) (NPS.*-comm b a)))

mutual

  cassini-odd : ∀ k → fib (2 ℕ* k ℕ+ 2) * fib (2 ℕ* k)
                    ≡ fib (2 ℕ* k ℕ+ 1) * fib (2 ℕ* k ℕ+ 1) + one
  cassini-odd ℕzero = proof Prefl (mkBij to from to-from from-to)
    where
      -- TODO: There are two possible base cases. Try both of them?
      to : (FibStr 2 × FibStr 0) → (FibStr 1 × FibStr 1 ⊔ Maybe ⊥)
      -- to (([] ∷1 ∷1) , []) = inj₂ nothing
      -- to (([] ∷2) , []) = inj₁ (([] ∷1) , ([] ∷1))
      to (([] ∷1 ∷1) , []) = inj₁ (([] ∷1) , ([] ∷1))
      to (([] ∷2) , []) = inj₂ nothing

      from : (FibStr 1 × FibStr 1 ⊔ Maybe ⊥) → (FibStr 2 × FibStr 0)
      -- from (inj₂ nothing) = ([] ∷1 ∷1) , []
      -- from (inj₁ (([] ∷1) , ([] ∷1))) = ([] ∷2) , []
      from (inj₂ nothing) = ([] ∷2) , []
      from (inj₁ (([] ∷1) , ([] ∷1))) = ([] ∷1 ∷1) , []
      from (inj₂ (just ()))

      to-from : ∀ y → to (from y) P≡ y
      to-from (inj₁ (([] ∷1) , ([] ∷1))) = Prefl
      to-from (inj₂ (just ()))
      to-from (inj₂ nothing) = Prefl

      from-to : ∀ x → from (to x) P≡ x
      from-to ((([] ∷1) ∷1) , []) = Prefl
      from-to (([] ∷2) , []) = Prefl

  cassini-odd (ℕsuc k) =
    begin
      fib (2 ℕ* (ℕsuc k) ℕ+ 2) * fib (2 ℕ* (ℕsuc k))
    -- P≡⟨ Pcong (λ x → fib x * fib (2 ℕ* (ℕsuc k))) (NPS.+-comm (2 ℕ* (ℕsuc k)) 2) ⟩
    --   (fib (ℕsuc (ℕsuc (2 ℕ* (ℕsuc k))))) * fib (2 ℕ* (ℕsuc k))
    -- ≡⟨ *-cong fib-def refl ⟩
    --   (fib (ℕsuc (2 ℕ* (ℕsuc k))) + fib (2 ℕ* (ℕsuc k))) * fib (2 ℕ* (ℕsuc k))
    -- ≡⟨ distribʳ-*-+ ⟩
    --   fib (ℕsuc (2 ℕ* (ℕsuc k))) * fib (2 ℕ* (ℕsuc k)) + fib (2 ℕ* (ℕsuc k)) * fib (2 ℕ* (ℕsuc k))
    -- P≡⟨ Pcong (λ x → fib (ℕsuc (2 ℕ* (ℕsuc k))) * fib (2 ℕ* (ℕsuc k)) + fib x * fib (2 ℕ* (ℕsuc k))) (lem2 2 k) ⟩
    --   fib (ℕsuc (2 ℕ* (ℕsuc k))) * fib (2 ℕ* (ℕsuc k)) + fib (2 ℕ* k ℕ+ 2) * fib (2 ℕ* (ℕsuc k))
    -- P≡⟨ Pcong (λ x → fib (ℕsuc (2 ℕ* (ℕsuc k))) * fib (2 ℕ* (ℕsuc k)) + fib (2 ℕ* k ℕ+ 2) * fib x) (lem2 2 k) ⟩
    ≡⟨ clem1 ⟩
      fib (ℕsuc (2 ℕ* (ℕsuc k))) * fib (2 ℕ* (ℕsuc k)) + fib (2 ℕ* k ℕ+ 2) * fib (2 ℕ* k ℕ+ 2)
    ≡⟨ +-cong refl (cassini-even k) ⟩
      fib (ℕsuc (2 ℕ* (ℕsuc k))) * fib (2 ℕ* (ℕsuc k)) + (fib (2 ℕ* k ℕ+ 3) * fib (2 ℕ* k ℕ+ 1) + one)
    ≡⟨ clem2 ⟩
    -- ≡⟨ sym +-assoc ⟩
    --   (fib (ℕsuc (2 ℕ* (ℕsuc k))) * fib (2 ℕ* (ℕsuc k)) + fib (2 ℕ* k ℕ+ 3) * fib (2 ℕ* k ℕ+ 1)) + one
    -- P≡⟨ Pcong (λ x → (fib x * fib (2 ℕ* (ℕsuc k)) + fib (2 ℕ* k ℕ+ 3) * fib (2 ℕ* k ℕ+ 1)) + one) (NPS.+-comm 1 (2 ℕ* (ℕsuc k))) ⟩
    --   (fib ((2 ℕ* (ℕsuc k)) ℕ+ 1) * fib (2 ℕ* (ℕsuc k)) + fib (2 ℕ* k ℕ+ 3) * fib (2 ℕ* k ℕ+ 1)) + one
    -- P≡⟨ Pcong (λ x → (fib (x ℕ+ 1) * fib (2 ℕ* (ℕsuc k)) + fib (2 ℕ* k ℕ+ 3) * fib (2 ℕ* k ℕ+ 1)) + one) (lem2 2 k) ⟩
    --   (fib ((2 ℕ* k ℕ+ 2) ℕ+ 1) * fib (2 ℕ* (ℕsuc k)) + fib (2 ℕ* k ℕ+ 3) * fib (2 ℕ* k ℕ+ 1)) + one
    -- P≡⟨ Pcong (λ x → (fib x * fib (2 ℕ* (ℕsuc k)) + fib (2 ℕ* k ℕ+ 3) * fib (2 ℕ* k ℕ+ 1)) + one) (NPS.+-assoc (2 ℕ* k) 2 1) ⟩
    --   (fib (2 ℕ* k ℕ+ 3) * fib (2 ℕ* (ℕsuc k)) + fib (2 ℕ* k ℕ+ 3) * fib (2 ℕ* k ℕ+ 1)) + one
    -- ≡⟨ +-cong (sym distribˡ-*-+) refl ⟩
    --   fib (2 ℕ* k ℕ+ 3) * (fib (2 ℕ* (ℕsuc k)) + fib (2 ℕ* k ℕ+ 1)) + one
    -- P≡⟨ Pcong (λ x → fib (2 ℕ* k ℕ+ 3) * (fib x + fib (2 ℕ* k ℕ+ 1)) + one) (lem2 2 k) ⟩
    --   fib (2 ℕ* k ℕ+ 3) * (fib (2 ℕ* k ℕ+ 2) + fib (2 ℕ* k ℕ+ 1)) + one
    -- P≡⟨ Pcong (λ x → fib (2 ℕ* k ℕ+ 3) * (fib x + fib (2 ℕ* k ℕ+ 1)) + one) (NPS.+-suc (2 ℕ* k) 1) ⟩
    --   fib (2 ℕ* k ℕ+ 3) * (fib (ℕsuc (2 ℕ* k ℕ+ 1)) + fib (2 ℕ* k ℕ+ 1)) + one
    -- ≡⟨ +-cong (*-cong refl (sym fib-def)) refl ⟩
    --   fib (2 ℕ* k ℕ+ 3) * (fib (ℕsuc (ℕsuc (2 ℕ* k ℕ+ 1)))) + one
    -- P≡⟨ Pcong (λ x → fib (2 ℕ* k ℕ+ 3) * (fib x) + one) (NPS.+-comm 2 (2 ℕ* k ℕ+ 1)) ⟩
    --   fib (2 ℕ* k ℕ+ 3) * (fib ((2 ℕ* k ℕ+ 1) ℕ+ 2)) + one
    -- P≡⟨ Pcong (λ x → fib (2 ℕ* k ℕ+ 3) * (fib x) + one) (NPS.+-assoc (2 ℕ* k) 1 2) ⟩
    --   fib (2 ℕ* k ℕ+ 3) * fib (2 ℕ* k ℕ+ 3) + one
    -- P≡⟨ Pcong (λ x → fib x * fib (2 ℕ* k ℕ+ 3) + one) (Psym (NPS.+-assoc (2 ℕ* k) 2 1)) ⟩
    --   fib ((2 ℕ* k ℕ+ 2) ℕ+ 1) * fib (2 ℕ* k ℕ+ 3) + one
    -- P≡⟨ Pcong (λ x → fib (x ℕ+ 1) * fib (2 ℕ* k ℕ+ 3) + one) (Psym (lem2 2 k)) ⟩
    --   fib ((2 ℕ* (ℕsuc k)) ℕ+ 1) * fib (2 ℕ* k ℕ+ 3) + one
    -- P≡⟨ Pcong (λ x → fib ((2 ℕ* (ℕsuc k)) ℕ+ 1) * fib x + one) (Psym (NPS.+-assoc (2 ℕ* k) 2 1)) ⟩
    --   fib ((2 ℕ* (ℕsuc k)) ℕ+ 1) * fib ((2 ℕ* k ℕ+ 2) ℕ+ 1) + one
    -- P≡⟨ Pcong (λ x → fib ((2 ℕ* (ℕsuc k)) ℕ+ 1) * fib (x ℕ+ 1) + one) (Psym (lem2 2 k)) ⟩
      fib (2 ℕ* (ℕsuc k) ℕ+ 1) * fib (2 ℕ* (ℕsuc k) ℕ+ 1) + one
    ∎
    where
      clem1 : fib (ℕsuc (k ℕ+ ℕsuc (k ℕ+ ℕzero) ℕ+ 2)) * fib (ℕsuc (k ℕ+ ℕsuc (k ℕ+ ℕzero))) ≡ (fib (ℕsuc (ℕsuc (k ℕ+ ℕsuc (k ℕ+ ℕzero)))) * fib (ℕsuc (k ℕ+ ℕsuc (k ℕ+ ℕzero))) + fib (k ℕ+ (k ℕ+ ℕzero) ℕ+ 2) * fib (k ℕ+ (k ℕ+ ℕzero) ℕ+ 2))
      clem1 rewrite fin-value k = solve 1 (λ x → :fib (:suc (x :+ :suc (x :+ :zero) :+ :two)) :* :fib (:suc (x :+ :suc (x :+ :zero))) := (:fib (:suc (:suc (x :+ :suc (x :+ :zero)))) :* :fib (:suc (x :+ :suc (x :+ :zero))) :+ :fib (x :+ (x :+ :zero) :+ :two) :* :fib (x :+ (x :+ :zero) :+ :two))) refl (fin k)

      clem2 : fib (ℕsuc (ℕsuc (k ℕ+ ℕsuc (k ℕ+ ℕzero)))) * fib (ℕsuc (k ℕ+ ℕsuc (k ℕ+ ℕzero))) + (fib (k ℕ+ (k ℕ+ ℕzero) ℕ+ 3) * fib (k ℕ+ (k ℕ+ ℕzero) ℕ+ 1) + one) ≡ (fib (ℕsuc (k ℕ+ ℕsuc (k ℕ+ ℕzero) ℕ+ 1)) * fib (ℕsuc (k ℕ+ ℕsuc (k ℕ+ ℕzero) ℕ+ 1)) + one)
      clem2 rewrite fin-value k = solve 1 (λ x → :fib (:suc (:suc (x :+ :suc (x :+ :zero)))) :* :fib (:suc (x :+ :suc (x :+ :zero))) :+ (:fib (x :+ (x :+ :zero) :+ :three) :* :fib (x :+ (x :+ :zero) :+ :one) :+ :one) := (:fib (:suc (x :+ :suc (x :+ :zero) :+ :one)) :* :fib (:suc (x :+ :suc (x :+ :zero) :+ :one)) :+ :one)) refl (fin k)

  cassini-even : ∀ k → fib (2 ℕ* k ℕ+ 2) * fib (2 ℕ* k ℕ+ 2)
                     ≡ fib (2 ℕ* k ℕ+ 3) * fib (2 ℕ* k ℕ+ 1) + one
  cassini-even k =
    begin
      fib (2 ℕ* k ℕ+ 2) * fib (2 ℕ* k ℕ+ 2)
    -- P≡⟨ Pcong (λ x → fib (2 ℕ* k ℕ+ 2) * fib x) (NPS.+-comm (2 ℕ* k) 2) ⟩
    --   fib (2 ℕ* k ℕ+ 2) * fib (ℕsuc (ℕsuc (2 ℕ* k)))
    -- ≡⟨ *-cong refl fib-def ⟩
    --   fib (2 ℕ* k ℕ+ 2) * (fib (ℕsuc (2 ℕ* k)) + fib (2 ℕ* k))
    -- ≡⟨ distribˡ-*-+ ⟩
    ≡⟨ clem1 ⟩
      fib (2 ℕ* k ℕ+ 2) * fib (ℕsuc (2 ℕ* k)) + fib (2 ℕ* k ℕ+ 2) * fib (2 ℕ* k)
    ≡⟨ +-cong refl (cassini-odd k) ⟩
      fib (2 ℕ* k ℕ+ 2) * fib (ℕsuc (2 ℕ* k)) + (fib (2 ℕ* k ℕ+ 1) * fib (2 ℕ* k ℕ+ 1) + one)
    ≡⟨ clem2 ⟩
    -- ≡⟨ sym +-assoc ⟩
    --   (fib (2 ℕ* k ℕ+ 2) * fib (ℕsuc (2 ℕ* k)) + fib (2 ℕ* k ℕ+ 1) * fib (2 ℕ* k ℕ+ 1)) + one
    -- P≡⟨ Pcong (λ x → (fib (2 ℕ* k ℕ+ 2) * fib x + fib (2 ℕ* k ℕ+ 1) * fib (2 ℕ* k ℕ+ 1)) + one) (NPS.+-comm 1 (2 ℕ* k)) ⟩
    --   (fib (2 ℕ* k ℕ+ 2) * fib (2 ℕ* k ℕ+ 1) + fib (2 ℕ* k ℕ+ 1) * fib (2 ℕ* k ℕ+ 1)) + one
    -- ≡⟨ +-cong (sym distribʳ-*-+) refl ⟩
    --   (fib (2 ℕ* k ℕ+ 2) + fib (2 ℕ* k ℕ+ 1)) * fib (2 ℕ* k ℕ+ 1) + one
    --   P≡⟨ Pcong (λ x → (fib x + fib (2 ℕ* k ℕ+ 1)) * fib (2 ℕ* k ℕ+ 1) + one) (NPS.+-suc (2 ℕ* k) 1) ⟩
    --   (fib (ℕsuc (2 ℕ* k ℕ+ 1)) + fib (2 ℕ* k ℕ+ 1)) * fib (2 ℕ* k ℕ+ 1) + one
    -- ≡⟨ +-cong (*-cong (sym fib-def) refl) refl ⟩
    --   fib (ℕsuc (ℕsuc (2 ℕ* k ℕ+ 1))) * fib (2 ℕ* k ℕ+ 1) + one
    -- P≡⟨ Pcong (λ x → fib x * fib (2 ℕ* k ℕ+ 1) + one) (NPS.+-comm 2 (k ℕ+ (k ℕ+ ℕzero) ℕ+ 1)) ⟩
    --   fib ((2 ℕ* k ℕ+ 1) ℕ+ 2) * fib (2 ℕ* k ℕ+ 1) + one
    -- P≡⟨ Pcong (λ x → fib x * fib (2 ℕ* k ℕ+ 1) + one) (NPS.+-assoc (2 ℕ* k) 1 2) ⟩
      fib (2 ℕ* k ℕ+ 3) * fib (2 ℕ* k ℕ+ 1) + one
    ∎
    where
      clem1 : fib (k ℕ+ (k ℕ+ ℕzero) ℕ+ 2) * fib (k ℕ+ (k ℕ+ ℕzero) ℕ+ 2) ≡ (fib (k ℕ+ (k ℕ+ ℕzero) ℕ+ 2) * fib (ℕsuc (k ℕ+ (k ℕ+ ℕzero))) + fib (k ℕ+ (k ℕ+ ℕzero) ℕ+ 2) * fib (k ℕ+ (k ℕ+ ℕzero)))
      clem1 rewrite fin-value k = solve 1 (λ x → :fib (:two :* x :+ :two) :* :fib (:two :* x :+ :two) := :fib (:two :* x :+ :two) :* :fib (:suc (:two :* x)) :+ :fib (:two :* x :+ :two) :* :fib (:two :* x)) refl (fin k)

      clem2 : fib (k ℕ+ (k ℕ+ ℕzero) ℕ+ 2) * fib (ℕsuc (k ℕ+ (k ℕ+ ℕzero))) + (fib (k ℕ+ (k ℕ+ ℕzero) ℕ+ 1) * fib (k ℕ+ (k ℕ+ ℕzero) ℕ+ 1) + one) ≡ (fib (k ℕ+ (k ℕ+ ℕzero) ℕ+ 3) * fib (k ℕ+ (k ℕ+ ℕzero) ℕ+ 1) + one)
      clem2 rewrite fin-value k = solve 1 (λ x → :fib (x :+ (x :+ :zero) :+ :two) :* :fib (:suc (x :+ (x :+ :zero))) :+ (:fib (x :+ (x :+ :zero) :+ :one) :* :fib (x :+ (x :+ :zero) :+ :one) :+ :one) := (:fib (x :+ (x :+ :zero) :+ :three) :* :fib (x :+ (x :+ :zero) :+ :one) :+ :one)) refl (fin k)

cassini-even-direct : ∀ k → lift (fib (2 ℕ* k ℕ+ 2) * fib (2 ℕ* k ℕ+ 2)) → lift (fib (2 ℕ* k ℕ+ 3) * fib (2 ℕ* k ℕ+ 1) + one)
cassini-even-direct k rewrite NPS.+-comm (2 ℕ* k) 3 | NPS.+-comm (2 ℕ* k) 2 | NPS.+-comm (2 ℕ* k) 1  = to k
  where
    units : ∀ k → FibStr k
    units ℕzero = []
    units (ℕsuc x) = (units x) ∷1

    fix : ∀ k → ℕsuc k ℕ+ 1 ℕ* ℕsuc k P≡ ℕsuc (ℕsuc (k ℕ+ k))
    fix k = Ptrans (Pcong (λ x → ℕsuc (k ℕ+ ℕsuc x)) (NPS.+-right-identity k)) (Pcong (λ x → ℕsuc x) (NPS.+-comm k (ℕsuc k)))

    -- to : ∀ k → FibStr (ℕsuc (ℕsuc (2 ℕ* k))) × FibStr (ℕsuc (ℕsuc (2 ℕ* k))) → FibStr (ℕsuc (ℕsuc (ℕsuc (2 ℕ* k)))) × FibStr (ℕsuc (2 ℕ* k)) ⊔ Maybe ⊥
    -- λ
    -- { (xs ∷1 ∷2 , ys ∷1) → inj₁ (xs ∷2 ∷1 ∷1 , ys)
    -- ; _ → inj₁ ((units ((ℕsuc (ℕsuc (ℕsuc (ℕsuc (ℕsuc (k ℕ+ k)))))))) , (units ((ℕsuc (ℕsuc (ℕsuc (k ℕ+ k)))))))
    -- }
    -- to2 : (FibStr (ℕsuc (ℕsuc (ℕsuc (ℕsuc (ℕsuc (k ℕ+ k))))))) × (FibStr (ℕsuc (ℕsuc (ℕsuc (k ℕ+ k))))) ⊔ Maybe ⊥


    fixit : ∀ {k} → FibStr (ℕsuc (ℕsuc (k ℕ+ k))) → FibStr (ℕsuc (ℕsuc (k ℕ+ (k ℕ+ ℕzero))))
    fixit {k} xs rewrite NPS.+-right-identity k = xs

    fixtp : ∀ k → (ℕsuc (ℕsuc (ℕsuc (ℕsuc (ℕsuc (k ℕ+ 0 ℕ+ (k ℕ+ 0 ℕ+ 0))))))) P≡ (ℕsuc (ℕsuc (ℕsuc (ℕsuc (ℕsuc (k ℕ+ 0 ℕ+ (k ℕ+ 0)))))))
    fixtp = ℕsolve 1 (λ x → (con 1 :ℕ+ (con 1 :ℕ+ (con 1 :ℕ+ (con 1 :ℕ+ (con 1 :ℕ+ (x :ℕ+ con 0 :ℕ+ (x :ℕ+ con 0 :ℕ+ con 0))))))) , (con 1 :ℕ+  (con 1 :ℕ+ (con 1 :ℕ+ (con 1 :ℕ+ (con 1 :ℕ+ (x :ℕ+ con 0 :ℕ+ (x :ℕ+ con 0)))))))) Prefl

    fixit2 : ∀ {k} → FibStr (ℕsuc (ℕsuc (ℕsuc (ℕsuc (ℕsuc (k ℕ+ 0 ℕ+ (k ℕ+ 0 ℕ+ 0))))))) → FibStr (ℕsuc (ℕsuc (ℕsuc (ℕsuc (ℕsuc (k ℕ+ 0 ℕ+ (k ℕ+ 0)))))))
    fixit2 {k} xs rewrite fixtp k = xs

    fixtp2 : ∀ k → (ℕsuc (ℕsuc (ℕsuc (k ℕ+ 0 ℕ+ (k ℕ+ 0 ℕ+ 0))))) P≡ (ℕsuc (ℕsuc (ℕsuc (k ℕ+ 0 ℕ+ (k ℕ+ 0)))))
    fixtp2 = ℕsolve 1 (λ x → (con 1 :ℕ+ (con 1 :ℕ+ (con 1 :ℕ+ (x :ℕ+ con 0 :ℕ+ (x :ℕ+ con 0 :ℕ+ con 0))))) , (con 1 :ℕ+ (con 1 :ℕ+ (con 1 :ℕ+ (x :ℕ+ con 0 :ℕ+ (x :ℕ+ con 0)))))) Prefl

    fixit3 : ∀ {k} → FibStr (ℕsuc (ℕsuc (ℕsuc (k ℕ+ 0 ℕ+ (k ℕ+ 0 ℕ+ 0))))) → FibStr (ℕsuc (ℕsuc (ℕsuc (k ℕ+ 0 ℕ+ (k ℕ+ 0)))))
    fixit3 {k} xs rewrite fixtp2 k = xs

    mutual
      to2 : ∀ k → (FibStr (ℕsuc (ℕsuc (ℕsuc (ℕsuc (k ℕ+ k)))))) × (FibStr (ℕsuc (ℕsuc (ℕsuc (ℕsuc (k ℕ+ k)))))) → (FibStr (ℕsuc (ℕsuc (ℕsuc (ℕsuc (ℕsuc (k ℕ+ k))))))) × (FibStr (ℕsuc (ℕsuc (ℕsuc (k ℕ+ k))))) ⊔ Maybe ⊥
      -- to2 k (xs ∷1 ∷2 , ys ∷1) = inj₁ (xs ∷2 ∷1 ∷1 , ys)
      -- to2 k (xs ∷1 ∷1 , ys ∷2) = inj₁ (xs ∷2 ∷1 , ys ∷1)

      -- THIS SEEMS ALMOST CORRECT! Try doing this with big random examples.
      to2 k (xs ∷2 , ys ∷1 ∷1) with (to k (fixit {k} ys , fixit {k} xs))
      ... | inj₂ (just ())
      ... | inj₂ nothing = inj₂ nothing
      ... | inj₁ (xs' , ys') rewrite (Psym (NPS.+-right-identity k)) = inj₁ (fixit2 {k} (xs' ∷1 ∷1) , fixit3 {k} (ys' ∷1 ∷1))

      to2 k (xs ∷2 , ys ∷1) = inj₁ (xs ∷1 ∷1 ∷1 , ys)
      to2 k (xs ∷1 , ys ∷1) = inj₁ (xs ∷2 , ys)
      to2 k (xs ∷1 , ys ∷2) = inj₁ (ys ∷2 ∷1 , xs)

      to2 k (xs ∷1 ∷2 , ys ∷1 ∷2) = inj₁ (xs ∷2 ∷1 ∷1 , ys ∷2)
      to2 k (xs ∷1 ∷2 , ys ∷2 ∷2) = inj₁ (xs ∷2 ∷1 ∷1 , ys ∷2 ∷1)

      to2 k (xs ∷2 , ys ∷2) = inj₁ (xs ∷1 ∷1 ∷1 , ys ∷1)

      -- to2 k _ = inj₂ nothing

      to : ∀ k → FibStr (ℕsuc (ℕsuc (2 ℕ* k))) × FibStr (ℕsuc (ℕsuc (2 ℕ* k))) → FibStr (ℕsuc (ℕsuc (ℕsuc (2 ℕ* k)))) × FibStr (ℕsuc (2 ℕ* k)) ⊔ Maybe ⊥

      -- (xs ::1 , ys ::1) -> (xs ::2 , ys)
      -- to k (xs ∷1 , ys ∷1) = inj₁ (xs ∷2 , ys)
      -- (xs ::1 , ys ::2)  -> (ys ::2 ::1, xs)
      -- to k (xs ∷1 , ys ∷2) = inj₁ (ys ∷2 ∷1 , xs)
      -- (xs ::2 , ys ::2) -> (xs ::1 ::1 ::1 , ys ::1)
      -- to k (xs ∷2 , ys ∷2) = inj₁ (xs ∷1 ∷1 ∷1 , ys ∷1)

      to ℕzero ([] ∷2 , [] ∷1 ∷1) = inj₁ ([] ∷1 ∷1 ∷1 , [] ∷1)
      to ℕzero ([] ∷1 ∷1 , [] ∷1 ∷1) = inj₁ ([] ∷1 ∷2 , [] ∷1)
      to ℕzero ([] ∷1 ∷1 , [] ∷2) = inj₁ ([] ∷2 ∷1 , [] ∷1)


      to (ℕsuc k) xs rewrite fix k = to2 k xs

      to _ a = inj₂ nothing

      -- (xs ::2 , ys ::1 ::1 ::1) -> (ys ::2 ::1 ::1 , xs ::1)
      -- (xs ::1 ::1 ::2 , ys ::1 ::2) -> (xs ::2 ::1 ::1 , ys ::2)
      -- (xs ::1 ::2 , ys ::2 ::1) -> (ys ::1 ::1 ::1 ::1 , xs ::2)
      -- (xs ::1 ::2 , ys ::1 ::1) -> (ys ::1 ::1 ::1 ::1 , xs ::1)
      -- (xs ::1 ::2 , ys ::2 ::2) -> (xs ::2 ::1 ::1 , ys ::2 ::1)
      -- (xs ::2 , ys ::1) -> (xs ::1 ::1 ::1 , ys)
      -- (xs ::2 , ys ::1 ::1 ::1) -> (ys ::1 ::1 ::1 ::1 , ys ::1)
      -- (xs ::1 ::2 , ys ::2 ::1) -> (ys ::1 ::1 ::1 ::1 , xs ::2)
      -- (xs ::1 ::2 , ys ::1 ::2) -> (xs ::2 ::1 ::1 , ys ::2)
      -- (xs ::2 ::2 , ys ::2 ::2 ::1 ::1) -> (ys ::2 ::1 ::1 ::1 ::1 ::1 , xs ::1 ::1 ::1)
      -- (xs ::2 ::2 , ys ::1 ::2 ::1 ::1) -> (ys ::2 ::1 ::1 ::1 ::1 , xs ::1 ::1 ::1)
      -- (xs ::1 ::2 , ys ::1 ::2 ::1 ::1) -> nothing
      -- to k (a , b) = inj₂ nothing

-- XXxxXXx|XXx
--  XXxxXX|xXXx
tailSwap : ∀ {n} → FibStr (ℕsuc n) → FibStr (ℕsuc n) → FibStr (ℕsuc (ℕsuc n)) × FibStr n ⊔ Maybe ⊥
tailSwap {n} a₁ b₁ = tsl a₁ b₁
  where
    mutual
    -- XXxxXXx|XXx_
    --  XXxxXX|xXXx
      tsl : ∀ {k} → FibStr (ℕsuc k) → FibStr (ℕsuc k) → FibStr (ℕsuc (ℕsuc k)) × FibStr k ⊔ Maybe ⊥
      tsl a (b ∷1) = inj₁ (a ∷1 , b)
      tsl a (b ∷2) with tsr a b
      tsl a (b ∷2) | inj₁ (p , q) = inj₁ (p ∷2 , q)
      tsl a (b ∷2) | inj₂ nothing = inj₂ nothing
      tsl a (b ∷2) | inj₂ (just ())

      -- XXxxXXx|XXxx
      --  XXxxXX|xXX_
      tsr : ∀ {k} → FibStr (ℕsuc (ℕsuc k)) → FibStr k → FibStr (ℕsuc k) × FibStr (ℕsuc k) ⊔ Maybe ⊥
      tsr {ℕzero} (a ∷1) b = inj₁ (a , (b ∷1))
      tsr {ℕzero} ([] ∷2) [] = inj₂ nothing
      tsr {ℕsuc k} (a ∷1) b = inj₁ (a , b ∷1)
      tsr {ℕsuc k} (a ∷2) b with tsl a b
      tsr {ℕsuc k} (a ∷2) b | inj₁ (p , q) = inj₁ (p , q ∷2)
      tsr {ℕsuc k} (a ∷2) b | inj₂ nothing = inj₂ nothing
      tsr {ℕsuc k} (a ∷2) b | inj₂ (just ())

cassini-even-direct-2 : ∀ {n} → FibStr (n ℕ+ (n ℕ+ ℕzero) ℕ+ 2) × FibStr (n ℕ+ (n ℕ+ ℕzero) ℕ+ 2) → FibStr (n ℕ+ (n ℕ+ ℕzero) ℕ+ 3) × FibStr (n ℕ+ (n ℕ+ ℕzero) ℕ+ 1) ⊔ Maybe ⊥
cassini-even-direct-2 {n} (a , b) rewrite NPS.+-comm (n ℕ+ (n ℕ+ ℕzero)) 2 | NPS.+-comm (n ℕ+ (n ℕ+ ℕzero)) 3 | NPS.+-comm (n ℕ+ (n ℕ+ ℕzero)) 1 = tailSwap a b

module Runner where
  open import IO
  open import Data.List hiding (_++_)
  open import Data.String as S
  open import Data.Unit
  import Agda.Builtin.IO as BIO
  import Data.Colist as CL
  open import Data.Nat.Show using () renaming (show to ℕshow)

  infixl 1 _>>'_
  _>>'_ : ∀ {a} → {A : Set a} → {B : Set a} (m₁ : (IO B)) (m₂ : (IO A)) → IO A
  m₁ >>' m₂ = (♯ m₁) >> (♯ m₂)

  count : (start : ℕ) → CL.Colist ℕ
  count x = x CL.∷ ♯ count (ℕsuc x)

  main : BIO.IO ⊤
  main = run $ mapM′ (λ n →
                            -- putStrLn (ℕshow (2 ℕ* n ℕ+ 1)) >>'
                            -- show≡ (sym (cassini-odd n)) >>'
                            -- putStrLn "" >>'
                            putStrLn (ℕshow (2 ℕ* n ℕ+ 2)) >>'
                            -- show≡ (cassini-even n) >>'
                            check≡ (cassini-even n) (cassini-even-direct n) >>'
                            -- check≡ (cassini-even n) (cassini-even-direct-2 {n}) >>'
                            putStrLn "")
                     (count ℕzero) >>'
         return tt

open Runner using (main)
