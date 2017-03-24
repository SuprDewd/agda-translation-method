module thrice where

open import Function

open import Translate
open import Translate.Solver
-- open import Translate.Fibonacci
open import Translate.Combinatorics
open import Translate.Common
open import Translate.EqReasoning
open import Translate.Axioms
open import Translate.Bijection using (getTo)
open import Translate.Tools
open import Data.Maybe

import Data.Fin as F

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

thrice : ∀ {n} → three * fib (ℕsuc (ℕsuc n)) ≡ fib (ℕsuc (ℕsuc (ℕsuc (ℕsuc n)))) + fib n
thrice {0} = axiom Prefl (from-just (toBij {three * fib (ℕsuc (ℕsuc 0))}
                                           {fib (ℕsuc (ℕsuc (ℕsuc (ℕsuc 0)))) + fib 0} (
    ((nothing             , [] ∷1 ∷1) , inj₁ ([] ∷1 ∷1 ∷1 ∷1)) L∷
    ((nothing             , [] ∷2)    , inj₁ ([] ∷1 ∷1 ∷2)) L∷
    ((just nothing        , [] ∷1 ∷1) , inj₁ ([] ∷2 ∷1 ∷1)) L∷
    ((just nothing        , [] ∷2)    , inj₁ ([] ∷2 ∷2)) L∷
    ((just (just nothing) , [] ∷1 ∷1) , inj₁ ([] ∷1 ∷2 ∷1)) L∷
    ((just (just nothing) , [] ∷2)    , inj₂ []) L∷ L[]
  )))
thrice {1} = axiom Prefl (from-just (toBij {three * fib (ℕsuc (ℕsuc 1))}
                                           {fib (ℕsuc (ℕsuc (ℕsuc (ℕsuc 1)))) + fib 1} (
    ((nothing             , [] ∷1 ∷1 ∷1) , inj₁ ([] ∷1 ∷1 ∷1 ∷1 ∷1)) L∷
    ((nothing             , [] ∷1 ∷2)    , inj₁ ([] ∷1 ∷1 ∷1 ∷2)) L∷
    ((nothing             , [] ∷2 ∷1)    , inj₁ ([] ∷1 ∷1 ∷2 ∷1)) L∷
    ((just nothing        , [] ∷1 ∷1 ∷1) , inj₁ ([] ∷2 ∷1 ∷1 ∷1)) L∷
    ((just nothing        , [] ∷1 ∷2)    , inj₁ ([] ∷2 ∷1 ∷2)) L∷
    ((just nothing        , [] ∷2 ∷1)    , inj₁ ([] ∷2 ∷2 ∷1)) L∷
    ((just (just nothing) , [] ∷1 ∷1 ∷1) , inj₁ ([] ∷1 ∷2 ∷1 ∷1)) L∷
    ((just (just nothing) , [] ∷1 ∷2)    , inj₁ ([] ∷1 ∷2 ∷2)) L∷
    ((just (just nothing) , [] ∷2 ∷1)    , inj₂ ([] ∷1)) L∷ L[]
  )))
thrice {ℕsuc (ℕsuc n)} = -- rewrite fin-value n = solve 1 (λ x → :three :* :fib (:suc (:suc (:suc (:suc x)))) := :fib (:suc (:suc (:suc (:suc (:suc (:suc x)))))) :+ :fib (:suc (:suc x))) refl (fin n)
  begin
    three * fib (4 ℕ+ n)
  ≡⟨ *-cong refl fib-def ⟩
    three * (fib (3 ℕ+ n) + fib (2 ℕ+ n))
  ≡⟨ distribˡ-*-+ ⟩
    three * fib (3 ℕ+ n) + three * fib (2 ℕ+ n)
  ≡⟨ +-cong thrice thrice ⟩
    (fib (5 ℕ+ n) + fib (1 ℕ+ n)) + (fib (4 ℕ+ n) + fib n)
  ≡⟨ +-assoc ⟩
    fib (5 ℕ+ n) + (fib (1 ℕ+ n) + (fib (4 ℕ+ n) + fib n))
  ≡⟨ +-cong refl +-comm ⟩
    fib (5 ℕ+ n) + ((fib (4 ℕ+ n) + fib n) + fib (1 ℕ+ n))
  ≡⟨ +-cong refl +-assoc ⟩
    fib (5 ℕ+ n) + (fib (4 ℕ+ n) + (fib n + fib (1 ℕ+ n)))
  ≡⟨ +-cong refl (+-cong refl +-comm) ⟩
    fib (5 ℕ+ n) + (fib (4 ℕ+ n) + (fib (1 ℕ+ n) + fib n))
  ≡⟨ sym +-assoc ⟩
    (fib (5 ℕ+ n) + fib (4 ℕ+ n)) + (fib (1 ℕ+ n) + fib n)
  ≡⟨ +-cong (sym fib-def) (sym fib-def) ⟩
    fib (6 ℕ+ n) + fib (2 ℕ+ n)
  ∎

lemma : ∀ {n} → three * (fib (ℕsuc n) + fib n) ≡ (fib (ℕsuc n) + fib n + fib (ℕsuc n) + (fib (ℕsuc n) + fib n) + fib n)
lemma {n} rewrite fin-value n =
  solve 1 (λ n → :three :* (:fib (:suc n) :+ :fib n) :=
                (:fib (:suc n) :+ :fib n :+ :fib (:suc n) :+ (:fib (:suc n) :+ :fib n) :+ :fib n)) refl (fin n)

thrice' : ∀ {n} → three * fib (ℕsuc (ℕsuc n)) ≡ fib (ℕsuc (ℕsuc (ℕsuc (ℕsuc n)))) + fib n
thrice' {n} =
  begin
    three * fib (ℕsuc (ℕsuc n))
  ≡⟨ *-cong refl fib-def  ⟩
    three * (fib (ℕsuc n) + fib n)
  -- ≡⟨ distribˡ-*-+ ⟩
  --   three * fib (ℕsuc n) + three * fib n
  -- ≡⟨ +-cong *-comm  *-comm ⟩
  --   fib (ℕsuc n) * three + fib n * three
  -- ≡⟨ +-cong +-*-suc +-*-suc ⟩
  --   (fib (ℕsuc n) + fib (ℕsuc n) * two) + (fib n + fib n * two)
  -- ≡⟨ +-cong (+-cong refl +-*-suc) (+-cong refl +-*-suc) ⟩
  --   (fib (ℕsuc n) + (fib (ℕsuc n) + fib (ℕsuc n) * one)) + (fib n + (fib n + fib n * one))
  -- ≡⟨ +-cong (+-cong refl (+-cong refl *-right-identity)) (+-cong refl (+-cong refl *-right-identity)) ⟩
  --   (fib (ℕsuc n) + (fib (ℕsuc n) + fib (ℕsuc n))) + (fib n + (fib n + fib n))
  -- ≡⟨ +-assoc ⟩
  --   fib (ℕsuc n) + ((fib (ℕsuc n) + fib (ℕsuc n)) + (fib n + (fib n + fib n)))
  -- ≡⟨ +-cong refl (+-assoc) ⟩
  --   fib (ℕsuc n) + (fib (ℕsuc n) + (fib (ℕsuc n) + (fib n + (fib n + fib n))))
  -- ≡⟨ +-cong refl (+-cong refl (sym +-assoc)) ⟩
  --   fib (ℕsuc n) + (fib (ℕsuc n) + ((fib (ℕsuc n) + fib n) + (fib n + fib n)))
  -- ≡⟨ +-cong refl (+-cong refl (sym +-assoc)) ⟩
  --   fib (ℕsuc n) + (fib (ℕsuc n) + (((fib (ℕsuc n) + fib n) + fib n) + fib n))
  -- ≡⟨ +-cong refl (sym +-assoc) ⟩
  --   fib (ℕsuc n) + ((fib (ℕsuc n) + ((fib (ℕsuc n) + fib n) + fib n)) + fib n)
  -- ≡⟨ sym +-assoc ⟩
  --   (fib (ℕsuc n) + (fib (ℕsuc n) + ((fib (ℕsuc n) + fib n) + fib n))) + fib n
  -- ≡⟨ +-comm ⟩
  --   fib n + (fib (ℕsuc n) + (fib (ℕsuc n) + ((fib (ℕsuc n) + fib n) + fib n)))
  -- ≡⟨ sym +-assoc ⟩
  --   (fib n + fib (ℕsuc n)) + (fib (ℕsuc n) + ((fib (ℕsuc n) + fib n) + fib n))
  -- ≡⟨ +-cong +-comm refl ⟩
  --   (fib (ℕsuc n) + fib n) + (fib (ℕsuc n) + ((fib (ℕsuc n) + fib n) + fib n))
  -- ≡⟨ sym +-assoc ⟩
  --   ((fib (ℕsuc n) + fib n) + fib (ℕsuc n)) + ((fib (ℕsuc n) + fib n) + fib n)
  -- ≡⟨ sym +-assoc ⟩
  ≡⟨ lemma ⟩
    (((fib (ℕsuc n) + fib n) + fib (ℕsuc n)) + (fib (ℕsuc n) + fib n)) + fib n
  ≡⟨ +-cong (+-cong (+-cong (sym fib-def) refl) refl) refl ⟩
    ((fib (ℕsuc (ℕsuc n)) + fib (ℕsuc n)) + (fib (ℕsuc n) + fib n)) + fib n
  ≡⟨ +-cong (+-cong (sym fib-def) (sym fib-def)) refl ⟩
    (fib (ℕsuc (ℕsuc (ℕsuc n))) + fib (ℕsuc (ℕsuc n))) + fib n
  ≡⟨ +-cong (sym fib-def) refl ⟩
    fib (ℕsuc (ℕsuc (ℕsuc (ℕsuc n)))) + fib n
  ∎

∑ : (n : ℕ) → (Fin n → Expr) → Expr
∑ ℕzero f = zero
∑ (ℕsuc n) f = f Fzero + ∑ n (λ i → f (Fsuc i))

-- ∑-pop : ∀ {n f} → ∑ (ℕsuc n) f ≡ ∑ n (λ i → f (F.inject₁ i)) + f (F.fromℕ n)
-- ∑-pop {ℕzero} {f} = +-comm
-- ∑-pop {ℕsuc n} {f} =
--   begin
--     f Fzero + (f (Fsuc Fzero) + ∑ n (λ i → f (Fsuc (Fsuc i))))
--   ≈⟨ {!!} ⟩
--     f Fzero + (∑ n (λ i → f (Fsuc (F.inject₁ i))) + f (Fsuc (F.fromℕ n)))
--   ≈⟨ sym +-assoc ⟩
--     (f Fzero + ∑ n (λ i → f (Fsuc (F.inject₁ i)))) + f (Fsuc (F.fromℕ n))
--   ∎

-- ∏ : (n : ℕ) → (Fin n → Expr) → Expr
-- ∏ ℕzero f = one
-- ∏ (ℕsuc n) f = f Fzero * ∏ n (λ i → f (Fsuc i))

-- The more general "thrice"
nce : ∀ {n} → fib (4 ℕ+ n) + ∑ n (λ fi → let i = 1 ℕ+ ℕsuc (F.toℕ fi) in nat i * fib i) ≡ nat (1 ℕ+ n) * fib (2 ℕ+ n) + nat 3
nce {n} =
  begin
    fib (4 ℕ+ n) + ∑ n (λ fi → let i = 1 ℕ+ ℕsuc (F.toℕ fi) in nat i * fib i)
  ≈⟨ {!!} ⟩
    fib (4 ℕ+ n) + ∑ n (λ fi → let i = 1 ℕ+ ℕsuc (F.toℕ fi) in nat i * fib i)
  ≈⟨ {!!} ⟩
    nat (1 ℕ+ n) * fib (2 ℕ+ n) + nat 3
  ∎


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
  main = run $ mapM′ (λ n → putStrLn (ℕshow n) >>'
                            show≡ (thrice {n}) >>'
                            -- show≡ (thrice' {n}) >>'
                            putStrLn "")
                     (count ℕzero) >>'
         return tt

open Runner using (main)
