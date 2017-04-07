module BinStr where

open import Function
open import Translate
open import Translate.Common
open import Translate.Arithmetic
open import Translate.Combinatorics
open import Translate.EqReasoning
open import Translate.Tools
open import Data.Maybe

ex : ∀ {a b c} → a * (b + c) ≡ c * a + a * b
ex {a} {b} {c} = trans distribˡ-*-+ (trans +-comm (+-cong *-comm refl))

ex2 : ∀ {a b c} → a * (b + c) ≡ c * a + a * b
ex2 {a} {b} {c} =
  begin
    a * (b + c)
  ≡⟨ distribˡ-*-+ ⟩
    a * b + a * c
  ≡⟨ +-comm ⟩
    a * c + a * b
  ≡⟨ +-cong *-comm refl ⟩
    c * a + a * b
  ∎

two-four : nat 2 * nat 2 ≡ nat 4
two-four = proof Prefl (from-just (toBij {nat 2 * nat 2} {nat 4} (
         ((nothing , nothing) , nothing) L∷
         ((nothing , just nothing) , just nothing) L∷
         ((just nothing , nothing) , just (just nothing)) L∷
         ((just nothing , just nothing) , just (just (just nothing))) L∷ L[]
  )))

phi : ∀ {n} → 2^ n * 2^ n ≡ 4^ n
phi {ℕzero} = proof Prefl (from-just (toBij {2^ 0 * 2^ 0} {4^ 0} (
    (([] , []) , []) L∷ L[]
  )))
-- phi {ℕzero} = proof Prefl (mkBij to from to-from from-to)
--   where
--     to : lift (2^ ℕzero * 2^ ℕzero) → lift (4^ ℕzero)
--     to ([] , []) = []

--     from : lift (4^ ℕzero) → lift (2^ ℕzero * 2^ ℕzero)
--     from [] = [] , []

--     to-from : ∀ y → to (from y) P≡ y
--     to-from [] = Prefl

--     from-to : ∀ x → from (to x) P≡ x
--     from-to ([] , []) = Prefl

phi {ℕsuc n} = begin
    2^ (ℕsuc n) * 2^ (ℕsuc n)       ≡⟨ *-cong 2^-def 2^-def ⟩
    (nat 2 * 2^ n) * (nat 2 * 2^ n) ≡⟨ sym *-assoc ⟩
    ((nat 2 * 2^ n) * nat 2) * 2^ n ≡⟨ *-cong *-comm refl ⟩
    (nat 2 * (nat 2 * 2^ n)) * 2^ n ≡⟨ *-cong (sym *-assoc) refl ⟩
    ((nat 2 * nat 2) * 2^ n) * 2^ n ≡⟨ *-assoc ⟩
    (nat 2 * nat 2) * (2^ n * 2^ n) ≡⟨ *-cong two-four refl ⟩
    (nat 4) * (2^ n * 2^ n)         ≡⟨ *-cong refl (phi {n}) ⟩
    (nat 4) * (4^ n)                ≡⟨ sym 4^-def ⟩
    4^ (ℕsuc n)                     ∎


module Runner where
  open import IO
  open import Data.List hiding (_++_)
  open import Data.String as S
  open import Data.Unit
  import Agda.Builtin.IO as BIO
  import Data.Colist as CL
  open import Data.Nat.Show using () renaming (show to ℕshow)
  open import Coinduction

  infixl 1 _>>'_
  _>>'_ : ∀ {a} → {A : Set a} → {B : Set a} (m₁ : (IO B)) (m₂ : (IO A)) → IO A
  m₁ >>' m₂ = (♯ m₁) >> (♯ m₂)

  count : (start : ℕ) → CL.Colist ℕ
  count x = x CL.∷ ♯ count (ℕsuc x)

  main : BIO.IO ⊤
  main = run $ mapM′ (λ n → putStrLn (ℕshow n) >>' show≡ (phi {n})
                                               >>' putStrLn ""
                      ) (count 10) >>'
         return tt

open Runner using (main)

