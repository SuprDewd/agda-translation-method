module SetPartitions where

open import Function
open import Translate
open import Translate.Support
open import Translate.EqReasoning
open import Translate.Combinatorics
open import Translate.Axioms
open import Translate.Tools
import Data.List as L

party : ∀ {l r} → S₂ l r ≡ CS₂ (ℕsuc l) r
party {ℕzero} {ℕzero} = axiom Prefl (mkBij to from)
  where
    to : SetPartitionK ℕzero ℕzero → CSetPartitionK (ℕsuc ℕzero) ℕzero
    to empty = add empty
    from : CSetPartitionK (ℕsuc ℕzero) ℕzero → SetPartitionK ℕzero ℕzero
    from (add empty) = empty
party {ℕzero} {ℕsuc r} = axiom Prefl (mkBij to from)
  where
    to : SetPartitionK ℕzero (ℕsuc r) → CSetPartitionK (ℕsuc ℕzero) (ℕsuc r)
    to (insert () x₁)
    from : CSetPartitionK (ℕsuc ℕzero) (ℕsuc r) → SetPartitionK ℕzero (ℕsuc r)
    from (add ())
    from (insert () x₁)
party {ℕsuc l} {ℕzero} =
  begin
    S₂ (ℕsuc l) ℕzero
  ≈⟨ S₂-def₂ ⟩
    S₂ l ℕzero
  ≈⟨ party ⟩
    CS₂ (ℕsuc l) ℕzero
  ≈⟨ sym CS₂-def₂ ⟩
    CS₂ (ℕsuc (ℕsuc l)) ℕzero
  ∎
party {ℕsuc l} {ℕsuc r} =
  begin
    S₂ (ℕsuc l) (ℕsuc r)
  ≈⟨ S₂-def₁ ⟩
    (nat (ℕsuc l)) * S₂ (ℕsuc l) r + S₂ l (ℕsuc r)
  ≈⟨ +-cong (*-cong refl party) party ⟩
    (nat (ℕsuc l)) * CS₂ (ℕsuc (ℕsuc l)) r + CS₂ (ℕsuc l) (ℕsuc r)
  ≈⟨ sym CS₂-def₁ ⟩
    CS₂ (ℕsuc (ℕsuc l)) (ℕsuc r)
  ∎

  -- begin
  --   S₂ (ℕsuc l) (ℕsuc r)
  -- ≈⟨ S₂-def₁ ⟩
  --   (nat (ℕsuc l)) * S₂ (ℕsuc l) r + S₂ l (ℕsuc r)
  -- ≈⟨ {!!} ⟩
  --   (nat (ℕsuc l)) * S₂ (ℕsuc l) r + S₂ l (ℕsuc r)
  -- ≈⟨ {!!} ⟩
  --   CS₂ (ℕsuc (ℕsuc l)) (ℕsuc r)
  -- ≈⟨ {!!} ⟩
  --   CS₂ (ℕsuc (ℕsuc l)) (ℕsuc r)
  -- ∎

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

  splits : ℕ → List (ℕ × ℕ)
  splits ℕzero = (0 , 0) L∷ L[]
  splits (ℕsuc n) = (0 , ℕsuc n) L∷ L.map (λ { (a , b) → ℕsuc a , b}) (splits n)

  main : BIO.IO ⊤
  main = run $ mapM′ (λ x → mapM′ (λ { (l , r) → putStrLn (ℕshow l ++ " " ++ ℕshow r)
                                              >>' show≡ (party {l} {r})
                                              >>' putStrLn ""
                                     })
                                  (CL.fromList $ splits x)) (count 0) >>'
         return tt

open Runner using (main)

