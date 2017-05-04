module SetPartitions where

open import Function
open import Translate
open import Translate.Common
open import Translate.EqReasoning
open import Translate.Combinatorics
open import Translate.Arithmetic
open import Translate.Tools
import Data.List as L
import Data.Nat.Properties.Simple as NPS

part : ∀ {n k} → S' (ℕsuc n) (ℕsuc k) ≡ S n k

part {ℕzero} {ℕzero} = proof Prefl (mkBij to from to-from from-to)
  where
    to : lift (S' (ℕsuc ℕzero) (ℕsuc ℕzero)) → lift (S ℕzero ℕzero)
    to (add empty) = empty
    to (insert () _)

    from : lift (S ℕzero ℕzero) → lift (S' (ℕsuc ℕzero) (ℕsuc ℕzero))
    from empty = add empty

    to-from : ∀ x → to (from x) P≡ x
    to-from empty = Prefl

    from-to : ∀ y → from (to y) P≡ y
    from-to (add empty) = Prefl
    from-to (insert () _)

part {ℕzero} {ℕsuc k} = proof (Ptrans (NPS.+-right-identity (k ℕ* 0))
                                       (NPS.*-right-zero k))
                                (mkBij to from to-from from-to)
  where
    to : lift (S' (ℕsuc ℕzero) (ℕsuc (ℕsuc k))) → lift (S ℕzero (ℕsuc k))
    to (add ())
    to (insert _ ())

    from : lift (S ℕzero (ℕsuc k)) → lift (S' (ℕsuc ℕzero) (ℕsuc (ℕsuc k)))
    from ()

    to-from : ∀ x → to (from x) P≡ x
    to-from ()

    from-to : ∀ y → from (to y) P≡ y
    from-to (add ())
    from-to (insert _ ())

part {ℕsuc n} {ℕzero} =
  begin
    S' (ℕsuc (ℕsuc n)) (ℕsuc ℕzero)
  ≡⟨ S'-def₂ ⟩
    zero
  ≡⟨ sym S-def₂ ⟩
    S (ℕsuc n) ℕzero
  ∎

part {ℕsuc n} {ℕsuc k} =
  begin
    S' (ℕsuc (ℕsuc n)) (ℕsuc (ℕsuc k))
  ≡⟨ S'-def₁ ⟩
    (nat (ℕsuc k)) * S' (ℕsuc n) (ℕsuc (ℕsuc k)) + S' (ℕsuc n) (ℕsuc k)
  ≡⟨ +-cong (*-cong refl part) part ⟩
    (nat (ℕsuc k)) * S n (ℕsuc k) + S n k
  ≡⟨ sym S-def₁ ⟩
    S (ℕsuc n) (ℕsuc k)
  ∎

-- party : ∀ {l r} → S l r ≡ S' (ℕsuc l) r
-- party {ℕzero} {ℕzero} = proof Prefl (mkBij to from to-from from-to)
--   where
--     to : SetPartitionK ℕzero ℕzero → SetPartitionK' (ℕsuc ℕzero) ℕzero
--     to empty = add empty

--     from : SetPartitionK' (ℕsuc ℕzero) ℕzero → SetPartitionK ℕzero ℕzero
--     from (add empty) = empty

--     to-from : ∀ y → to (from y) P≡ y
--     to-from (add empty) = Prefl

--     from-to : ∀ x → from (to x) P≡ x
--     from-to empty = Prefl

-- party {ℕzero} {ℕsuc r} = proof Prefl (mkBij to from to-from from-to)
--   where
--     to : SetPartitionK ℕzero (ℕsuc r) → SetPartitionK' (ℕsuc ℕzero) (ℕsuc r)
--     to (insert () x₁)

--     from : SetPartitionK' (ℕsuc ℕzero) (ℕsuc r) → SetPartitionK ℕzero (ℕsuc r)
--     from (add ())
--     from (insert () x₁)

--     to-from : ∀ y → to (from y) P≡ y
--     to-from (add ())
--     to-from (insert () y)

--     from-to : ∀ x → from (to x) P≡ x
--     from-to (insert () x₁)

-- party {ℕsuc l} {ℕzero} =
--   begin
--     S (ℕsuc l) ℕzero
--   ≡⟨ S-def₂ ⟩
--     S l ℕzero
--   ≡⟨ party ⟩
--     S' (ℕsuc l) ℕzero
--   ≡⟨ sym S'-def₂ ⟩
--     S' (ℕsuc (ℕsuc l)) ℕzero
--   ∎
-- party {ℕsuc l} {ℕsuc r} =
--   begin
--     S (ℕsuc l) (ℕsuc r)
--   ≡⟨ S-def₁ ⟩
--     (nat (ℕsuc l)) * S (ℕsuc l) r + S l (ℕsuc r)
--   ≡⟨ +-cong (*-cong refl party) party ⟩
--     (nat (ℕsuc l)) * S' (ℕsuc (ℕsuc l)) r + S' (ℕsuc l) (ℕsuc r)
--   ≡⟨ sym S'-def₁ ⟩
--     S' (ℕsuc (ℕsuc l)) (ℕsuc r)
--   ∎

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
                                              >>' show≡ (part {l} {r})
                                              >>' putStrLn ""
                                     })
                                  (CL.fromList $ splits x)) (count 0) >>'
         return tt

open Runner using (main)

