------------------------------------------------------------------------
-- The Translate library
--
-- Expressions for various combinatorial structures
------------------------------------------------------------------------

module Translate.Combinatorics where

open import Translate.Base
open import Translate.Support
open import Translate.Types
open import Function
import Data.Fin as F
open import Translate.Bijection using (getTo; getFrom; getToFrom; getFromTo)

-- infixr 7 _^_
-- TODO: infix? ? ∷


------------------------------------------------------------------------
-- Fibonacci strings

fib-def : ∀ {n} → fib (ℕsuc (ℕsuc n)) ≡ fib (ℕsuc n) + fib n
fib-def {n} = axiom Prefl (mkBij to from toFrom fromTo)
  where
    to : lift (fib (ℕsuc (ℕsuc n))) → lift (fib (ℕsuc n) + fib n)
    to (xs ∷1) = inj₁ xs
    to (xs ∷2) = inj₂ xs

    from : lift (fib (ℕsuc n) + fib n) → lift (fib (ℕsuc (ℕsuc n)))
    from (inj₁ xs) = xs ∷1
    from (inj₂ xs) = xs ∷2

    toFrom : ∀ y → to (from y) P≡ y
    toFrom (inj₁ x) = Prefl
    toFrom (inj₂ y) = Prefl

    fromTo : ∀ x → from (to x) P≡ x
    fromTo (x ∷1) = Prefl
    fromTo (x ∷2) = Prefl

fib-cong : ∀ {a b} → a P≡ b → (fib a) ≡ (fib b)
fib-cong Prefl = refl

------------------------------------------------------------------------
-- Binary strings

-- Enumeration

-- ℕ2^ : ℕ → ℕ
-- ℕ2^ 0 = 1
-- ℕ2^ (ℕsuc n) = ℕ2^ n ℕ+ ℕ2^ n

-- -- Combinatorial interpretation

-- data BinStr : ℕ → Set where
--   [] : BinStr ℕzero
--   _∷_ : ∀ {n} → Fin 2 → BinStr n → BinStr (ℕsuc n)

-- -- Expressions

-- 2^ : ℕ → Expr
-- 2^ n = record
--   { value = ♯ ℕ2^ n
--   ; lift = BinStr n
--   }

-- Axioms

-- 2^-def : ∀ {n} → 2^ (ℕsuc n) ≡ 2^ n + 2^ n
-- 2^-def {n} = axiom Prefl $ mkBij
--   (λ { (Fzero ∷ xs) → inj₁ xs
--      ; (Fsuc Fzero ∷ xs) → inj₂ xs
--      ; (Fsuc (Fsuc ()) ∷ _)
--      })
--   (λ { (inj₁ xs) → Fzero ∷ xs
--      ; (inj₂ xs) → Fsuc Fzero ∷ xs
--      })

------------------------------------------------------------------------
-- Set partitions

S₂-def₁ : ∀ {l r} → S₂ (ℕsuc l) (ℕsuc r) ≡ (nat (ℕsuc l)) * S₂ (ℕsuc l) r + S₂ l (ℕsuc r)
S₂-def₁ {l} {r} = axiom (Pcong (λ x → ℕS₂ (ℕsuc l) r ℕ+ x ℕ* ℕS₂ (ℕsuc l) r ℕ+ ℕS₂ l (ℕsuc r)) (Psym (nat-value l))) (mkBij to from toFrom fromTo)
  where
    to : lift (S₂ (ℕsuc l) (ℕsuc r)) → lift ((nat (ℕsuc l)) * S₂ (ℕsuc l) r + S₂ l (ℕsuc r))
    to (add x) = inj₂ x
    to (insert Fzero x₁) = inj₁ (nothing , x₁)
    to (insert (Fsuc x) x₁) = inj₁ (just (getFrom (nat-lift l) x) , x₁)

    from : lift ((nat (ℕsuc l)) * S₂ (ℕsuc l) r + S₂ l (ℕsuc r)) → lift (S₂ (ℕsuc l) (ℕsuc r))
    from (inj₁ (just x , b)) = insert (Fsuc (getTo (nat-lift l) x)) b
    from (inj₁ (nothing , b)) = insert Fzero b
    from (inj₂ y) = add y

    toFrom : ∀ y → to (from y) P≡ y
    toFrom (inj₁ (just x , b)) = Pcong (λ t → inj₁ (just t , b)) (getFromTo (nat-lift l) x)
    toFrom (inj₁ (nothing , b)) = Prefl
    toFrom (inj₂ y) = Prefl

    fromTo : ∀ x → from (to x) P≡ x
    fromTo (add x) = Prefl
    fromTo (insert Fzero x₁) = Prefl
    fromTo (insert (Fsuc x) x₁) = Pcong (λ t → insert (Fsuc t) x₁) (getToFrom (nat-lift l) x)

S₂-def₂ : ∀ {l} → S₂ (ℕsuc l) ℕzero ≡ S₂ l ℕzero
S₂-def₂ {l} = axiom Prefl (mkBij to from toFrom fromTo)
  where
    to : SetPartitionK (ℕsuc l) ℕzero → SetPartitionK l ℕzero
    to (add x) = x

    from : SetPartitionK l ℕzero → SetPartitionK (ℕsuc l) ℕzero
    from x = add x

    toFrom : ∀ y → to (from y) P≡ y
    toFrom y = Prefl

    fromTo : ∀ x → from (to x) P≡ x
    fromTo (add x) = Prefl

------------------------------------------------------------------------
-- Set partitions with no consecutive numbers in a part

CS₂-def₁ : ∀ {l r} → CS₂ (ℕsuc l) (ℕsuc r) ≡ (nat l) * CS₂ (ℕsuc l) r + CS₂ l (ℕsuc r)
CS₂-def₁ {l} {r} = axiom (Pcong (λ x → x ℕ* ℕCS₂ (ℕsuc l) r ℕ+ ℕCS₂ l (ℕsuc r)) (Psym (nat-value l))) (mkBij to from toFrom fromTo)
  where
    to : lift (CS₂ (ℕsuc l) (ℕsuc r)) → lift ((nat l) * CS₂ (ℕsuc l) r + CS₂ l (ℕsuc r))
    to (add x) = inj₂ x
    to (insert x x₁) = inj₁ ((getFrom (nat-lift l) x) , x₁)

    from : lift ((nat l) * CS₂ (ℕsuc l) r + CS₂ l (ℕsuc r)) → lift (CS₂ (ℕsuc l) (ℕsuc r))
    from (inj₁ (a , b)) = insert (getTo (nat-lift l) a) b
    from (inj₂ y) = add y

    toFrom : ∀ y → to (from y) P≡ y
    toFrom (inj₁ (x₁ , x₂)) = Pcong (λ t → inj₁ (t , x₂)) (getFromTo (nat-lift l) x₁)
    toFrom (inj₂ y) = Prefl

    fromTo : ∀ x → from (to x) P≡ x
    fromTo (add x) = Prefl
    fromTo (insert x x₁) = Pcong (λ t → insert t x₁) (getToFrom (nat-lift l) x)

CS₂-def₂ : ∀ {l} → CS₂ (ℕsuc l) ℕzero ≡ CS₂ l ℕzero
CS₂-def₂ {l} = axiom Prefl (mkBij to from toFrom fromTo)
  where
    to : CSetPartitionK (ℕsuc l) ℕzero → CSetPartitionK l ℕzero
    to (add x) = x

    from : CSetPartitionK l ℕzero → CSetPartitionK (ℕsuc l) ℕzero
    from x = add x

    toFrom : ∀ y → to (from y) P≡ y
    toFrom y = Prefl

    fromTo : ∀ x → from (to x) P≡ x
    fromTo (add x) = Prefl

------------------------------------------------------------------------
-- K-ary strings

-- Enumeration

-- _ℕ^_ : ℕ → ℕ → ℕ
-- k ℕ^ ℕzero = 1
-- k ℕ^ ℕsuc n = k ℕ* (k ℕ^ n)

-- -- Combinatorial interpretation

-- data K-aryStr (k : ℕ) : ℕ → Set where
--   [] : K-aryStr k ℕzero
--   _∷_ : ∀ {n} → Fin k → K-aryStr k n → K-aryStr k (ℕsuc n)

-- -- Expressions

-- _^_ : ℕ → ℕ → Expr
-- k ^ n = record
--   { value = ♯ (k ℕ^ n)
--   ; lift = K-aryStr k n
--   }

-- Axioms

-- ^-def : ∀ {n} k → k ^ (ℕsuc n) ≡ (fin k) * (k ^ n)
-- ^-def {n} k = axiom Prefl $ mkBij
--   (λ { (x ∷ xs) → x , xs })
--   (λ { (x , xs) → x ∷ xs })

------------------------------------------------------------------------
-- Binary strings with a given number of ones

-- Enumeration

-- TODO: Make a decidable version of this?
-- try-lower : ∀ {n} → Fin (ℕsuc n) → Maybe (Fin n)
-- try-lower {ℕzero} Fzero = nothing -- There is nothing in Fin 0
-- try-lower {ℕzero} (Fsuc ())
-- try-lower {ℕsuc n} Fzero = just Fzero
-- try-lower {ℕsuc n} (Fsuc k) with try-lower {n} k
-- try-lower {ℕsuc n} (Fsuc k) | just x = just (Fsuc x)
-- try-lower {ℕsuc n} (Fsuc k) | nothing = nothing

-- ℕbin : (n : ℕ) → (k : Fin (ℕsuc n)) → ℕ
-- ℕbin _ Fzero = 1
-- ℕbin ℕzero (Fsuc ())
-- ℕbin (ℕsuc n) (Fsuc k) with try-lower (Fsuc k)
-- ℕbin (ℕsuc n) (Fsuc k) | just x = ℕbin n k ℕ+ ℕbin n x
-- ℕbin (ℕsuc n) (Fsuc k) | nothing = ℕbin n k

-- -- Combinatorial interpretation

-- data Binomial : (n : ℕ) → (k : Fin (ℕsuc n)) → Set where
--   [] : Binomial ℕzero Fzero
--   0∷_ : ∀ {n k} → Binomial n k → Binomial (ℕsuc n) (F.inject₁ k)
--   1∷_ : ∀ {n k} → Binomial n k → Binomial (ℕsuc n) (F.raise 1 k)

-- -- Expressions

-- bin : (n : ℕ) → (k : Fin (ℕsuc n)) → Expr
-- bin n k = record
--   { value = ♯ ℕbin n k
--   ; lift = Binomial n k
--   }

-- Axioms

-- TODO: How should we implement this?
-- bin-def : ∀ n k → ?
-- bin-def n k = ?

------------------------------------------------------------------------
-- Dyck paths

-- Enumeration

-- TODO: How should we implement this?
-- ℕcat : ℕ → ℕ
-- ℕcat n = {!!}

-- Combinatorial interpretation

-- data DyckPath : ℕ → Set where
--   empty : DyckPath ℕzero
--   right : ∀ {n} → DyckPath n → DyckPath (ℕsuc n)
--   up : ∀ {n k} → DyckPath n → DyckPath k → DyckPath (2 ℕ+ n ℕ+ k)

-- Expressions

-- cat : ℕ → Expr
-- cat n = record
--   { value = ♯ ℕcat n
--   ; lift = DyckPath n
--   }

-- Axioms

-- TODO: How should we implement this?
-- cat : ∀ n k → ?
-- cat n k = ?

