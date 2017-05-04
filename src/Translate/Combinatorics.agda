------------------------------------------------------------------------
-- The Translate library
--
-- Expressions for various combinatorial structures
------------------------------------------------------------------------

module Translate.Combinatorics where

open import Translate.Base
open import Translate.Common
open import Translate.Types
open import Function
import Data.Fin as F
open import Translate.Bijection using (getTo; getFrom; getToFrom; getFromTo)

-- infixr 7 _^_
-- TODO: infix? ? ∷


------------------------------------------------------------------------
-- Fibonacci strings

fib-def : ∀ {n} → fib (ℕsuc (ℕsuc n)) ≡ fib (ℕsuc n) + fib n
fib-def {n} = proof Prefl (mkBij to from to-from from-to)
  where
    to : lift (fib (ℕsuc (ℕsuc n))) → lift (fib (ℕsuc n) + fib n)
    to (xs ∷1) = inj₁ xs
    to (xs ∷2) = inj₂ xs

    from : lift (fib (ℕsuc n) + fib n) → lift (fib (ℕsuc (ℕsuc n)))
    from (inj₁ xs) = xs ∷1
    from (inj₂ xs) = xs ∷2

    to-from : ∀ y → to (from y) P≡ y
    to-from (inj₁ x) = Prefl
    to-from (inj₂ y) = Prefl

    from-to : ∀ x → from (to x) P≡ x
    from-to (x ∷1) = Prefl
    from-to (x ∷2) = Prefl

fib-cong : ∀ {a b} → a P≡ b → (fib a) ≡ (fib b)
fib-cong Prefl = refl

------------------------------------------------------------------------
-- Binary strings

2^-def : ∀ {n} → 2^ (ℕsuc n) ≡ nat 2 * 2^ n
2^-def {n} = proof Prefl (mkBij to from to-from from-to)
  where
    to : lift (2^ (ℕsuc n)) → lift (nat 2 * 2^ n)
    to (Fzero ∷ xs) = nothing , xs
    to (Fsuc Fzero ∷ xs) = just nothing , xs
    to (Fsuc (Fsuc ()) ∷ xs)

    from : lift (nat 2 * 2^ n) → lift (2^ (ℕsuc n))
    from (nothing , xs) = Fzero ∷ xs
    from (just nothing , xs) = Fsuc Fzero ∷ xs
    from (just (just ()) , xs)

    to-from : ∀ y → to (from y) P≡ y
    to-from (just (just ()) , xs)
    to-from (just nothing , xs) = Prefl
    to-from (nothing , xs) = Prefl

    from-to : ∀ x → from (to x) P≡ x
    from-to (Fzero ∷ xs) = Prefl
    from-to (Fsuc Fzero ∷ xs) = Prefl
    from-to (Fsuc (Fsuc ()) ∷ xs)

2^-cong : ∀ {a b} → a P≡ b → (2^ a) ≡ (2^ b)
2^-cong Prefl = refl

------------------------------------------------------------------------
-- Quaternary strings

4^-def : ∀ {n} → 4^ (ℕsuc n) ≡ nat 4 * 4^ n
4^-def {n} = proof Prefl (mkBij to from to-from from-to)
  where
    to : lift (4^ (ℕsuc n)) → lift (nat 4 * 4^ n)
    to (Fzero ∷ xs) = nothing , xs
    to (Fsuc Fzero ∷ xs) = just nothing , xs
    to (Fsuc (Fsuc Fzero) ∷ xs) = just (just nothing) , xs
    to (Fsuc (Fsuc (Fsuc Fzero)) ∷ xs) = just (just (just nothing)) , xs
    to (Fsuc (Fsuc (Fsuc (Fsuc ()))) ∷ xs)

    from : lift (nat 4 * 4^ n) → lift (4^ (ℕsuc n))
    from (just (just (just (just ()))) , xs)
    from (just (just (just nothing)) , xs) = Fsuc (Fsuc (Fsuc Fzero)) ∷ xs
    from (just (just nothing) , xs) = Fsuc (Fsuc Fzero) ∷ xs
    from (just nothing , xs) = Fsuc Fzero ∷ xs
    from (nothing , xs) = Fzero ∷ xs

    to-from : ∀ y → to (from y) P≡ y
    to-from (just (just (just (just ()))) , xs)
    to-from (just (just (just nothing)) , xs) = Prefl
    to-from (just (just nothing) , xs) = Prefl
    to-from (just nothing , xs) = Prefl
    to-from (nothing , xs) = Prefl

    from-to : ∀ x → from (to x) P≡ x
    from-to (Fzero ∷ xs) = Prefl
    from-to (Fsuc Fzero ∷ xs) = Prefl
    from-to (Fsuc (Fsuc Fzero) ∷ xs) = Prefl
    from-to (Fsuc (Fsuc (Fsuc Fzero)) ∷ xs) = Prefl
    from-to (Fsuc (Fsuc (Fsuc (Fsuc ()))) ∷ xs)

------------------------------------------------------------------------
-- Set partitions

S-def₁ : ∀ {n k} → S (ℕsuc n) (ℕsuc k) ≡ (nat (ℕsuc k)) * S n (ℕsuc k) + S n k
S-def₁ {n} {k} = proof (Pcong (λ x → ℕS n (ℕsuc k) ℕ+ x ℕ* ℕS n (ℕsuc k) ℕ+ ℕS n k) (Psym (nat-value k)))
                       (mkBij to from to-from from-to)
  where
    to : lift (S (ℕsuc n) (ℕsuc k)) → lift ((nat (ℕsuc k)) * S n (ℕsuc k) + S n k)
    to (add x) = inj₂ x
    to (insert Fzero x₁) = inj₁ (nothing , x₁)
    to (insert (Fsuc x) x₁) = inj₁ (just (getFrom (nat-lift _) x) , x₁)

    from : lift ((nat (ℕsuc k)) * S n (ℕsuc k) + S n k) → lift (S (ℕsuc n) (ℕsuc k))
    from (inj₁ (just x , y)) = insert (Fsuc (getTo (nat-lift k) x)) y
    from (inj₁ (nothing , y)) = insert Fzero y
    from (inj₂ y) = add y

    to-from : ∀ y → to (from y) P≡ y
    to-from (inj₁ (just x , y)) rewrite getFromTo (nat-lift k) x = Prefl
    to-from (inj₁ (nothing , y)) = Prefl
    to-from (inj₂ y) = Prefl

    from-to : ∀ x → from (to x) P≡ x
    from-to (add x) = Prefl
    from-to (insert Fzero x₁) = Prefl
    from-to (insert (Fsuc x) x₁) rewrite getToFrom (nat-lift k) x = Prefl

S-def₂ : ∀ {n} → S (ℕsuc n) ℕzero ≡ zero
S-def₂ {n} = proof Prefl (mkBij to from to-from from-to)
  where
    to : lift (S (ℕsuc n) ℕzero) → lift zero
    to (insert () x₁)

    from : lift zero → lift (S (ℕsuc n) ℕzero)
    from ()

    to-from : ∀ y → to (from y) P≡ y
    to-from ()

    from-to : ∀ x → from (to x) P≡ x
    from-to (insert () x₁)

-- S-def₁ {ℕzero} {ℕzero} = proof Prefl (mkBij {!!} {!!} {!!} {!!})
--   where
--     to : lift (S (ℕsuc ℕzero) (ℕsuc ℕzero)) → lift ((nat (ℕsuc ℕzero)) * S ℕzero (ℕsuc ℕzero) + S ℕzero ℕzero)
--     to (add empty) = inj₂ empty
--     to (insert x ())

--     from : lift ((nat (ℕsuc ℕzero)) * S ℕzero (ℕsuc ℕzero) + S ℕzero ℕzero) → lift (S (ℕsuc ℕzero) (ℕsuc ℕzero))
--     from (inj₁ (x , ()))
--     from (inj₂ empty) = add empty

--     to-from : ∀ y → to (from y) P≡ y
--     to-from (inj₁ (x , ()))
--     to-from (inj₂ empty) = Prefl

--     from-to : ∀ x → from (to x) P≡ x
--     from-to (add empty) = Prefl
--     from-to (insert x ())

-- S-def₁ {ℕzero} {ℕsuc k} = proof {!!} {!!}

-- S-def₁ {ℕsuc n} {ℕzero} = {!!}
-- S-def₁ {ℕsuc n} {ℕsuc k} = {!!}

-- S₂-def₁ : ∀ {l r} → S₂ (ℕsuc l) (ℕsuc r) ≡ (nat (ℕsuc l)) * S₂ (ℕsuc l) r + S₂ l (ℕsuc r)
-- S₂-def₁ {l} {r} = proof (Pcong (λ x → ℕS₂ (ℕsuc l) r ℕ+ x ℕ* ℕS₂ (ℕsuc l) r ℕ+ ℕS₂ l (ℕsuc r)) (Psym (nat-value l))) (mkBij to from to-from from-to)
--   where
--     to : lift (S₂ (ℕsuc l) (ℕsuc r)) → lift ((nat (ℕsuc l)) * S₂ (ℕsuc l) r + S₂ l (ℕsuc r))
--     to (add x) = inj₂ x
--     to (insert Fzero x₁) = inj₁ (nothing , x₁)
--     to (insert (Fsuc x) x₁) = inj₁ (just (getFrom (nat-lift l) x) , x₁)

--     from : lift ((nat (ℕsuc l)) * S₂ (ℕsuc l) r + S₂ l (ℕsuc r)) → lift (S₂ (ℕsuc l) (ℕsuc r))
--     from (inj₁ (just x , b)) = insert (Fsuc (getTo (nat-lift l) x)) b
--     from (inj₁ (nothing , b)) = insert Fzero b
--     from (inj₂ y) = add y

--     to-from : ∀ y → to (from y) P≡ y
--     to-from (inj₁ (just x , b)) = Pcong (λ t → inj₁ (just t , b)) (getFromTo (nat-lift l) x)
--     to-from (inj₁ (nothing , b)) = Prefl
--     to-from (inj₂ y) = Prefl

--     from-to : ∀ x → from (to x) P≡ x
--     from-to (add x) = Prefl
--     from-to (insert Fzero x₁) = Prefl
--     from-to (insert (Fsuc x) x₁) = Pcong (λ t → insert (Fsuc t) x₁) (getToFrom (nat-lift l) x)

-- S₂-def₂ : ∀ {l} → S₂ (ℕsuc l) ℕzero ≡ S₂ l ℕzero
-- S₂-def₂ {l} = proof Prefl (mkBij to from to-from from-to)
--   where
--     to : SetPartitionK (ℕsuc l) ℕzero → SetPartitionK l ℕzero
--     to (add x) = x

--     from : SetPartitionK l ℕzero → SetPartitionK (ℕsuc l) ℕzero
--     from x = add x

--     to-from : ∀ y → to (from y) P≡ y
--     to-from y = Prefl

--     from-to : ∀ x → from (to x) P≡ x
--     from-to (add x) = Prefl

------------------------------------------------------------------------
-- Set partitions with no consecutive numbers in a part

S'-def₁ : ∀ {n k} → S' (ℕsuc n) (ℕsuc k) ≡ (nat k) * S' n (ℕsuc k) + S' n k
S'-def₁ {n} {ℕzero} = proof (Pcong (λ x → x ℕ* ℕS' n (ℕsuc ℕzero) ℕ+ ℕS' n ℕzero) (Psym (nat-value ℕzero)))
                       (mkBij to from to-from from-to)
  where
    to : lift (S' (ℕsuc n) (ℕsuc ℕzero)) → lift ((nat ℕzero) * S' n (ℕsuc ℕzero) + S' n ℕzero)
    to (add x) = inj₂ x
    to (insert () x₁)
    -- to (insert (Fsuc x) x₁) = inj₁ (just (getFrom (nat-lift _) x) , x₁)
    -- to (add x) = inj₂ x
    -- to (insert Fzero x₁) = inj₁ (nothing , x₁)
    -- to (insert (Fsuc x) x₁) = inj₁ (just (getFrom (nat-lift _) x) , x₁)

    from : lift ((nat ℕzero) * S' n (ℕsuc ℕzero) + S' n ℕzero) → lift (S' (ℕsuc n) (ℕsuc ℕzero))
    from (inj₁ (() , y))
    from (inj₂ empty) = add empty
    -- from (inj₂ (add y)) = {!!}
    -- from (inj₂ (insert x y)) = {!!}
    -- from (inj₁ (just x , y)) = insert (Fsuc (getTo (nat-lift k) x)) y
    -- from (inj₁ (nothing , y)) = insert Fzero y
    -- from (inj₂ y) = add y

    to-from : ∀ y → to (from y) P≡ y
    to-from (inj₁ (() , y))
    to-from (inj₂ empty) = Prefl
    -- to-from (inj₁ (just x , y)) rewrite getFromTo (nat-lift k) x = Prefl
    -- to-from (inj₁ (nothing , y)) = Prefl
    -- to-from (inj₂ y) = Prefl

    from-to : ∀ x → from (to x) P≡ x
    from-to (add empty) = Prefl
    from-to (insert () x₁)
    -- from-to (add x) = Prefl
    -- from-to (insert Fzero x₁) = Prefl
    -- from-to (insert (Fsuc x) x₁) rewrite getToFrom (nat-lift k) x = Prefl

S'-def₁ {n} {ℕsuc k} = proof (Pcong (λ x → x ℕ* ℕS' n (ℕsuc (ℕsuc k)) ℕ+ ℕS' n (ℕsuc k)) (Psym (nat-value (ℕsuc k))))
                       (mkBij to from to-from from-to)
  where
    to : lift (S' (ℕsuc n) (ℕsuc (ℕsuc k))) → lift ((nat (ℕsuc k)) * S' n (ℕsuc (ℕsuc k)) + S' n (ℕsuc k))
    to (add x) = inj₂ x
    to (insert Fzero x₁) = inj₁ (nothing , x₁)
    to (insert (Fsuc x) x₁) = inj₁ (just (getFrom (nat-lift _) x) , x₁)
    -- to (add x) = inj₂ x
    -- to (insert Fzero x₁) = inj₁ (nothing , x₁)
    -- to (insert (Fsuc x) x₁) = inj₁ (just (getFrom (nat-lift _) x) , x₁)

    from : lift ((nat (ℕsuc k)) * S' n (ℕsuc (ℕsuc k)) + S' n (ℕsuc k)) → lift (S' (ℕsuc n) (ℕsuc (ℕsuc k)))
    from (inj₁ (just x , y)) = insert (Fsuc (getTo (nat-lift k) x)) y
    from (inj₁ (nothing , y)) = insert Fzero y
    -- from (inj₂ *) = {!!}
    from (inj₂ y) = add y
    -- from (inj₂ (insert x y)) = {!!}
    -- from (inj₁ (just x , y)) = insert (Fsuc (getTo (nat-lift k) x)) y
    -- from (inj₁ (nothing , y)) = insert Fzero y
    -- from (inj₂ y) = add y

    to-from : ∀ y → to (from y) P≡ y
    to-from (inj₁ (just x , y)) rewrite getFromTo (nat-lift k) x = Prefl
    to-from (inj₁ (nothing , y)) = Prefl
    to-from (inj₂ y) = Prefl
    -- to-from (inj₁ (just x , y)) rewrite getFromTo (nat-lift k) x = Prefl
    -- to-from (inj₁ (nothing , y)) = Prefl
    -- to-from (inj₂ y) = Prefl

    from-to : ∀ x → from (to x) P≡ x
    from-to (add x) = Prefl
    from-to (insert Fzero x₁) = Prefl
    from-to (insert (Fsuc x) x₁) rewrite getToFrom (nat-lift k) x = Prefl
    -- from-to (add x) = Prefl
    -- from-to (insert Fzero x₁) = Prefl
    -- from-to (insert (Fsuc x) x₁) rewrite getToFrom (nat-lift k) x = Prefl

S'-def₂ : ∀ {n} → S' (ℕsuc (ℕsuc n)) (ℕsuc ℕzero) ≡ zero
S'-def₂ {n} = proof Prefl (mkBij to from to-from from-to)
  where
    to : lift (S' (ℕsuc (ℕsuc n)) (ℕsuc ℕzero)) → lift zero
    to (add ())
    to (insert () x₁)

    from : lift zero → lift (S' (ℕsuc (ℕsuc n)) (ℕsuc ℕzero))
    from ()

    to-from : ∀ y → to (from y) P≡ y
    to-from ()

    from-to : ∀ x → from (to x) P≡ x
    from-to (add ())
    from-to (insert () x₁)

-- CS₂-def₁ : ∀ {l r} → CS₂ (ℕsuc l) (ℕsuc r) ≡ (nat l) * CS₂ (ℕsuc l) r + CS₂ l (ℕsuc r)
-- CS₂-def₁ {l} {r} = proof (Pcong (λ x → x ℕ* ℕCS₂ (ℕsuc l) r ℕ+ ℕCS₂ l (ℕsuc r)) (Psym (nat-value l))) (mkBij to from to-from from-to)
--   where
--     to : lift (CS₂ (ℕsuc l) (ℕsuc r)) → lift ((nat l) * CS₂ (ℕsuc l) r + CS₂ l (ℕsuc r))
--     to (add x) = inj₂ x
--     to (insert x x₁) = inj₁ ((getFrom (nat-lift l) x) , x₁)

--     from : lift ((nat l) * CS₂ (ℕsuc l) r + CS₂ l (ℕsuc r)) → lift (CS₂ (ℕsuc l) (ℕsuc r))
--     from (inj₁ (a , b)) = insert (getTo (nat-lift l) a) b
--     from (inj₂ y) = add y

--     to-from : ∀ y → to (from y) P≡ y
--     to-from (inj₁ (x₁ , x₂)) = Pcong (λ t → inj₁ (t , x₂)) (getFromTo (nat-lift l) x₁)
--     to-from (inj₂ y) = Prefl

--     from-to : ∀ x → from (to x) P≡ x
--     from-to (add x) = Prefl
--     from-to (insert x x₁) = Pcong (λ t → insert t x₁) (getToFrom (nat-lift l) x)

-- CS₂-def₂ : ∀ {l} → CS₂ (ℕsuc l) ℕzero ≡ CS₂ l ℕzero
-- CS₂-def₂ {l} = proof Prefl (mkBij to from to-from from-to)
--   where
--     to : CSetPartitionK (ℕsuc l) ℕzero → CSetPartitionK l ℕzero
--     to (add x) = x

--     from : CSetPartitionK l ℕzero → CSetPartitionK (ℕsuc l) ℕzero
--     from x = add x

--     to-from : ∀ y → to (from y) P≡ y
--     to-from y = Prefl

--     from-to : ∀ x → from (to x) P≡ x
--     from-to (add x) = Prefl

------------------------------------------------------------------------
-- Binary strings with l zeros and r ones

choose-def₁ : ∀ {l r} → (ℕsuc l) choose (ℕsuc r) ≡ l choose (ℕsuc r) + (ℕsuc l) choose r
choose-def₁ {l} {r} = proof Prefl (mkBij to from to-from from-to)
  where
    to : lift ((ℕsuc l) choose (ℕsuc r)) → lift (l choose (ℕsuc r) + (ℕsuc l) choose r)
    to (0∷ x) = inj₁ x
    to (1∷ x) = inj₂ x

    from : lift (l choose (ℕsuc r) + (ℕsuc l) choose r) → lift ((ℕsuc l) choose (ℕsuc r))
    from (inj₁ x) = 0∷ x
    from (inj₂ y) = 1∷ y

    to-from : ∀ y → to (from y) P≡ y
    to-from (inj₁ x) = Prefl
    to-from (inj₂ y) = Prefl

    from-to : ∀ x → from (to x) P≡ x
    from-to (0∷ x) = Prefl
    from-to (1∷ x) = Prefl

choose-def₂ : ∀ {r} → ℕzero choose (ℕsuc r) ≡ ℕzero choose r
choose-def₂ {r} = proof Prefl (mkBij to from to-from from-to)
  where
    to : lift (ℕzero choose (ℕsuc r)) → lift (ℕzero choose r)
    to (1∷ x) = x

    from : lift (ℕzero choose r) → lift (ℕzero choose (ℕsuc r))
    from x = 1∷ x

    to-from : ∀ y → to (from y) P≡ y
    to-from x = Prefl

    from-to : ∀ x → from (to x) P≡ x
    from-to (1∷ x) = Prefl

choose-def₃ : ∀ {l} → (ℕsuc l) choose ℕzero ≡ l choose ℕzero
choose-def₃ {l} = proof Prefl (mkBij to from to-from from-to)
  where
    to : lift ((ℕsuc l) choose ℕzero) → lift (l choose ℕzero)
    to (0∷ x) = x

    from : lift (l choose ℕzero) → lift ((ℕsuc l) choose ℕzero)
    from x = 0∷ x

    to-from : ∀ y → to (from y) P≡ y
    to-from x = Prefl

    from-to : ∀ x → from (to x) P≡ x
    from-to (0∷ x) = Prefl
