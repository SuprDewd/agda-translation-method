module thrice where

open import Function

open import Translate
open import Translate.Solver
-- open import Translate.Fibonacci
open import Translate.Combinatorics
open import Translate.Support
open import Translate.EqReasoning
open import Translate.Axioms
open import Translate.Bijection using (getTo)
open import Translate.Tools

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
-- thrice {n} rewrite fin-value n = solve 1 (λ x → :three :* :fib (:suc (:suc x)) := :fib (:suc (:suc (:suc (:suc x)))) :+ :fib x) refl (fin n)
thrice {0} = axiom Prefl (mkBij to from toFrom fromTo)
  where
    to : lift (three * fib 2) → lift (fib 4 + fib 0)
    to (nothing             , [] ∷1 ∷1) = inj₁ ([] ∷1 ∷1 ∷1 ∷1)
    to (nothing             , [] ∷2)    = inj₁ ([] ∷1 ∷1 ∷2)
    to (just nothing        , [] ∷1 ∷1) = inj₁ ([] ∷2 ∷1 ∷1)
    to (just nothing        , [] ∷2)    = inj₁ ([] ∷2 ∷2)
    to (just (just nothing) , [] ∷1 ∷1) = inj₁ ([] ∷1 ∷2 ∷1)
    to (just (just nothing) , [] ∷2)    = inj₂ []
    to (just (just (just ())) , _)

    from : lift (fib 4 + fib 0) → lift (three * fib 2)
    from (inj₁ ([] ∷1 ∷1 ∷1 ∷1)) = nothing             , [] ∷1 ∷1
    from (inj₁ ([] ∷1 ∷1 ∷2))    = nothing             , [] ∷2
    from (inj₁ ([] ∷2 ∷1 ∷1))    = just nothing        , [] ∷1 ∷1
    from (inj₁ ([] ∷2 ∷2))       = just nothing        , [] ∷2
    from (inj₁ ([] ∷1 ∷2 ∷1))    = just (just nothing) , [] ∷1 ∷1
    from (inj₂ [])               = just (just nothing) , [] ∷2

    toFrom : ∀ y → to (from y) P≡ y
    toFrom (inj₁ ([] ∷1 ∷1 ∷1 ∷1)) = Prefl
    toFrom (inj₁ ([] ∷1 ∷1 ∷2))    = Prefl
    toFrom (inj₁ ([] ∷2 ∷1 ∷1))    = Prefl
    toFrom (inj₁ ([] ∷2 ∷2))       = Prefl
    toFrom (inj₁ ([] ∷1 ∷2 ∷1))    = Prefl
    toFrom (inj₂ [])               = Prefl

    fromTo : ∀ x → from (to x) P≡ x
    fromTo (nothing             , [] ∷1 ∷1) = Prefl
    fromTo (nothing             , [] ∷2)    = Prefl
    fromTo (just nothing        , [] ∷1 ∷1) = Prefl
    fromTo (just nothing        , [] ∷2)    = Prefl
    fromTo (just (just nothing) , [] ∷1 ∷1) = Prefl
    fromTo (just (just nothing) , [] ∷2)    = Prefl
    fromTo (just (just (just ())) , _)

thrice {1} = axiom Prefl (mkBij to from toFrom fromTo)
  where
    to : lift (three * fib 3) → lift (fib 5 + fib 1)
    to (nothing             , [] ∷1 ∷1 ∷1) = inj₁ ([] ∷1 ∷1 ∷1 ∷1 ∷1)
    to (nothing             , [] ∷1 ∷2)    = inj₁ ([] ∷1 ∷1 ∷1 ∷2)
    to (nothing             , [] ∷2 ∷1)    = inj₁ ([] ∷1 ∷1 ∷2 ∷1)
    to (just nothing        , [] ∷1 ∷1 ∷1) = inj₁ ([] ∷2 ∷1 ∷1 ∷1)
    to (just nothing        , [] ∷1 ∷2)    = inj₁ ([] ∷2 ∷1 ∷2)
    to (just nothing        , [] ∷2 ∷1)    = inj₁ ([] ∷2 ∷2 ∷1)
    to (just (just nothing) , [] ∷1 ∷1 ∷1) = inj₁ ([] ∷1 ∷2 ∷1 ∷1)
    to (just (just nothing) , [] ∷1 ∷2)    = inj₁ ([] ∷1 ∷2 ∷2)
    to (just (just nothing) , [] ∷2 ∷1)    = inj₂ ([] ∷1)
    to (just (just (just ())) , _)

    from : lift (fib 5 + fib 1) → lift (three * fib 3)
    from (inj₁ ([] ∷1 ∷1 ∷1 ∷1 ∷1)) = nothing             , [] ∷1 ∷1 ∷1
    from (inj₁ ([] ∷1 ∷1 ∷1 ∷2))    = nothing             , [] ∷1 ∷2
    from (inj₁ ([] ∷1 ∷1 ∷2 ∷1))    = nothing             , [] ∷2 ∷1
    from (inj₁ ([] ∷2 ∷1 ∷1 ∷1))    = just nothing        , [] ∷1 ∷1 ∷1
    from (inj₁ ([] ∷2 ∷1 ∷2))       = just nothing        , [] ∷1 ∷2
    from (inj₁ ([] ∷2 ∷2 ∷1))       = just nothing        , [] ∷2 ∷1
    from (inj₁ ([] ∷1 ∷2 ∷1 ∷1))    = just (just nothing) , [] ∷1 ∷1 ∷1
    from (inj₁ ([] ∷1 ∷2 ∷2))       = just (just nothing) , [] ∷1 ∷2
    from (inj₂ ([] ∷1))             = just (just nothing) , [] ∷2 ∷1

    toFrom : ∀ y → to (from y) P≡ y
    toFrom (inj₁ ([] ∷1 ∷1 ∷1 ∷1 ∷1)) = Prefl
    toFrom (inj₁ ([] ∷1 ∷1 ∷1 ∷2))    = Prefl
    toFrom (inj₁ ([] ∷1 ∷1 ∷2 ∷1))    = Prefl
    toFrom (inj₁ ([] ∷2 ∷1 ∷1 ∷1))    = Prefl
    toFrom (inj₁ ([] ∷2 ∷1 ∷2))       = Prefl
    toFrom (inj₁ ([] ∷2 ∷2 ∷1))       = Prefl
    toFrom (inj₁ ([] ∷1 ∷2 ∷1 ∷1))    = Prefl
    toFrom (inj₁ ([] ∷1 ∷2 ∷2))       = Prefl
    toFrom (inj₂ ([] ∷1))             = Prefl

    fromTo : ∀ x → from (to x) P≡ x
    fromTo (nothing             , [] ∷1 ∷1 ∷1) = Prefl
    fromTo (nothing             , [] ∷1 ∷2)    = Prefl
    fromTo (nothing             , [] ∷2 ∷1)    = Prefl
    fromTo (just nothing        , [] ∷1 ∷1 ∷1) = Prefl
    fromTo (just nothing        , [] ∷1 ∷2)    = Prefl
    fromTo (just nothing        , [] ∷2 ∷1)    = Prefl
    fromTo (just (just nothing) , [] ∷1 ∷1 ∷1) = Prefl
    fromTo (just (just nothing) , [] ∷1 ∷2)    = Prefl
    fromTo (just (just nothing) , [] ∷2 ∷1)    = Prefl
    fromTo (just (just (just ())) , _)

thrice {ℕsuc (ℕsuc n)} = -- rewrite fin-value n = solve 1 (λ x → :three :* :fib (:suc (:suc (:suc (:suc x)))) := :fib (:suc (:suc (:suc (:suc (:suc (:suc x)))))) :+ :fib (:suc (:suc x))) refl (fin n)
  begin
    three * fib (4 ℕ+ n)
  ≈⟨ *-cong refl fib-def ⟩
    three * (fib (3 ℕ+ n) + fib (2 ℕ+ n))
  ≈⟨ distribˡ-*-+ ⟩
    three * fib (3 ℕ+ n) + three * fib (2 ℕ+ n)
  ≈⟨ +-cong thrice thrice ⟩
    (fib (5 ℕ+ n) + fib (1 ℕ+ n)) + (fib (4 ℕ+ n) + fib n)
  ≈⟨ +-assoc ⟩
    fib (5 ℕ+ n) + (fib (1 ℕ+ n) + (fib (4 ℕ+ n) + fib n))
  ≈⟨ +-cong refl +-comm ⟩
    fib (5 ℕ+ n) + ((fib (4 ℕ+ n) + fib n) + fib (1 ℕ+ n))
  ≈⟨ +-cong refl +-assoc ⟩
    fib (5 ℕ+ n) + (fib (4 ℕ+ n) + (fib n + fib (1 ℕ+ n)))
  ≈⟨ +-cong refl (+-cong refl +-comm) ⟩
    fib (5 ℕ+ n) + (fib (4 ℕ+ n) + (fib (1 ℕ+ n) + fib n))
  ≈⟨ sym +-assoc ⟩
    (fib (5 ℕ+ n) + fib (4 ℕ+ n)) + (fib (1 ℕ+ n) + fib n)
  ≈⟨ +-cong (sym fib-def) (sym fib-def) ⟩
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
  ≈⟨ *-cong refl fib-def  ⟩
    three * (fib (ℕsuc n) + fib n)
  -- ≈⟨ distribˡ-*-+ ⟩
  --   three * fib (ℕsuc n) + three * fib n
  -- ≈⟨ +-cong *-comm  *-comm ⟩
  --   fib (ℕsuc n) * three + fib n * three
  -- ≈⟨ +-cong +-*-suc +-*-suc ⟩
  --   (fib (ℕsuc n) + fib (ℕsuc n) * two) + (fib n + fib n * two)
  -- ≈⟨ +-cong (+-cong refl +-*-suc) (+-cong refl +-*-suc) ⟩
  --   (fib (ℕsuc n) + (fib (ℕsuc n) + fib (ℕsuc n) * one)) + (fib n + (fib n + fib n * one))
  -- ≈⟨ +-cong (+-cong refl (+-cong refl *-right-identity)) (+-cong refl (+-cong refl *-right-identity)) ⟩
  --   (fib (ℕsuc n) + (fib (ℕsuc n) + fib (ℕsuc n))) + (fib n + (fib n + fib n))
  -- ≈⟨ +-assoc ⟩
  --   fib (ℕsuc n) + ((fib (ℕsuc n) + fib (ℕsuc n)) + (fib n + (fib n + fib n)))
  -- ≈⟨ +-cong refl (+-assoc) ⟩
  --   fib (ℕsuc n) + (fib (ℕsuc n) + (fib (ℕsuc n) + (fib n + (fib n + fib n))))
  -- ≈⟨ +-cong refl (+-cong refl (sym +-assoc)) ⟩
  --   fib (ℕsuc n) + (fib (ℕsuc n) + ((fib (ℕsuc n) + fib n) + (fib n + fib n)))
  -- ≈⟨ +-cong refl (+-cong refl (sym +-assoc)) ⟩
  --   fib (ℕsuc n) + (fib (ℕsuc n) + (((fib (ℕsuc n) + fib n) + fib n) + fib n))
  -- ≈⟨ +-cong refl (sym +-assoc) ⟩
  --   fib (ℕsuc n) + ((fib (ℕsuc n) + ((fib (ℕsuc n) + fib n) + fib n)) + fib n)
  -- ≈⟨ sym +-assoc ⟩
  --   (fib (ℕsuc n) + (fib (ℕsuc n) + ((fib (ℕsuc n) + fib n) + fib n))) + fib n
  -- ≈⟨ +-comm ⟩
  --   fib n + (fib (ℕsuc n) + (fib (ℕsuc n) + ((fib (ℕsuc n) + fib n) + fib n)))
  -- ≈⟨ sym +-assoc ⟩
  --   (fib n + fib (ℕsuc n)) + (fib (ℕsuc n) + ((fib (ℕsuc n) + fib n) + fib n))
  -- ≈⟨ +-cong +-comm refl ⟩
  --   (fib (ℕsuc n) + fib n) + (fib (ℕsuc n) + ((fib (ℕsuc n) + fib n) + fib n))
  -- ≈⟨ sym +-assoc ⟩
  --   ((fib (ℕsuc n) + fib n) + fib (ℕsuc n)) + ((fib (ℕsuc n) + fib n) + fib n)
  -- ≈⟨ sym +-assoc ⟩
  ≈⟨ lemma ⟩
    (((fib (ℕsuc n) + fib n) + fib (ℕsuc n)) + (fib (ℕsuc n) + fib n)) + fib n
  ≈⟨ +-cong (+-cong (+-cong (sym fib-def) refl) refl) refl ⟩
    ((fib (ℕsuc (ℕsuc n)) + fib (ℕsuc n)) + (fib (ℕsuc n) + fib n)) + fib n
  ≈⟨ +-cong (+-cong (sym fib-def) (sym fib-def)) refl ⟩
    (fib (ℕsuc (ℕsuc (ℕsuc n))) + fib (ℕsuc (ℕsuc n))) + fib n
  ≈⟨ +-cong (sym fib-def) refl ⟩
    fib (ℕsuc (ℕsuc (ℕsuc (ℕsuc n)))) + fib n
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
