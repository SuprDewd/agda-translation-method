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

fin-value : ∀ {n} → value (fin n) P≡ n
fin-value {ℕzero} = Prefl
fin-value {ℕsuc n} rewrite fin-value {n} = Prefl

thrice : ∀ {n} → three * fib (ℕsuc (ℕsuc n)) ≡ fib (ℕsuc (ℕsuc (ℕsuc (ℕsuc n)))) + fib n
-- thrice {n} rewrite Psym (fin-value {n}) = solve 1 (λ x → :three :* :fib (:suc (:suc x)) := :fib (:suc (:suc (:suc (:suc x)))) :+ :fib x) refl (fin n)
thrice {0} = axiom Prefl (mkBij to from)
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

thrice {1} = axiom Prefl (mkBij to from)
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

thrice {ℕsuc (ℕsuc n)} = -- rewrite Psym (fin-value {n}) = solve 1 (λ x → :three :* :fib (:suc (:suc (:suc (:suc x)))) := :fib (:suc (:suc (:suc (:suc (:suc (:suc x)))))) :+ :fib (:suc (:suc x))) refl (fin n)
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
lemma {n} rewrite Psym (fin-value {n}) =
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
  cassini-odd ℕzero = axiom Prefl (mkBij to from)
    where
      -- TODO: There are two possible base cases. Try both of them?
      to : (FibStr 2 × FibStr 0) → (FibStr 1 × FibStr 1 ⊎ Maybe (Fin ℕzero))
      to (([] ∷1 ∷1) , []) = inj₂ nothing
      to (([] ∷2) , []) = inj₁ (([] ∷1) , ([] ∷1))

      from : (FibStr 1 × FibStr 1 ⊎ Maybe (Fin ℕzero)) → (FibStr 2 × FibStr 0)
      from (inj₂ nothing) = ([] ∷1 ∷1) , []
      from (inj₁ (([] ∷1) , ([] ∷1))) = ([] ∷2) , []
      from (inj₂ (just ()))

  cassini-odd (ℕsuc k) =
    begin
      fib (2 ℕ* (ℕsuc k) ℕ+ 2) * fib (2 ℕ* (ℕsuc k))
    ≡⟨ Pcong (λ x → fib x * fib (2 ℕ* (ℕsuc k))) (NPS.+-comm (2 ℕ* (ℕsuc k)) 2) ⟩
      (fib (ℕsuc (ℕsuc (2 ℕ* (ℕsuc k))))) * fib (2 ℕ* (ℕsuc k))
    ≈⟨ *-cong fib-def refl ⟩
      (fib (ℕsuc (2 ℕ* (ℕsuc k))) + fib (2 ℕ* (ℕsuc k))) * fib (2 ℕ* (ℕsuc k))
    ≈⟨ distribʳ-*-+ ⟩
      fib (ℕsuc (2 ℕ* (ℕsuc k))) * fib (2 ℕ* (ℕsuc k)) + fib (2 ℕ* (ℕsuc k)) * fib (2 ℕ* (ℕsuc k))
    ≡⟨ Pcong (λ x → fib (ℕsuc (2 ℕ* (ℕsuc k))) * fib (2 ℕ* (ℕsuc k)) + fib x * fib (2 ℕ* (ℕsuc k))) (lem2 2 k) ⟩
      fib (ℕsuc (2 ℕ* (ℕsuc k))) * fib (2 ℕ* (ℕsuc k)) + fib (2 ℕ* k ℕ+ 2) * fib (2 ℕ* (ℕsuc k))
    ≡⟨ Pcong (λ x → fib (ℕsuc (2 ℕ* (ℕsuc k))) * fib (2 ℕ* (ℕsuc k)) + fib (2 ℕ* k ℕ+ 2) * fib x) (lem2 2 k) ⟩
      fib (ℕsuc (2 ℕ* (ℕsuc k))) * fib (2 ℕ* (ℕsuc k)) + fib (2 ℕ* k ℕ+ 2) * fib (2 ℕ* k ℕ+ 2)
    ≈⟨ +-cong refl (cassini-even k) ⟩
      fib (ℕsuc (2 ℕ* (ℕsuc k))) * fib (2 ℕ* (ℕsuc k)) + (fib (2 ℕ* k ℕ+ 3) * fib (2 ℕ* k ℕ+ 1) + one)
    ≈⟨ sym +-assoc ⟩
      (fib (ℕsuc (2 ℕ* (ℕsuc k))) * fib (2 ℕ* (ℕsuc k)) + fib (2 ℕ* k ℕ+ 3) * fib (2 ℕ* k ℕ+ 1)) + one
    ≡⟨ Pcong (λ x → (fib x * fib (2 ℕ* (ℕsuc k)) + fib (2 ℕ* k ℕ+ 3) * fib (2 ℕ* k ℕ+ 1)) + one) (NPS.+-comm 1 (2 ℕ* (ℕsuc k))) ⟩
      (fib ((2 ℕ* (ℕsuc k)) ℕ+ 1) * fib (2 ℕ* (ℕsuc k)) + fib (2 ℕ* k ℕ+ 3) * fib (2 ℕ* k ℕ+ 1)) + one
    ≡⟨ Pcong (λ x → (fib (x ℕ+ 1) * fib (2 ℕ* (ℕsuc k)) + fib (2 ℕ* k ℕ+ 3) * fib (2 ℕ* k ℕ+ 1)) + one) (lem2 2 k) ⟩
      (fib ((2 ℕ* k ℕ+ 2) ℕ+ 1) * fib (2 ℕ* (ℕsuc k)) + fib (2 ℕ* k ℕ+ 3) * fib (2 ℕ* k ℕ+ 1)) + one
    ≡⟨ Pcong (λ x → (fib x * fib (2 ℕ* (ℕsuc k)) + fib (2 ℕ* k ℕ+ 3) * fib (2 ℕ* k ℕ+ 1)) + one) (NPS.+-assoc (2 ℕ* k) 2 1) ⟩
      (fib (2 ℕ* k ℕ+ 3) * fib (2 ℕ* (ℕsuc k)) + fib (2 ℕ* k ℕ+ 3) * fib (2 ℕ* k ℕ+ 1)) + one
    ≈⟨ +-cong (sym distribˡ-*-+) refl ⟩
      fib (2 ℕ* k ℕ+ 3) * (fib (2 ℕ* (ℕsuc k)) + fib (2 ℕ* k ℕ+ 1)) + one
    ≡⟨ Pcong (λ x → fib (2 ℕ* k ℕ+ 3) * (fib x + fib (2 ℕ* k ℕ+ 1)) + one) (lem2 2 k) ⟩
      fib (2 ℕ* k ℕ+ 3) * (fib (2 ℕ* k ℕ+ 2) + fib (2 ℕ* k ℕ+ 1)) + one
    ≡⟨ Pcong (λ x → fib (2 ℕ* k ℕ+ 3) * (fib x + fib (2 ℕ* k ℕ+ 1)) + one) (NPS.+-suc (2 ℕ* k) 1) ⟩
      fib (2 ℕ* k ℕ+ 3) * (fib (ℕsuc (2 ℕ* k ℕ+ 1)) + fib (2 ℕ* k ℕ+ 1)) + one
    ≈⟨ +-cong (*-cong refl (sym fib-def)) refl ⟩
      fib (2 ℕ* k ℕ+ 3) * (fib (ℕsuc (ℕsuc (2 ℕ* k ℕ+ 1)))) + one
    ≡⟨ Pcong (λ x → fib (2 ℕ* k ℕ+ 3) * (fib x) + one) (NPS.+-comm 2 (2 ℕ* k ℕ+ 1)) ⟩
      fib (2 ℕ* k ℕ+ 3) * (fib ((2 ℕ* k ℕ+ 1) ℕ+ 2)) + one
    ≡⟨ Pcong (λ x → fib (2 ℕ* k ℕ+ 3) * (fib x) + one) (NPS.+-assoc (2 ℕ* k) 1 2) ⟩
      fib (2 ℕ* k ℕ+ 3) * fib (2 ℕ* k ℕ+ 3) + one
    ≡⟨ Pcong (λ x → fib x * fib (2 ℕ* k ℕ+ 3) + one) (Psym (NPS.+-assoc (2 ℕ* k) 2 1)) ⟩
      fib ((2 ℕ* k ℕ+ 2) ℕ+ 1) * fib (2 ℕ* k ℕ+ 3) + one
    ≡⟨ Pcong (λ x → fib (x ℕ+ 1) * fib (2 ℕ* k ℕ+ 3) + one) (Psym (lem2 2 k)) ⟩
      fib ((2 ℕ* (ℕsuc k)) ℕ+ 1) * fib (2 ℕ* k ℕ+ 3) + one
    ≡⟨ Pcong (λ x → fib ((2 ℕ* (ℕsuc k)) ℕ+ 1) * fib x + one) (Psym (NPS.+-assoc (2 ℕ* k) 2 1)) ⟩
      fib ((2 ℕ* (ℕsuc k)) ℕ+ 1) * fib ((2 ℕ* k ℕ+ 2) ℕ+ 1) + one
    ≡⟨ Pcong (λ x → fib ((2 ℕ* (ℕsuc k)) ℕ+ 1) * fib (x ℕ+ 1) + one) (Psym (lem2 2 k)) ⟩
      fib (2 ℕ* (ℕsuc k) ℕ+ 1) * fib (2 ℕ* (ℕsuc k) ℕ+ 1) + one
    ∎

  cassini-even : ∀ k → fib (2 ℕ* k ℕ+ 2) * fib (2 ℕ* k ℕ+ 2)
                     ≡ fib (2 ℕ* k ℕ+ 3) * fib (2 ℕ* k ℕ+ 1) + one
  cassini-even k =
    begin
      fib (2 ℕ* k ℕ+ 2) * fib (2 ℕ* k ℕ+ 2)
    -- ≡⟨ Pcong (λ x → fib (2 ℕ* k ℕ+ 2) * fib x) (NPS.+-comm (2 ℕ* k) 2) ⟩
    --   fib (2 ℕ* k ℕ+ 2) * fib (ℕsuc (ℕsuc (2 ℕ* k)))
    -- ≈⟨ *-cong refl fib-def ⟩
    --   fib (2 ℕ* k ℕ+ 2) * (fib (ℕsuc (2 ℕ* k)) + fib (2 ℕ* k))
    -- ≈⟨ distribˡ-*-+ ⟩
    ≈⟨ clem1 ⟩
      fib (2 ℕ* k ℕ+ 2) * fib (ℕsuc (2 ℕ* k)) + fib (2 ℕ* k ℕ+ 2) * fib (2 ℕ* k)
    ≈⟨ +-cong refl (cassini-odd k) ⟩
      fib (2 ℕ* k ℕ+ 2) * fib (ℕsuc (2 ℕ* k)) + (fib (2 ℕ* k ℕ+ 1) * fib (2 ℕ* k ℕ+ 1) + one)
    ≈⟨ clem2 ⟩
    -- ≈⟨ sym +-assoc ⟩
    --   (fib (2 ℕ* k ℕ+ 2) * fib (ℕsuc (2 ℕ* k)) + fib (2 ℕ* k ℕ+ 1) * fib (2 ℕ* k ℕ+ 1)) + one
    -- ≡⟨ Pcong (λ x → (fib (2 ℕ* k ℕ+ 2) * fib x + fib (2 ℕ* k ℕ+ 1) * fib (2 ℕ* k ℕ+ 1)) + one) (NPS.+-comm 1 (2 ℕ* k)) ⟩
    --   (fib (2 ℕ* k ℕ+ 2) * fib (2 ℕ* k ℕ+ 1) + fib (2 ℕ* k ℕ+ 1) * fib (2 ℕ* k ℕ+ 1)) + one
    -- ≈⟨ +-cong (sym distribʳ-*-+) refl ⟩
    --   (fib (2 ℕ* k ℕ+ 2) + fib (2 ℕ* k ℕ+ 1)) * fib (2 ℕ* k ℕ+ 1) + one
    --   ≡⟨ Pcong (λ x → (fib x + fib (2 ℕ* k ℕ+ 1)) * fib (2 ℕ* k ℕ+ 1) + one) (NPS.+-suc (2 ℕ* k) 1) ⟩
    --   (fib (ℕsuc (2 ℕ* k ℕ+ 1)) + fib (2 ℕ* k ℕ+ 1)) * fib (2 ℕ* k ℕ+ 1) + one
    -- ≈⟨ +-cong (*-cong (sym fib-def) refl) refl ⟩
    --   fib (ℕsuc (ℕsuc (2 ℕ* k ℕ+ 1))) * fib (2 ℕ* k ℕ+ 1) + one
    -- ≡⟨ Pcong (λ x → fib x * fib (2 ℕ* k ℕ+ 1) + one) (NPS.+-comm 2 (k ℕ+ (k ℕ+ ℕzero) ℕ+ 1)) ⟩
    --   fib ((2 ℕ* k ℕ+ 1) ℕ+ 2) * fib (2 ℕ* k ℕ+ 1) + one
    -- ≡⟨ Pcong (λ x → fib x * fib (2 ℕ* k ℕ+ 1) + one) (NPS.+-assoc (2 ℕ* k) 1 2) ⟩
      fib (2 ℕ* k ℕ+ 3) * fib (2 ℕ* k ℕ+ 1) + one
    ∎
    where
      clem1 : fib (k ℕ+ (k ℕ+ ℕzero) ℕ+ 2) * fib (k ℕ+ (k ℕ+ ℕzero) ℕ+ 2) ≡ (fib (k ℕ+ (k ℕ+ ℕzero) ℕ+ 2) * fib (ℕsuc (k ℕ+ (k ℕ+ ℕzero))) + fib (k ℕ+ (k ℕ+ ℕzero) ℕ+ 2) * fib (k ℕ+ (k ℕ+ ℕzero)))
      clem1 rewrite (Psym (fin-value {k})) = solve 1 (λ x → :fib (:two :* x :+ :two) :* :fib (:two :* x :+ :two) := :fib (:two :* x :+ :two) :* :fib (:suc (:two :* x)) :+ :fib (:two :* x :+ :two) :* :fib (:two :* x)) refl (fin k)

      clem2 : fib (k ℕ+ (k ℕ+ ℕzero) ℕ+ 2) * fib (ℕsuc (k ℕ+ (k ℕ+ ℕzero))) + (fib (k ℕ+ (k ℕ+ ℕzero) ℕ+ 1) * fib (k ℕ+ (k ℕ+ ℕzero) ℕ+ 1) + one) ≡ (fib (k ℕ+ (k ℕ+ ℕzero) ℕ+ 3) * fib (k ℕ+ (k ℕ+ ℕzero) ℕ+ 1) + one)
      clem2 rewrite (Psym (fin-value {k})) = solve 1 (λ x → :fib (x :+ (x :+ :zero) :+ :two) :* :fib (:suc (x :+ (x :+ :zero))) :+ (:fib (x :+ (x :+ :zero) :+ :one) :* :fib (x :+ (x :+ :zero) :+ :one) :+ :one) := (:fib (x :+ (x :+ :zero) :+ :three) :* :fib (x :+ (x :+ :zero) :+ :one) :+ :one)) refl (fin k)

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

  show≡ : ∀ {A B : Expr} → A ≡ B → IO ⊤
  show≡ {A} {B} p = mapM′ (proj (getTo (toBijection p))) (CL.fromList (generate A)) >>' return tt
    where
      proj : (Translate.lift A → Translate.lift B) → Translate.lift A → IO ⊤
      proj f x =
        putStr (Translate.show A x) >>'
        putStr " -> " >>'
        putStrLn (Translate.show B (f x)) >>'
        return tt

  count : (start : ℕ) → CL.Colist ℕ
  count x = x CL.∷ ♯ count (ℕsuc x)

  main : BIO.IO ⊤
  main = run $ mapM′ (λ n →
                            -- putStrLn (ℕshow n) >>'
                            -- show≡ (thrice {n}) >>'
                            -- show≡ (thrice' {n}) >>'
                            putStrLn (ℕshow (2 ℕ* n ℕ+ 1)) >>'
                            show≡ (sym (cassini-odd n)) >>'
                            putStrLn "" >>'
                            putStrLn (ℕshow (2 ℕ* n ℕ+ 2)) >>'
                            show≡ (cassini-even n) >>'
                            putStrLn "")
                     (count ℕzero) >>'
         return tt

open Runner using (main)
