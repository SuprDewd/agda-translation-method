
module Translate.Solver where

open import Translate.Support
open import Translate.Base
open import Translate.EqReasoning
open import Translate.Support
open import Translate.Types
open import Translate.Axioms
open import Translate.Semiring
open import Translate.Properties

open import Translate.Solver.Types
open import Translate.Solver.Semiring

open import Data.Vec as V
open import Data.List as L
open import Data.Nat
  using ()
  renaming ( compare to ℕcompare
           ; less to ℕless
           ; equal to ℕequal
           ; greater to ℕgreater
           )

open import Relation.Nullary
open import Function
import Data.Fin as F
open import Data.Product

-- meow : :Expr 3
-- meow = quoteGoal x in {!x!}

open import Translate.Solver.Reflection
open import Translate.Solver.Types
open import Translate.Solver.Combinatorics

-- TODO: Clean this up and integrate into new AST design
--
-- open import Level renaming (zero to Lzero; suc to Lzuc)
-- open import Algebra
-- open import Data.Vec
-- open import Data.Nat as N using (ℕ)
-- import Data.Nat.Properties.Simple as NPS
-- open import Data.Fin as F using (Fin)
-- open import Data.Product
-- import Relation.Binary.PropositionalEquality as P
-- import Data.Bool as B
-- 
-- 
-- import Relation.Binary.Reflection as Reflection
-- open import Relation.Binary
-- open import Relation.Nullary
-- 
-- module SemiringSolver2 {ℓ₁ ℓ₂}
--                        (cs : CommutativeSemiring ℓ₁ ℓ₂)
--                        (_≟0 : ∀ x → Dec ((CommutativeSemiring._≡_ cs) x (CommutativeSemiring.0# cs))) where
-- 
-- open CommutativeSemiring cs
-- import Relation.Binary.EqReasoning as EqR; open EqR setoid
-- 
infixl 6 _C*_
infixl 5 _C+_

------------------------------------------------------------------------
-- Polynomial

-- data Polynomial : (n : ℕ) → Set ℓ₁ where
--   con : ∀ {n} → Expr → Polynomial n
--   var : ∀ {n} → (Fin n) → Polynomial n
--   _∗+_ : ∀ {n} → Polynomial n → Polynomial n → Polynomial n
--   _∗*_ : ∀ {n} → Polynomial n → Polynomial n → Polynomial n

-- _≟0 : (e : Expr) → Dec (e ≡ zero)
-- _≟0 = {!!}

⟦_⟧ : ∀ {n} → Polynomial n → Vec Expr n → Expr
⟦ ∗atom x ⟧ Γ = semantics x Γ
-- ⟦ ∗var x ⟧ Γ = lookup x Γ
⟦ ∗zero ⟧ Γ = zero
⟦ ∗suc x ⟧ Γ = suc (⟦ x ⟧ Γ)
⟦ l ∗+ r ⟧ Γ = ⟦ l ⟧ Γ + ⟦ r ⟧ Γ
⟦ l ∗* r ⟧ Γ = ⟦ l ⟧ Γ * ⟦ r ⟧ Γ

import Level as L
ℓ₁ : L.Level
ℓ₁ = L.suc L.zero

private

  -- distribˡ-*-+ : ∀ {a b c} → a * (b + c) ≡ a * b + a * c
  -- distribˡ-*-+ = ?

  suc-expand : ∀ {x} → suc x ≡ suc zero + x
  suc-expand {x} = axiom Prefl (mkBij to from)
    where
      to : lift (suc x) → lift (suc zero + x)
      to (just y) = inj₂ y
      to nothing = inj₁ nothing

      from : lift (suc zero + x) → lift (suc x)
      from (inj₁ (just ()))
      from (inj₁ nothing) = nothing
      from (inj₂ y) = just y

  suc-pull : ∀ {a b} → suc a + b ≡ suc (a + b)
  suc-pull {a} {b} = axiom Prefl (mkBij to from)
    where
      to : lift (suc a + b) → lift (suc (a + b))
      to (inj₁ (just x)) = just (inj₁ x)
      to (inj₁ nothing) = nothing
      to (inj₂ y) = just (inj₂ y)

      from : lift (suc (a + b)) → lift (suc a + b)
      from (just (inj₁ x)) = inj₁ (just x)
      from nothing = inj₁ nothing
      from (just (inj₂ y)) = inj₂ y

  suc-cong : ∀ {a b} → a ≡ b → suc a ≡ suc b
  suc-cong p with (toEquality p) | (toBijection p)
  suc-cong {a} {b} p | q | mkBij t f = axiom (Pcong (λ x → ℕsuc x) q) (mkBij to from)
    where
      to : lift (suc a) → lift (suc b)
      to (just x) = just (t x)
      to nothing = nothing

      from : lift (suc b) → lift (suc a)
      from (just x) = just (f x)
      from nothing = nothing

  suc-* : ∀ {a b} → suc a * b ≡ b + a * b
  suc-* {a} {b} = axiom Prefl (mkBij to from)
    where
      to : lift (suc a * b) → lift (b + a * b)
      to (just x , y) = inj₂ (x , y)
      to (nothing , y) = inj₁ y

      from : lift (b + a * b) → lift (suc a * b)
      from (inj₁ y) = nothing , y
      from (inj₂ (x , y)) = just x , y

------------------------------------------------------------------------
-- Expansion

-- data Constant : Set where
--   zero : Constant
--   suc : Constant → Constant

data Monomial (n : ℕ) : Set ℓ₁ where
  con : Constant → Monomial n
  -- var : (Fin n) → Monomial n
  atom : :Expr n → Monomial n
  _∗*_ : Monomial n → Monomial n → Monomial n

data SumOfMonomials (n : ℕ) : Set ℓ₁ where
  mon : Monomial n → SumOfMonomials n
  _∗+_ : SumOfMonomials n → SumOfMonomials n → SumOfMonomials n

⟦_⟧C : Constant → Expr
⟦ ∗zero ⟧C = zero
⟦ ∗suc x ⟧C = suc ⟦ x ⟧C
⟦ x ∗+ y ⟧C = ⟦ x ⟧C + ⟦ y ⟧C
⟦ x ∗* y ⟧C = ⟦ x ⟧C * ⟦ y ⟧C

⟦_⟧M : ∀ {n} → Monomial n → Vec Expr n → Expr
⟦ atom x ⟧M ρ = semantics x ρ
⟦ con x ⟧M ρ = ⟦ x ⟧C
-- ⟦ var x ⟧M ρ = lookup x ρ
⟦ x ∗* y ⟧M ρ = ⟦ x ⟧M ρ * ⟦ y ⟧M ρ

⟦_⟧SM : ∀ {n} → SumOfMonomials n → Vec Expr n → Expr
⟦ mon x ⟧SM ρ = ⟦ x ⟧M ρ
⟦ x ∗+ y ⟧SM ρ = ⟦ x ⟧SM ρ + ⟦ y ⟧SM ρ

*-expand : ∀ {n} → SumOfMonomials n -> SumOfMonomials n → SumOfMonomials n
*-expand (mon l) (mon r) = mon (l ∗* r)
*-expand (mon l) (r₁ ∗+ r₂) = *-expand (mon l) r₁ ∗+ *-expand (mon l) r₂
*-expand (l₁ ∗+ l₂) (mon r) = *-expand l₁ (mon r) ∗+ *-expand l₂ (mon r)
*-expand (l₁ ∗+ l₂) (r₁ ∗+ r₂) = *-expand l₁ r₁ ∗+ *-expand l₁ r₂ ∗+ *-expand l₂ r₁ ∗+ *-expand l₂ r₂

*-expand-correct : ∀ {n} ρ → (p : SumOfMonomials n) → (q : SumOfMonomials n) → ⟦ p ⟧SM ρ * ⟦ q ⟧SM ρ ≡ ⟦ *-expand p q ⟧SM ρ
*-expand-correct ρ (mon l) (mon r) = refl
*-expand-correct ρ (mon l) (r₁ ∗+ r₂) =
  begin
    ⟦ l ⟧M ρ * (⟦ r₁ ⟧SM ρ + ⟦ r₂ ⟧SM ρ)
  ≈⟨ *-comm ⟩
    (⟦ r₁ ⟧SM ρ + ⟦ r₂ ⟧SM ρ) * ⟦ l ⟧M ρ
  ≈⟨ distribʳ-*-+ ⟩
    (⟦ r₁ ⟧SM ρ) * (⟦ l ⟧M ρ) + (⟦ r₂ ⟧SM ρ) * (⟦ l ⟧M ρ)
  ≈⟨ +-cong *-comm *-comm ⟩
    (⟦ l ⟧M ρ) * (⟦ r₁ ⟧SM ρ) + (⟦ l ⟧M ρ) * (⟦ r₂ ⟧SM ρ)
  ≡⟨⟩
    (⟦ mon l ⟧SM ρ) * (⟦ r₁ ⟧SM ρ) + (⟦ mon l ⟧SM ρ) * (⟦ r₂ ⟧SM ρ)
  ≈⟨ +-cong (*-expand-correct ρ (mon l) r₁) (*-expand-correct ρ (mon l) r₂) ⟩
    (⟦ *-expand (mon l) r₁ ⟧SM ρ) + (⟦ *-expand (mon l) r₂ ⟧SM ρ)
  ∎
*-expand-correct ρ (l₁ ∗+ l₂) (mon r) =
  begin
    (⟦ l₁ ⟧SM ρ + ⟦ l₂ ⟧SM ρ) * ⟦ r ⟧M ρ
  ≈⟨ distribʳ-*-+ ⟩
    ⟦ l₁ ⟧SM ρ * ⟦ r ⟧M ρ + ⟦ l₂ ⟧SM ρ * ⟦ r ⟧M ρ
  ≡⟨⟩
    ⟦ l₁ ⟧SM ρ * ⟦ mon r ⟧SM ρ + ⟦ l₂ ⟧SM ρ * ⟦ mon r ⟧SM ρ
  ≈⟨ +-cong (*-expand-correct ρ l₁ (mon r)) (*-expand-correct ρ l₂ (mon r)) ⟩
    (⟦ *-expand l₁ (mon r) ⟧SM ρ) + (⟦ *-expand l₂ (mon r) ⟧SM ρ)
  ∎
*-expand-correct ρ (l₁ ∗+ l₂) (r₁ ∗+ r₂) =
  begin
    (⟦ l₁ ⟧SM ρ + ⟦ l₂ ⟧SM ρ) * (⟦ r₁ ⟧SM ρ + ⟦ r₂ ⟧SM ρ)
  ≈⟨ distribʳ-*-+ ⟩
    ⟦ l₁ ⟧SM ρ * (⟦ r₁ ⟧SM ρ + ⟦ r₂ ⟧SM ρ) + ⟦ l₂ ⟧SM ρ * (⟦ r₁ ⟧SM ρ + ⟦ r₂ ⟧SM ρ)
  ≈⟨ +-cong distribˡ-*-+ distribˡ-*-+ ⟩
    (⟦ l₁ ⟧SM ρ * ⟦ r₁ ⟧SM ρ + ⟦ l₁ ⟧SM ρ * ⟦ r₂ ⟧SM ρ) + (⟦ l₂ ⟧SM ρ * ⟦ r₁ ⟧SM ρ + ⟦ l₂ ⟧SM ρ * ⟦ r₂ ⟧SM ρ)
  ≈⟨ +-cong (+-cong (*-expand-correct ρ l₁ r₁) (*-expand-correct ρ l₁ r₂)) (+-cong (*-expand-correct ρ l₂ r₁) (*-expand-correct ρ l₂ r₂)) ⟩
    (⟦ *-expand l₁ r₁ ⟧SM ρ + ⟦ *-expand l₁ r₂ ⟧SM ρ) + (⟦ *-expand l₂ r₁ ⟧SM ρ + ⟦ *-expand l₂ r₂ ⟧SM ρ)
  ≈⟨ sym (+-assoc ) ⟩ -- (⟦ *-expand l₁ r₁ ⟧SM ρ + ⟦ *-expand l₁ r₂ ⟧SM ρ) (⟦ *-expand l₂ r₁ ⟧SM ρ) (⟦ *-expand l₂ r₂ ⟧SM ρ)
    ((⟦ *-expand l₁ r₁ ⟧SM ρ + ⟦ *-expand l₁ r₂ ⟧SM ρ) + ⟦ *-expand l₂ r₁ ⟧SM ρ) + ⟦ *-expand l₂ r₂ ⟧SM ρ
  ∎

-- TODO: Make sure this is correct
expand : ∀ {n} → Polynomial n → SumOfMonomials n
expand (∗atom x) = mon (atom x)
-- expand (∗var x) = mon (var x)
expand ∗zero = mon (con ∗zero)
expand (∗suc x) = mon (con (∗suc ∗zero)) ∗+ expand x
expand (l ∗+ r) = expand l ∗+ expand r
expand (l ∗* r) = *-expand (expand l) (expand r)

-- expand (con x) = mon (con x)
-- expand (var x) = mon (var x)
-- expand (l ∗+ r) = expand l ∗+ expand r
-- expand (l ∗* r) = *-expand (expand l) (expand r)

expand-correct : ∀ {n} → (ρ : Vec Expr n) → (p : Polynomial n) → ⟦ p ⟧ ρ ≡ ⟦ expand p ⟧SM ρ
expand-correct ρ (∗atom x) = refl
-- expand-correct ρ (∗var x) = refl
expand-correct ρ ∗zero = refl
expand-correct ρ (∗suc x) =
  begin
    suc (⟦ x ⟧ ρ)
  ≈⟨ suc-expand ⟩
    suc zero + (⟦ x ⟧ ρ)
  ≈⟨ +-cong refl (expand-correct ρ x) ⟩
    suc zero + ⟦ expand x ⟧SM ρ
  ∎
expand-correct ρ (l ∗+ r) = +-cong (expand-correct ρ l) (expand-correct ρ r)
expand-correct ρ (l ∗* r) =
  begin
    ⟦ l ⟧ ρ * ⟦ r ⟧ ρ
  ≈⟨ *-cong (expand-correct ρ l) (expand-correct ρ r) ⟩
    ⟦ expand l ⟧SM ρ * ⟦ expand r ⟧SM ρ
  ≈⟨ *-expand-correct ρ (expand l) (expand r) ⟩
    ⟦ *-expand (expand l) (expand r) ⟧SM ρ
  ∎
-- expand-correct ρ (con x) = refl
-- expand-correct ρ (var x) = refl
-- expand-correct ρ (p ∗+ p₁) = +-cong (expand-correct ρ p) (expand-correct ρ p₁)
-- expand-correct ρ (p ∗* p₁) =
--   begin
--     ⟦ p ⟧ ρ * ⟦ p₁ ⟧ ρ
--   ≡⟨ *-cong (expand-correct ρ p) (expand-correct ρ p₁) ⟩
--     ⟦ expand p ⟧SM ρ * ⟦ expand p₁ ⟧SM ρ
--   ≡⟨ *-expand-correct ρ (expand p) (expand p₁) ⟩
--     ⟦ *-expand (expand p) (expand p₁) ⟧SM ρ
--   ∎

------------------------------------------------------------------------
-- Right leaning

data RightLeaningSumOfMonomials (n : ℕ) : Set ℓ₁ where
  nil : RightLeaningSumOfMonomials n
  _∗+_ : Monomial n → RightLeaningSumOfMonomials n → RightLeaningSumOfMonomials n

⟦_⟧RLSM : ∀ {n} → RightLeaningSumOfMonomials n → Vec Expr n → Expr
⟦ nil ⟧RLSM ρ = zero
⟦ l ∗+ r ⟧RLSM ρ = ⟦ l ⟧M ρ + ⟦ r ⟧RLSM ρ

combine-lean-right : ∀ {n} → RightLeaningSumOfMonomials n → RightLeaningSumOfMonomials n → RightLeaningSumOfMonomials n
combine-lean-right nil r = r
combine-lean-right (x ∗+ l) r = x ∗+ (combine-lean-right l r)

combine-lean-right-correct : ∀ {n} → (ρ : Vec Expr n) → (p q : RightLeaningSumOfMonomials n) → ⟦ p ⟧RLSM ρ + ⟦ q ⟧RLSM ρ ≡ ⟦ combine-lean-right p q ⟧RLSM ρ
combine-lean-right-correct ρ nil r = trans +-comm +-right-identity
combine-lean-right-correct ρ (x ∗+ l) r =
  begin
    (⟦ x ⟧M ρ + ⟦ l ⟧RLSM ρ) + ⟦ r ⟧RLSM ρ
  ≈⟨ +-assoc ⟩
    ⟦ x ⟧M ρ + (⟦ l ⟧RLSM ρ + ⟦ r ⟧RLSM ρ)
  ≈⟨ +-cong refl (combine-lean-right-correct ρ l r) ⟩
    ⟦ x ⟧M ρ + ⟦ combine-lean-right l r ⟧RLSM ρ
  ∎

lean-right : ∀ {n} → SumOfMonomials n → RightLeaningSumOfMonomials n
lean-right (mon x) = x ∗+ nil
lean-right (mon x ∗+ r) = x ∗+ lean-right r
lean-right ((l₁ ∗+ l₂) ∗+ r) = combine-lean-right (lean-right l₁) (lean-right (l₂ ∗+ r))

lean-right-correct : ∀ {n} → (ρ : Vec Expr n) → (p : SumOfMonomials n) → ⟦ p ⟧SM ρ ≡ ⟦ lean-right p ⟧RLSM ρ
lean-right-correct ρ (mon x) = sym +-right-identity
lean-right-correct ρ (mon x ∗+ r) = +-cong refl (lean-right-correct ρ r)
lean-right-correct ρ ((l₁ ∗+ l₂) ∗+ r) =
  begin
    (⟦ l₁ ⟧SM ρ + ⟦ l₂ ⟧SM ρ) + ⟦ r ⟧SM ρ
  ≈⟨ +-assoc ⟩
    ⟦ l₁ ⟧SM ρ + (⟦ l₂ ⟧SM ρ + ⟦ r ⟧SM ρ)
  ≡⟨⟩
    ⟦ l₁ ⟧SM ρ + (⟦ l₂ ∗+ r ⟧SM ρ)
  ≈⟨ +-cong (lean-right-correct ρ l₁) (lean-right-correct ρ (l₂ ∗+ r)) ⟩
    ⟦ lean-right l₁ ⟧RLSM ρ + ⟦ lean-right (l₂ ∗+ r) ⟧RLSM ρ
  ≈⟨ combine-lean-right-correct ρ (lean-right l₁) (lean-right (l₂ ∗+ r)) ⟩
    ⟦ combine-lean-right (lean-right l₁) (lean-right (l₂ ∗+ r)) ⟧RLSM ρ
  ∎

------------------------------------------------------------------------
-- Monomial normalization

-- VarProduct : ℕ → Set
-- VarProduct n = Vec ℕ n

-- ⟦_⟧VP_ : ∀ {n} → VarProduct n → Vec Expr n → Expr
-- ⟦ [] ⟧VP ρ = suc zero
-- ⟦ ℕzero ∷ xs ⟧VP (ρ₁ ∷ ρ) = ⟦ xs ⟧VP ρ
-- ⟦ ℕsuc x ∷ xs ⟧VP (ρ₁ ∷ ρ) = ρ₁ * ⟦ x ∷ xs ⟧VP (ρ₁ ∷ ρ)

-- varProduct-none : ∀ {n} → VarProduct n
-- varProduct-none {n} = replicate 0

-- varProduct-none-correct : ∀ {n} → (ρ : Vec Expr n) → ⟦ varProduct-none {n} ⟧VP ρ ≡ suc zero
-- varProduct-none-correct {ℕzero} ρ = refl
-- varProduct-none-correct {ℕsuc n} (ρ₁ ∷ ρ) = varProduct-none-correct ρ

-- varProduct-one : ∀ {n} → Fin n → VarProduct n
-- varProduct-one Fin.zero = 1 ∷ varProduct-none
-- varProduct-one (Fin.suc i) = 0 ∷ varProduct-one i

-- varProduct-one-correct : ∀ {n} → (ρ : Vec Expr n) → (f : Fin n) → ⟦ varProduct-one {n} f ⟧VP ρ ≡ lookup f ρ
-- varProduct-one-correct {ℕsuc n} (ρ₁ ∷ ρ) Fin.zero =
--   begin
--     ⟦ varProduct-one {ℕsuc n} Fin.zero ⟧VP (ρ₁ ∷ ρ)
--   ≡⟨⟩
--     ⟦ 1 ∷ varProduct-none ⟧VP (ρ₁ ∷ ρ)
--   ≡⟨⟩
--     ρ₁ * ⟦ varProduct-none {n} ⟧VP ρ
--   ≈⟨ *-cong refl (varProduct-none-correct ρ) ⟩
--     ρ₁ * (suc zero)
--   ≈⟨ *-right-identity ⟩
--     lookup Fin.zero (ρ₁ ∷ ρ)
--   ∎
-- varProduct-one-correct (ρ₁ ∷ ρ) (Fin.suc f) = varProduct-one-correct ρ f

-- varProduct-mul : ∀ {n} → VarProduct n → VarProduct n → VarProduct n
-- varProduct-mul [] [] = []
-- varProduct-mul (x ∷ l) (x₁ ∷ r) = (x ℕ+ x₁) ∷ varProduct-mul l r

-- varProduct-mul-correct : ∀ {n} → (ρ : Vec Expr n) → (l : VarProduct n) → (r : VarProduct n) → ⟦ l ⟧VP ρ * ⟦ r ⟧VP ρ ≡ ⟦ varProduct-mul l r ⟧VP ρ
-- varProduct-mul-correct ρ [] [] = trans *-comm *-right-identity
-- varProduct-mul-correct (ρ ∷ ρ₁) (ℕzero ∷ l) (ℕzero ∷ r) = varProduct-mul-correct ρ₁ l r
-- varProduct-mul-correct (ρ ∷ ρ₁) (ℕzero ∷ l) (ℕsuc x ∷ r) =
--   begin
--     ⟦ ℕzero ∷ l ⟧VP (ρ ∷ ρ₁) * ⟦ ℕsuc x ∷ r ⟧VP (ρ ∷ ρ₁)
--   ≡⟨⟩
--     ⟦ ℕzero ∷ l ⟧VP (ρ ∷ ρ₁) * (ρ * ⟦ x ∷ r ⟧VP (ρ ∷ ρ₁))
--   ≈⟨ *-cong refl *-comm ⟩
--     ⟦ ℕzero ∷ l ⟧VP (ρ ∷ ρ₁) * (⟦ x ∷ r ⟧VP (ρ ∷ ρ₁) * ρ)
--   ≈⟨ sym *-assoc ⟩
--     (⟦ ℕzero ∷ l ⟧VP (ρ ∷ ρ₁) * ⟦ x ∷ r ⟧VP (ρ ∷ ρ₁)) * ρ
--   ≈⟨ *-comm ⟩
--     ρ * (⟦ ℕzero ∷ l ⟧VP (ρ ∷ ρ₁) * ⟦ x ∷ r ⟧VP (ρ ∷ ρ₁))
--   ≈⟨ *-cong refl (varProduct-mul-correct (ρ ∷ ρ₁) (ℕzero ∷ l) (x ∷ r)) ⟩
--     ρ * ⟦ varProduct-mul (ℕzero ∷ l) (x ∷ r) ⟧VP (ρ ∷ ρ₁)
--   ≡⟨⟩
--     ρ * ⟦ (ℕzero ℕ+ x) ∷ varProduct-mul l r ⟧VP (ρ ∷ ρ₁)
--   ≡⟨⟩
--     ρ * ⟦ x ∷ varProduct-mul l r ⟧VP (ρ ∷ ρ₁)
--   ≡⟨⟩
--     ⟦ (ℕsuc x) ∷ varProduct-mul l r ⟧VP (ρ ∷ ρ₁)
--   ≡⟨⟩
--     ⟦ (ℕzero ℕ+ ℕsuc x) ∷ varProduct-mul l r ⟧VP (ρ ∷ ρ₁)
--   ≡⟨⟩
--     ⟦ varProduct-mul (ℕzero ∷ l) (ℕsuc x ∷ r) ⟧VP (ρ ∷ ρ₁)
--   ∎
-- varProduct-mul-correct (ρ ∷ ρ₁) (ℕsuc x ∷ l) (x₁ ∷ r) =
--   begin
--     ⟦ (ℕsuc x ∷ l) ⟧VP (ρ ∷ ρ₁) * ⟦ x₁ ∷ r ⟧VP (ρ ∷ ρ₁)
--   ≡⟨⟩
--     (ρ * ⟦ (x ∷ l) ⟧VP (ρ ∷ ρ₁)) * ⟦ x₁ ∷ r ⟧VP (ρ ∷ ρ₁)
--   ≈⟨ *-assoc ⟩
--     ρ * (⟦ (x ∷ l) ⟧VP (ρ ∷ ρ₁) * ⟦ x₁ ∷ r ⟧VP (ρ ∷ ρ₁))
--   ≈⟨ *-cong refl (varProduct-mul-correct (ρ ∷ ρ₁) (x ∷ l) (x₁ ∷ r)) ⟩
--     ρ * ⟦ varProduct-mul (x ∷ l) (x₁ ∷ r) ⟧VP (ρ ∷ ρ₁)
--   ≡⟨⟩
--     ρ * ⟦ (x ℕ+ x₁) ∷ varProduct-mul l r ⟧VP (ρ ∷ ρ₁)
--   ≡⟨⟩
--     ⟦ (ℕsuc (x ℕ+ x₁)) ∷ varProduct-mul l r ⟧VP (ρ ∷ ρ₁)
--   ≡⟨⟩
--     ⟦ (ℕsuc x ℕ+ x₁) ∷ varProduct-mul l r ⟧VP (ρ ∷ ρ₁)
--   ≡⟨⟩
--     ⟦ varProduct-mul (ℕsuc x ∷ l) (x₁ ∷ r) ⟧VP (ρ ∷ ρ₁)
--   ∎


data SemiNormalizedMonomial (n : ℕ) : Set ℓ₁ where
  con : Constant → SemiNormalizedMonomial n
  _∗*_ : :Expr n → SemiNormalizedMonomial n → SemiNormalizedMonomial n

⟦_⟧SNM : ∀ {n} → SemiNormalizedMonomial n → Vec Expr n → Expr
⟦ con x ⟧SNM ρ = ⟦ x ⟧C
⟦ l ∗* r ⟧SNM ρ = (semantics l ρ) * ⟦ r ⟧SNM ρ

-- data NormalizedMonomial : ℕ → Set ℓ₁ where
--   _∗*_ : ∀ {n} → Constant → VarProduct n → NormalizedMonomial n

-- ⟦_⟧NM : ∀ {n} → NormalizedMonomial n → Vec Expr n → Expr
-- ⟦ x ∗* x₁ ⟧NM ρ = ⟦ x ⟧C * ⟦ x₁ ⟧VP ρ

-- combine-normalized-monomial : ∀ {n} → NormalizedMonomial n → NormalizedMonomial n → NormalizedMonomial n
-- combine-normalized-monomial (cₗ ∗* xₗ) (cᵣ ∗* xᵣ) = (cₗ ∗* cᵣ) ∗* (varProduct-mul xₗ xᵣ) -- XXX: How can we normalize cₗ * cᵣ???

-- combine-normalized-monomial-correct : ∀ {n} (ρ : Vec Expr n) → (p : NormalizedMonomial n) → (q : NormalizedMonomial n) → ⟦ p ⟧NM ρ * ⟦ q ⟧NM ρ ≡ ⟦ combine-normalized-monomial p q ⟧NM ρ
-- combine-normalized-monomial-correct ρ (x ∗* x₁) (x₂ ∗* x₃) = ?
--   -- begin
--   --   (⟦ x ⟧C * ⟦ x₁ ⟧VP ρ) * (⟦ x₂ ⟧C * (⟦ x₃ ⟧VP ρ))
--   -- ≈⟨ *-assoc ⟩
--   --   ⟦ x ⟧C * (⟦ x₁ ⟧VP ρ * (⟦ x₂ ⟧C * (⟦ x₃ ⟧VP ρ)))
--   -- ≈⟨ *-cong refl (sym *-assoc) ⟩
--   --   ⟦ x ⟧C * ((⟦ x₁ ⟧VP ρ * ⟦ x₂ ⟧C) * (⟦ x₃ ⟧VP ρ))
--   -- ≈⟨ *-cong refl (*-cong *-comm refl) ⟩
--   --   ⟦ x ⟧C * ((⟦ x₂ ⟧C * ⟦ x₁ ⟧VP ρ) * (⟦ x₃ ⟧VP ρ))
--   -- ≈⟨ sym *-assoc ⟩
--   --   (⟦ x ⟧C * (⟦ x₂ ⟧C * ⟦ x₁ ⟧VP ρ)) * (⟦ x₃ ⟧VP ρ)
--   -- ≈⟨ *-cong (sym *-assoc) refl ⟩
--   --   ((⟦ x ⟧C * ⟦ x₂ ⟧C) * ⟦ x₁ ⟧VP ρ) * (⟦ x₃ ⟧VP ρ)
--   -- ≈⟨ *-assoc ⟩
--   --   (⟦ x ⟧C * ⟦ x₂ ⟧C) * (⟦ x₁ ⟧VP ρ * ⟦ x₃ ⟧VP ρ)
--   -- ≈⟨ *-cong refl (varProduct-mul-correct ρ x₁ x₃) ⟩
--   --   (⟦ x ⟧C * ⟦ x₂ ⟧C) * (⟦ varProduct-mul x₁ x₃ ⟧VP ρ)
--   -- ∎

combine-normalized-monomial : ∀ {n} → SemiNormalizedMonomial n → SemiNormalizedMonomial n → SemiNormalizedMonomial n
combine-normalized-monomial (con x) (con x₁) = con (x ∗* x₁)
combine-normalized-monomial (con x) (x₁ ∗* r) = x₁ ∗* combine-normalized-monomial (con x) r
combine-normalized-monomial (x ∗* l) r = x ∗* combine-normalized-monomial l r

combine-normalized-monomial-correct : ∀ {n} → (ρ : Vec Expr n) → (p q : SemiNormalizedMonomial n) → ⟦ p ⟧SNM ρ * ⟦ q ⟧SNM ρ ≡ ⟦ combine-normalized-monomial p q ⟧SNM ρ
combine-normalized-monomial-correct ρ (con x) (con x₁) = refl
combine-normalized-monomial-correct ρ (con x) (x₁ ∗* r) =
  begin
    ⟦ x ⟧C * (semantics x₁ ρ * ⟦ r ⟧SNM ρ)
  ≈⟨ sym *-assoc ⟩
    (⟦ x ⟧C * semantics x₁ ρ) * ⟦ r ⟧SNM ρ
  ≈⟨ *-cong *-comm refl ⟩
    (semantics x₁ ρ * ⟦ x ⟧C) * ⟦ r ⟧SNM ρ
  ≈⟨ *-assoc ⟩
    semantics x₁ ρ * (⟦ x ⟧C * ⟦ r ⟧SNM ρ)
  ≈⟨ *-cong refl (combine-normalized-monomial-correct ρ (con x) r) ⟩
    semantics x₁ ρ * ⟦ combine-normalized-monomial (con x) r ⟧SNM ρ
  ∎
combine-normalized-monomial-correct ρ (x ∗* l) r =
  begin
    semantics x ρ * ⟦ l ⟧SNM ρ * ⟦ r ⟧SNM ρ
  ≈⟨ *-assoc ⟩
    semantics x ρ * (⟦ l ⟧SNM ρ * ⟦ r ⟧SNM ρ)
  ≈⟨ *-cong refl (combine-normalized-monomial-correct ρ l r) ⟩
    semantics x ρ * ⟦ combine-normalized-monomial l r ⟧SNM ρ
  ∎

normalize-monomial : ∀ {n} → Monomial n → SemiNormalizedMonomial n
normalize-monomial (con x) = con x
-- normalize-monomial (var x) = {!!}
normalize-monomial (atom x) = x ∗* con (∗suc ∗zero)
normalize-monomial (l ∗* r) = combine-normalized-monomial (normalize-monomial l) (normalize-monomial r)

normalize-monomial-correct : ∀ {n} → (ρ : Vec Expr n) → (p : Monomial n) → ⟦ p ⟧M ρ ≡ ⟦ normalize-monomial p ⟧SNM ρ
normalize-monomial-correct ρ (con x) = refl
normalize-monomial-correct ρ (atom x) = sym (*-right-identity)
normalize-monomial-correct ρ (x ∗* x₁) =
  begin
    ⟦ x ⟧M ρ * ⟦ x₁ ⟧M ρ
  ≈⟨ *-cong (normalize-monomial-correct ρ x) (normalize-monomial-correct ρ x₁) ⟩
    ⟦ normalize-monomial x ⟧SNM ρ * ⟦ normalize-monomial x₁ ⟧SNM ρ
  ≈⟨ combine-normalized-monomial-correct ρ (normalize-monomial x) (normalize-monomial x₁) ⟩
    ⟦ combine-normalized-monomial (normalize-monomial x) (normalize-monomial x₁) ⟧SNM ρ
  ∎

insert-normalized-monomial : ∀ {n} → :Expr n → SemiNormalizedMonomial n → SemiNormalizedMonomial n
insert-normalized-monomial x (con x₁) = x ∗* (con x₁)
insert-normalized-monomial x (x₁ ∗* xs) with termLt (quoteTerm x) (quoteTerm x₁)
insert-normalized-monomial x (x₁ ∗* xs) | true = x ∗* (x₁ ∗* xs)
insert-normalized-monomial x (x₁ ∗* xs) | false = x₁ ∗* insert-normalized-monomial x xs

insert-normalized-monomial-correct : ∀ {n} → (ρ : Vec Expr n) → (p : :Expr n) → (q : SemiNormalizedMonomial n) → (semantics p ρ) * ⟦ q ⟧SNM ρ ≡ ⟦ insert-normalized-monomial p q ⟧SNM ρ
insert-normalized-monomial-correct ρ p (con x) = refl
insert-normalized-monomial-correct ρ p (x ∗* q) =
  begin
    semantics p ρ * (semantics x ρ * ⟦ q ⟧SNM ρ)
  ≈⟨ sym *-assoc ⟩
    (semantics p ρ * semantics x ρ) * ⟦ q ⟧SNM ρ
  ≈⟨ *-cong *-comm refl ⟩
    (semantics x ρ * semantics p ρ) * ⟦ q ⟧SNM ρ
  ≈⟨ *-assoc ⟩
    semantics x ρ * (semantics p ρ * ⟦ q ⟧SNM ρ)
  ≈⟨ *-cong refl (insert-normalized-monomial-correct ρ p q) ⟩
    semantics x ρ * ⟦ insert-normalized-monomial p q ⟧SNM ρ
  ∎

sort-normalized-monomial : ∀ {n} → SemiNormalizedMonomial n → SemiNormalizedMonomial n
sort-normalized-monomial (con x) = con x
sort-normalized-monomial (x ∗* x₁) = insert-normalized-monomial x (sort-normalized-monomial x₁)

sort-normalized-monomial-correct : ∀ {n} → (ρ : Vec Expr n) → (p : SemiNormalizedMonomial n) → ⟦ p ⟧SNM ρ ≡ ⟦ sort-normalized-monomial p ⟧SNM ρ
sort-normalized-monomial-correct ρ (con x) = refl
sort-normalized-monomial-correct ρ (x ∗* x₁) =
  begin
    semantics x ρ * ⟦ x₁ ⟧SNM ρ
  ≈⟨ *-cong refl (sort-normalized-monomial-correct ρ x₁) ⟩
    semantics x ρ * ⟦ sort-normalized-monomial x₁ ⟧SNM ρ
  ≈⟨ insert-normalized-monomial-correct ρ x (sort-normalized-monomial x₁) ⟩
    ⟦ insert-normalized-monomial x (sort-normalized-monomial x₁) ⟧SNM ρ
  ∎

-- squash-normalized-monomial : ∀ {n} → NormalizedMonomial n → NormalizedMonomial n
-- squash-normalized-monomial (con x) = con x
-- squash-normalized-monomial (x ∗* con x₁) = x ∗* con x₁
-- squash-normalized-monomial (x ∗* (x₁ ∗* xs)) with termEq (quoteTerm x) (quoteTerm x₁)
-- ... | 

-- normalize-monomial : ∀ {n} → Monomial n → NormalizedMonomial n
-- normalize-monomial (atom x) = ? -- x ∗* varProduct-none
-- normalize-monomial (con x) = x ∗* varProduct-none
-- normalize-monomial (var x) = (∗suc ∗zero) ∗* varProduct-one x
-- normalize-monomial (l ∗* r) = combine-normalized-monomial (normalize-monomial l) (normalize-monomial r)

-- normalize-monomial-correct : ∀ {n} → (ρ : Vec Expr n) → (p : Monomial n) → ⟦ p ⟧M ρ ≡ ⟦ normalize-monomial p ⟧NM ρ
-- normalize-monomial-correct {n} ρ (atom x) = ?
-- normalize-monomial-correct {n} ρ (con x) = ?
--   -- begin
--   --   x
--   -- ≈⟨ sym *-right-identity ⟩
--   --   x * (suc zero)
--   -- ≈⟨ *-cong refl (sym (varProduct-none-correct {n} ρ)) ⟩
--   --   x * ⟦ varProduct-none {n} ⟧VP ρ
--   -- ∎
-- normalize-monomial-correct ρ (var x) = ?
--   -- begin
--   --   lookup x ρ
--   -- ≈⟨ sym (trans *-comm *-right-identity) ⟩
--   --   (suc zero) * lookup x ρ
--   -- ≈⟨ *-cong refl (sym (varProduct-one-correct ρ x)) ⟩
--   --   (suc zero) * (⟦ varProduct-one x ⟧VP ρ)
--   -- ∎
-- normalize-monomial-correct ρ (l ∗* r) =
--   begin
--     ⟦ l ⟧M ρ * ⟦ r ⟧M ρ
--   ≈⟨ *-cong (normalize-monomial-correct ρ l) (normalize-monomial-correct ρ r) ⟩
--     ⟦ normalize-monomial l ⟧NM ρ * ⟦ normalize-monomial r ⟧NM ρ
--   ≈⟨ combine-normalized-monomial-correct ρ (normalize-monomial l) (normalize-monomial r) ⟩
--     ⟦ combine-normalized-monomial (normalize-monomial l) (normalize-monomial r) ⟧NM ρ
--   ∎

------------------------------------------------------------------------
-- Normalize constants

data NormalizedConstant : Set where
  ∗zero : NormalizedConstant
  ∗suc : NormalizedConstant → NormalizedConstant

⟦_⟧NC : NormalizedConstant → Expr
⟦ ∗zero ⟧NC = zero
⟦ ∗suc x ⟧NC = suc ⟦ x ⟧NC

_C+_ : NormalizedConstant → NormalizedConstant → NormalizedConstant
_C+_ ∗zero y = y
_C+_ (∗suc x) y = ∗suc (x C+ y)

C+-correct : (p q : NormalizedConstant) → ⟦ p ⟧NC + ⟦ q ⟧NC ≡ ⟦ p C+ q ⟧NC
C+-correct ∗zero q =
  begin
    zero + ⟦ q ⟧NC
  ≈⟨ +-comm ⟩
    ⟦ q ⟧NC + zero
  ≈⟨ +-right-identity ⟩
    ⟦ q ⟧NC
  ∎
C+-correct (∗suc p) q =
  begin
    suc ⟦ p ⟧NC + ⟦ q ⟧NC
  ≈⟨ suc-pull ⟩
    suc (⟦ p ⟧NC + ⟦ q ⟧NC)
  ≈⟨ suc-cong (C+-correct p q) ⟩
    suc ⟦ p C+ q ⟧NC
  ∎

_C*_ : NormalizedConstant → NormalizedConstant → NormalizedConstant
∗zero C* y = ∗zero
∗suc x C* y = y C+ x C* y

C*-correct : (p q : NormalizedConstant) → ⟦ p ⟧NC * ⟦ q ⟧NC ≡ ⟦ p C* q ⟧NC
C*-correct ∗zero y =
  begin
    zero * ⟦ y ⟧NC
  ≈⟨ *-comm ⟩
    ⟦ y ⟧NC * zero
  ≈⟨ *-right-zero ⟩
    zero
  ∎
C*-correct (∗suc x) y =
  begin
    suc ⟦ x ⟧NC * ⟦ y ⟧NC
  ≈⟨ suc-* ⟩
    ⟦ y ⟧NC + ⟦ x ⟧NC * ⟦ y ⟧NC
  ≈⟨ +-cong refl (C*-correct x y) ⟩
    ⟦ y ⟧NC + ⟦ x C* y ⟧NC
  ≈⟨ C+-correct y (x C* y) ⟩
    ⟦ y C+ x C* y ⟧NC
  ∎

data NormalizedMonomial (n : ℕ) : Set ℓ₁ where
  con : NormalizedConstant → NormalizedMonomial n
  _∗*_ : :Expr n → NormalizedMonomial n → NormalizedMonomial n

⟦_⟧NM : ∀ {n} → NormalizedMonomial n → Vec Expr n → Expr
⟦ con x ⟧NM ρ = ⟦ x ⟧NC
⟦ l ∗* r ⟧NM ρ = (semantics l ρ) * ⟦ r ⟧NM ρ

normalize-constant : Constant → NormalizedConstant
normalize-constant ∗zero = ∗zero
normalize-constant (∗suc x) = ∗suc (normalize-constant x)
normalize-constant (x ∗+ x₁) = (normalize-constant x) C+ (normalize-constant x₁)
normalize-constant (x ∗* x₁) = (normalize-constant x) C* (normalize-constant x₁)

normalize-constant-correct : (p : Constant) → ⟦ p ⟧C ≡ ⟦ normalize-constant p ⟧NC
normalize-constant-correct ∗zero = refl
normalize-constant-correct (∗suc p) = suc-cong (normalize-constant-correct p)
normalize-constant-correct (p ∗+ p₁) =
  begin
    ⟦ p ⟧C + ⟦ p₁ ⟧C
  ≈⟨ +-cong (normalize-constant-correct p) (normalize-constant-correct p₁) ⟩
    ⟦ normalize-constant p ⟧NC + ⟦ normalize-constant p₁ ⟧NC
  ≈⟨ C+-correct (normalize-constant p) (normalize-constant p₁) ⟩
    ⟦ normalize-constant p C+ normalize-constant p₁ ⟧NC
  ∎
normalize-constant-correct (p ∗* p₁) =
  begin
    ⟦ p ⟧C * ⟦ p₁ ⟧C
  ≈⟨ *-cong (normalize-constant-correct p) (normalize-constant-correct p₁) ⟩
    ⟦ normalize-constant p ⟧NC * ⟦ normalize-constant p₁ ⟧NC
  ≈⟨ C*-correct (normalize-constant p) (normalize-constant p₁) ⟩
    ⟦ normalize-constant p C* normalize-constant p₁ ⟧NC
  ∎

normalize-constants : ∀ {n} → SemiNormalizedMonomial n → NormalizedMonomial n
normalize-constants (con x) = con (normalize-constant x)
normalize-constants (x ∗* xs) = x ∗* (normalize-constants xs)

normalize-constants-correct : ∀ {n} → (ρ : Vec Expr n) → (p : SemiNormalizedMonomial n) → ⟦ p ⟧SNM ρ ≡ ⟦ normalize-constants p ⟧NM ρ
normalize-constants-correct ρ (con x) = normalize-constant-correct x
normalize-constants-correct ρ (x ∗* p) = *-cong refl (normalize-constants-correct ρ p)

data RightLeaningSumOfNormalizedMonomials : (n : ℕ) → Set ℓ₁ where
  nil : ∀ {n} → RightLeaningSumOfNormalizedMonomials n
  _∗+_ : ∀ {n} → NormalizedMonomial n → RightLeaningSumOfNormalizedMonomials n → RightLeaningSumOfNormalizedMonomials n

⟦_⟧RLSNM : ∀ {n} → RightLeaningSumOfNormalizedMonomials n → Vec Expr n → Expr
⟦ nil ⟧RLSNM ρ = zero
⟦ x ∗+ x₁ ⟧RLSNM ρ = ⟦ x ⟧NM ρ + ⟦ x₁ ⟧RLSNM ρ

normalize-monomials : ∀ {n} → RightLeaningSumOfMonomials n → RightLeaningSumOfNormalizedMonomials n
normalize-monomials nil = nil
normalize-monomials (x ∗+ p) = normalize-constants (normalize-monomial x) ∗+ normalize-monomials p

normalize-monomials-correct : ∀ {n} → (ρ : Vec Expr n) → (p : RightLeaningSumOfMonomials n) → ⟦ p ⟧RLSM ρ ≡ ⟦ normalize-monomials p ⟧RLSNM ρ
normalize-monomials-correct ρ nil = refl
normalize-monomials-correct ρ (x ∗+ xs) =
  begin
    ⟦ x ⟧M ρ + ⟦ xs ⟧RLSM ρ
  ≈⟨ +-cong (normalize-monomial-correct ρ x) (normalize-monomials-correct ρ xs) ⟩
    ⟦ normalize-monomial x ⟧SNM ρ + ⟦ normalize-monomials xs ⟧RLSNM ρ
  ≈⟨ +-cong (normalize-constants-correct ρ (normalize-monomial x)) refl ⟩
    ⟦ normalize-constants (normalize-monomial x) ⟧NM ρ + ⟦ normalize-monomials xs ⟧RLSNM ρ
  ∎
-- +-cong (normalize-monomial-correct ρ x) (normalize-monomials-correct ρ xs)

------------------------------------------------------------------------
-- Throw out zero monomials

is-zero : ∀ {n} → (p : NormalizedMonomial n) → Maybe (∀ ρ → ⟦ p ⟧NM ρ ≡ zero)
is-zero (con ∗zero) = just (λ ρ → refl)
is-zero (con (∗suc x)) = nothing
is-zero (x ∗* p) with is-zero p
is-zero (x ∗* p) | just prf = just (λ ρ → begin
    semantics x ρ * ⟦ p ⟧NM ρ
  ≈⟨ *-cong refl (prf ρ) ⟩
    semantics x ρ * zero
  ≈⟨ *-right-zero ⟩
    zero
  ∎)
is-zero (x ∗* p) | nothing = nothing

throw-out-zeros : ∀ {n} → RightLeaningSumOfNormalizedMonomials n → RightLeaningSumOfNormalizedMonomials n
throw-out-zeros nil = nil
throw-out-zeros (x ∗+ x₁) with is-zero x
throw-out-zeros (x ∗+ x₂) | just x₁ = throw-out-zeros x₂
throw-out-zeros (x ∗+ x₁) | nothing = x ∗+ throw-out-zeros x₁

throw-out-zeros-correct : ∀ {n} → (ρ : Vec Expr n) → (p : RightLeaningSumOfNormalizedMonomials n) → ⟦ p ⟧RLSNM ρ ≡ ⟦ throw-out-zeros p ⟧RLSNM ρ
throw-out-zeros-correct ρ nil = refl
throw-out-zeros-correct ρ (x ∗+ p) with is-zero x
throw-out-zeros-correct ρ (x ∗+ p) | just prf =
  begin
    ⟦ x ∗+ p ⟧RLSNM ρ
  ≡⟨⟩
    ⟦ x ⟧NM ρ + ⟦ p ⟧RLSNM ρ
  ≈⟨ +-cong (prf ρ) refl ⟩
    zero + ⟦ p ⟧RLSNM ρ
  ≈⟨ +-comm ⟩
    ⟦ p ⟧RLSNM ρ + zero
  ≈⟨ +-right-identity ⟩
    ⟦ p ⟧RLSNM ρ
  ≈⟨ throw-out-zeros-correct ρ p ⟩
    ⟦ throw-out-zeros p ⟧RLSNM ρ
  ∎
throw-out-zeros-correct ρ (x ∗+ p) | nothing = +-cong refl (throw-out-zeros-correct ρ p)

-- mutual
--   no-zeros' : ∀ {n} → (c : Expr) → Dec (c ≡ zero) → VarProduct n → RightLeaningSumOfNormalizedMonomials n → L.List (NormalizedMonomial n)
--   no-zeros' c (yes prf) x p = no-zeros p
--   no-zeros' c (no ¬prf) x p = ? -- (c ∗* x) L.∷ no-zeros p

--   no-zeros : ∀ {n} → RightLeaningSumOfNormalizedMonomials n → L.List (NormalizedMonomial n)
--   no-zeros nil = L.[]
--   no-zeros (c ∗* x ∗+ p) = ? -- no-zeros' c (c ≟0) x p

-- to-sum : ∀ {n} → L.List (NormalizedMonomial n) → RightLeaningSumOfNormalizedMonomials n
-- to-sum L.[] = nil
-- to-sum (x L.∷ xs) = x ∗+ to-sum xs

-- throw-out-zeros : ∀ {n} → RightLeaningSumOfNormalizedMonomials n → RightLeaningSumOfNormalizedMonomials n
-- throw-out-zeros p = to-sum (no-zeros p)

-- mutual
--   throw-out-zeros-correct' : ∀ {n}
--                           → (ρ : Vec Expr n)
--                           → (c : Constant)
--                           → (d : Dec (c P≡ ∗zero))
--                           → ((c ≟0) P≡ d)
--                           → (x : VarProduct n)
--                           → (p : RightLeaningSumOfNormalizedMonomials n)
--                           → ⟦ (c ∗* x) ∗+ p ⟧RLSNM ρ ≡ ⟦ throw-out-zeros ((c ∗* x) ∗+ p) ⟧RLSNM ρ
--   throw-out-zeros-correct' ρ c (yes prf) prf2 x p rewrite prf2 =
--     begin
--       c * (⟦ x ⟧VP ρ) + ⟦ p ⟧RLSNM ρ
--     ≈⟨ +-cong (*-cong prf refl) refl ⟩
--       zero * (⟦ x ⟧VP ρ) + ⟦ p ⟧RLSNM ρ
--     ≈⟨ +-cong *-comm refl ⟩
--       (⟦ x ⟧VP ρ) * zero + ⟦ p ⟧RLSNM ρ
--     ≈⟨ +-cong *-right-zero refl ⟩
--       zero + ⟦ p ⟧RLSNM ρ
--     ≈⟨ +-comm ⟩
--       ⟦ p ⟧RLSNM ρ + zero
--     ≈⟨ +-right-identity ⟩
--       ⟦ p ⟧RLSNM ρ
--     ≈⟨ throw-out-zeros-correct ρ p ⟩
--       ⟦ to-sum (no-zeros p) ⟧RLSNM ρ
--     ∎
--   throw-out-zeros-correct' ρ c (no ¬prf) prf2 x p rewrite prf2 =
--     begin
--       c * (⟦ x ⟧VP ρ) + ⟦ p ⟧RLSNM ρ
--     ≈⟨ +-cong refl (throw-out-zeros-correct ρ p) ⟩
--       c * (⟦ x ⟧VP ρ) + ⟦ to-sum (no-zeros p) ⟧RLSNM ρ
--     ∎

--   throw-out-zeros-correct : ∀ {n} → (ρ : Vec Expr n) → (p : RightLeaningSumOfNormalizedMonomials n) → ⟦ p ⟧RLSNM ρ ≡ ⟦ throw-out-zeros p ⟧RLSNM ρ
--   throw-out-zeros-correct ρ nil = refl
--   throw-out-zeros-correct ρ (c ∗* x ∗+ p) = throw-out-zeros-correct' ρ c (c ≟0) Prefl x p

-- ------------------------------------------------------------------------
-- -- Sorting

-- infixr 6 _∧_
-- _∧_ : Bool → Bool → Bool
-- true ∧ true = true
-- _ ∧ _ = false

exprEq : ∀ {n} → :Expr n → :Expr n → Bool
exprEq a b = termEq (quoteTerm a) (quoteTerm b)

exprLt : ∀ {n} → :Expr n → :Expr n → Bool
exprLt a b = termLt (quoteTerm a) (quoteTerm b)

-- (Mostly) generated using https://github.com/SuprDewd/generate-agda-comparators

mutual

  -- normalizedConstantEq : NormalizedConstant → NormalizedConstant → Bool
  -- normalizedConstantEq ∗zero ∗zero = true
  -- normalizedConstantEq (∗suc l1) (∗suc r1) = normalizedConstantEq l1 r1
  -- normalizedConstantEq _ _ = false

  normalizedMonomialEq : ∀ {n} → NormalizedMonomial n → NormalizedMonomial n → Bool
  -- normalizedMonomialEq (con l1) (con r1) = normalizedConstantEq l1 r1
  normalizedMonomialEq (con l1) (con r1) = true -- Monomials are equal if everything but their constants are equal
  normalizedMonomialEq (_∗*_ l1 l2) (_∗*_ r1 r2) = exprEq l1 r1 Translate.Solver.Reflection.∧ normalizedMonomialEq l2 r2
  normalizedMonomialEq _ _ = false

-- isLt : ∀ {n} → Vec Bool n → Vec Bool n → Bool
-- isLt [] [] = false
-- isLt (true ∷ xs) (_ ∷ ys) = isLt xs ys
-- isLt (false ∷ xs) (y ∷ ys) = y

mutual

  -- normalizedConstantLt : NormalizedConstant → NormalizedConstant → Bool
  -- normalizedConstantLt ∗zero ∗zero = false
  -- normalizedConstantLt (∗suc l1) (∗suc r1) = isLt (normalizedConstantEq l1 r1 ∷ []) (normalizedConstantLt l1 r1 ∷ [])
  -- normalizedConstantLt ∗zero (∗suc _) = true
  -- normalizedConstantLt _ _ = false

  normalizedMonomialLt : ∀ {n} → NormalizedMonomial n → NormalizedMonomial n → Bool
  normalizedMonomialLt (con l1) (con r1) = false -- isLt (normalizedConstantEq l1 r1 ∷ []) (normalizedConstantLt l1 r1 ∷ [])
  normalizedMonomialLt (_∗*_ l1 l2) (_∗*_ r1 r2) = isLt (exprEq l1 r1 ∷ normalizedMonomialEq l2 r2 ∷ []) (exprLt l1 r1 ∷ normalizedMonomialLt l2 r2 ∷ [])
  normalizedMonomialLt (con _) (_∗*_ _ _) = true
  normalizedMonomialLt _ _ = false


-- module VarProductComparison where

--   open import Data.Vec.Properties

--   data Ordering : Set where
--     less : Ordering
--     equal : Ordering
--     greater : Ordering

--   compare : ∀ {n} → VarProduct n → VarProduct n → Ordering
--   compare [] [] = equal
--   compare (x ∷ xs) (y ∷ ys) with ℕcompare x y
--   compare (m ∷ xs) (.(ℕsuc (m ℕ+ k)) ∷ ys) | ℕless .m k = less
--   compare (m ∷ xs) (.m ∷ ys) | ℕequal .m = compare xs ys
--   compare (.(ℕsuc (m ℕ+ k)) ∷ xs) (m ∷ ys) | ℕgreater .m k = greater

--   decEq : ∀ {n} → (x : VarProduct n) → (y : VarProduct n) → Dec (x P≡ y)
--   decEq [] [] = yes Prefl
--   decEq (x ∷ xs) (y ∷ ys) with x ℕ≟ y | decEq xs ys
--   decEq (x ∷ xs) (.x ∷ ys) | yes Prefl | yes p₁ = yes (Pcong (λ t → x ∷ t) p₁)
--   decEq (x ∷ xs) (y ∷ ys) | yes p | no ¬p = no (λ t → ¬p (proj₂ (∷-injective t)))
--   decEq (x ∷ xs) (y ∷ ys) | no ¬p | _ = no (λ t → ¬p (proj₁ (∷-injective t)))



insert : ∀ {n} → NormalizedMonomial n → RightLeaningSumOfNormalizedMonomials n → RightLeaningSumOfNormalizedMonomials n
insert x nil = x ∗+ nil
insert x (x₁ ∗+ xs) with normalizedMonomialLt x x₁
insert x (x₁ ∗+ xs) | true = x ∗+ (x₁ ∗+ xs)
insert x (x₁ ∗+ xs) | false = x₁ ∗+ insert x xs

insert-correct : ∀ {n} → (ρ : Vec Expr n) → (x : NormalizedMonomial n) → (xs : RightLeaningSumOfNormalizedMonomials n) → ⟦ x ⟧NM ρ + ⟦ xs ⟧RLSNM ρ ≡ ⟦ insert x xs ⟧RLSNM ρ
insert-correct ρ x nil = refl
insert-correct ρ x (x₁ ∗+ xs) with normalizedMonomialLt x x₁
insert-correct ρ x (x₁ ∗+ xs) | true = refl
insert-correct ρ x (x₁ ∗+ xs) | false =
  begin
    ⟦ x ⟧NM ρ + (⟦ x₁ ⟧NM ρ + ⟦ xs ⟧RLSNM ρ)
  ≈⟨ sym +-assoc ⟩
    (⟦ x ⟧NM ρ + ⟦ x₁ ⟧NM ρ) + ⟦ xs ⟧RLSNM ρ
  ≈⟨ +-cong +-comm refl ⟩
    (⟦ x₁ ⟧NM ρ + ⟦ x ⟧NM ρ) + ⟦ xs ⟧RLSNM ρ
  ≈⟨ +-assoc ⟩
    ⟦ x₁ ⟧NM ρ + (⟦ x ⟧NM ρ + ⟦ xs ⟧RLSNM ρ)
  ≈⟨ +-cong refl (insert-correct ρ x xs) ⟩
    ⟦ x₁ ∗+ insert x xs ⟧RLSNM ρ
  ∎

-- insert-correct ρ y nil = refl
-- insert-correct ρ (c₁ ∗* x₁) (c₂ ∗* x₂ ∗+ xs) with VarProductComparison.compare x₁ x₂
-- insert-correct ρ (c₁ ∗* x₁) (c₂ ∗* x₂ ∗+ xs) | VarProductComparison.less = refl
-- insert-correct ρ (c₁ ∗* x₁) (c₂ ∗* x₂ ∗+ xs) | VarProductComparison.equal = refl
-- insert-correct ρ (c₁ ∗* x₁) (c₂ ∗* x₂ ∗+ xs) | VarProductComparison.greater =
--   begin
--     c₁ * ⟦ x₁ ⟧VP ρ + (c₂ * ⟦ x₂ ⟧VP ρ + ⟦ xs ⟧RLSNM ρ)
--   ≈⟨ sym +-assoc ⟩
--     (c₁ * ⟦ x₁ ⟧VP ρ + c₂ * ⟦ x₂ ⟧VP ρ) + ⟦ xs ⟧RLSNM ρ
--   ≈⟨ +-cong +-comm refl ⟩
--     (c₂ * ⟦ x₂ ⟧VP ρ + c₁ * ⟦ x₁ ⟧VP ρ) + ⟦ xs ⟧RLSNM ρ
--   ≈⟨ +-assoc ⟩
--     c₂ * ⟦ x₂ ⟧VP ρ + (c₁ * ⟦ x₁ ⟧VP ρ + ⟦ xs ⟧RLSNM ρ)
--   ≡⟨⟩
--     c₂ * (⟦ x₂ ⟧VP ρ) + (⟦ (c₁ ∗* x₁) ⟧NM ρ + ⟦ xs ⟧RLSNM ρ)
--   ≈⟨ +-cong refl (insert-correct ρ (c₁ ∗* x₁) xs) ⟩
--     c₂ * (⟦ x₂ ⟧VP ρ) + ⟦ insert (c₁ ∗* x₁) xs ⟧RLSNM ρ
--   ∎

sort : ∀ {n} → RightLeaningSumOfNormalizedMonomials n → RightLeaningSumOfNormalizedMonomials n
sort nil = nil
sort (x ∗+ xs) = insert x (sort xs)

sort-correct : ∀ {n} → (ρ : Vec Expr n) → (p : RightLeaningSumOfNormalizedMonomials n) → ⟦ p ⟧RLSNM ρ ≡ ⟦ sort p ⟧RLSNM ρ
sort-correct ρ nil = refl
sort-correct ρ (x ∗+ xs) =
  begin
    ⟦ x ⟧NM ρ + ⟦ xs ⟧RLSNM ρ
  ≈⟨ +-cong refl (sort-correct ρ xs) ⟩
    ⟦ x ⟧NM ρ + ⟦ sort xs ⟧RLSNM ρ
  ≈⟨ insert-correct ρ x (sort xs) ⟩
    ⟦ insert x (sort xs) ⟧RLSNM ρ
  ∎

------------------------------------------------------------------------
-- Squashing

-- squash' : ∀ {n} → Expr → VarProduct n → RightLeaningSumOfNormalizedMonomials n → RightLeaningSumOfNormalizedMonomials n
-- squash' c x nil = c ∗* x ∗+ nil
-- squash' c₁ x₁ (c₂ ∗* x₂ ∗+ xs) with VarProductComparison.decEq x₁ x₂
-- ... | yes p = squash' (c₁ + c₂) x₁ xs  -- XXX: How can we normalize c₁ + c₂???
-- ... | no ¬p = c₁ ∗* x₁ ∗+ squash' c₂ x₂ xs

-- squash'-correct : ∀ {n} → (ρ : Vec Expr n) → (c : Expr) → (x : VarProduct n) → (xs : RightLeaningSumOfNormalizedMonomials n) → c * ⟦ x ⟧VP ρ + ⟦ xs ⟧RLSNM ρ ≡ ⟦ squash' c x xs ⟧RLSNM ρ
-- squash'-correct ρ c x nil = refl
-- squash'-correct ρ c₁ x₁ (c₂ ∗* x₂ ∗+ xs) with VarProductComparison.decEq x₁ x₂
-- squash'-correct ρ c₁ x₁ (c₂ ∗* .x₁ ∗+ xs) | yes Prefl =
--   begin
--     c₁ * ⟦ x₁ ⟧VP ρ + (c₂ * ⟦ x₁ ⟧VP ρ + ⟦ xs ⟧RLSNM ρ)
--   ≈⟨ sym +-assoc ⟩
--     (c₁ * ⟦ x₁ ⟧VP ρ + c₂ * ⟦ x₁ ⟧VP ρ) + ⟦ xs ⟧RLSNM ρ
--   ≈⟨ +-cong (sym distribʳ-*-+) refl ⟩
--     (c₁ + c₂) * ⟦ x₁ ⟧VP ρ + ⟦ xs ⟧RLSNM ρ
--   ≈⟨ squash'-correct ρ (c₁ + c₂) x₁ xs ⟩
--     ⟦ squash' (c₁ + c₂) x₁ xs ⟧RLSNM ρ
--   ∎
-- ... | no ¬p = +-cong refl (squash'-correct ρ c₂ x₂ xs)

-- squash : ∀ {n} → RightLeaningSumOfNormalizedMonomials n → RightLeaningSumOfNormalizedMonomials n
-- squash nil = nil
-- squash (x ∗* x₁ ∗+ xs) = squash' x x₁ xs

-- open import Translate.Support
open import Data.Product

postulate
  -- XXX: THIS MAY NOT BE TRUE WHEN COINDUCTION IS INVOLVED!
  quote-correct : ∀ {n} {x y : :Expr n} → quoteTerm x P≡ quoteTerm y → x P≡ y

exprEq' : ∀ {n} → (x y : :Expr n) → Maybe (x P≡ y)
exprEq' {n} x y with (quoteTerm x) Term≟ (quoteTerm y)
exprEq' x y | yes p = {!!}
exprEq' x y | no ¬p = {!!}

try-combine : ∀ {n} → (l r : NormalizedMonomial n) → Maybe (Σ (NormalizedMonomial n) (λ p → (∀ ρ → ⟦ l ⟧NM ρ + ⟦ r ⟧NM ρ ≡ ⟦ p ⟧NM ρ)))
try-combine (con x) (con x₁) = just (con (x C+ x₁) , (λ ρ → C+-correct x x₁))
try-combine (x₁ ∗* l) (x₂ ∗* r) with (quoteTerm x₁) Term≟ (quoteTerm x₂) | try-combine l r
try-combine {n} (x₁ ∗* l) (x₂ ∗* r) | yes eq | just (xs , prf) = just (x₁ ∗* xs , (λ ρ → begin
      semantics x₁ ρ * ⟦ l ⟧NM ρ + semantics x₂ ρ * ⟦ r ⟧NM ρ
    ≈⟨ +-cong refl {!quote-correct {n} {x₁} {x₂} eq !} ⟩
      semantics x₁ ρ * ⟦ l ⟧NM ρ + semantics x₁ ρ * ⟦ r ⟧NM ρ
    ≈⟨ sym (distribˡ-*-+) ⟩
      semantics x₁ ρ * (⟦ l ⟧NM ρ + ⟦ r ⟧NM ρ)
    ≈⟨ *-cong refl (prf ρ) ⟩
      semantics x₁ ρ * ⟦ xs ⟧NM ρ
    ∎
  ))
try-combine (x ∗* l) (x₁ ∗* r) | _ | nothing = nothing
try-combine (x₁ ∗* l) (x₂ ∗* r) | no _ | _ = nothing
try-combine _ _ = nothing

-- squash-correct : ∀ {n} → (ρ : Vec Expr n) → (xs : RightLeaningSumOfNormalizedMonomials n) → ⟦ xs ⟧RLSNM ρ ≡ ⟦ squash xs ⟧RLSNM ρ
-- squash-correct ρ nil = refl
-- squash-correct ρ (c ∗* x ∗+ xs) = squash'-correct ρ c x xs

-- ------------------------------------------------------------------------
-- -- Normalization

-- ⟦_⇓⟧ : ∀ {n} → Polynomial n → Vec Expr n → Expr
-- ⟦ p ⇓⟧ ρ = ⟦ squash $ sort $ throw-out-zeros $ normalize-monomials $ lean-right $ expand p ⟧RLSNM ρ

-- correct : ∀ {n} (e : Polynomial n) ρ → ⟦ e ⇓⟧ ρ ≡ ⟦ e ⟧ ρ
-- correct e ρ =
--   begin
--     ⟦ e ⇓⟧ ρ
--   ≡⟨⟩
--     ⟦ squash (sort (throw-out-zeros (normalize-monomials (lean-right (expand e))))) ⟧RLSNM ρ
--   ≈⟨ sym (squash-correct ρ (sort (throw-out-zeros (normalize-monomials (lean-right (expand e)))))) ⟩
--     ⟦ sort (throw-out-zeros (normalize-monomials (lean-right (expand e)))) ⟧RLSNM ρ
--   ≈⟨ sym (sort-correct ρ (throw-out-zeros (normalize-monomials (lean-right (expand e))))) ⟩
--     ⟦ throw-out-zeros (normalize-monomials (lean-right (expand e))) ⟧RLSNM ρ
--   ≈⟨ sym (throw-out-zeros-correct ρ (normalize-monomials (lean-right (expand e)))) ⟩
--     ⟦ normalize-monomials (lean-right (expand e)) ⟧RLSNM ρ
--   ≈⟨ sym (normalize-monomials-correct ρ (lean-right (expand e))) ⟩
--     ⟦ lean-right (expand e) ⟧RLSM ρ
--   ≈⟨ sym (lean-right-correct ρ (expand e)) ⟩
--     ⟦ expand e ⟧SM ρ
--   ≈⟨ sym (expand-correct ρ e) ⟩
--     ⟦ e ⟧ ρ
--   ∎


-- open Reflection ≡-setoid ∗var ⟦_⟧ ⟦_⇓⟧ correct public
--   using (prove; solve) renaming (_⊜_ to _:=_)

