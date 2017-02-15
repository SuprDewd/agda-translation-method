
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
open import Translate.Solver.Types public
open import Translate.Solver.Combinatorics

-- TODO: Can I combine function definitions and correctness proofs using something like CorrectTransform?

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
import Relation.Binary.Reflection as Reflection
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
-- :Expr

-- data :Expr : (n : ℕ) → Set ℓ₁ where
--   con : ∀ {n} → Expr → :Expr n
--   var : ∀ {n} → (Fin n) → :Expr n
--   _:+_ : ∀ {n} → :Expr n → :Expr n → :Expr n
--   _:*_ : ∀ {n} → :Expr n → :Expr n → :Expr n

-- _≟0 : (e : Expr) → Dec (e ≡ zero)
-- _≟0 = {!!}

-- ⟦_⟧ : ∀ {n} → :Expr n → Env n → Expr
-- -- ⟦ :var x ⟧ Γ = lookup x Γ
-- ⟦ :zero ⟧ Γ = zero
-- ⟦ :suc x ⟧ Γ = suc (⟦ x ⟧ Γ)
-- ⟦ l :+ r ⟧ Γ = ⟦ l ⟧ Γ + ⟦ r ⟧ Γ
-- ⟦ l :* r ⟧ Γ = ⟦ l ⟧ Γ * ⟦ r ⟧ Γ

import Level as L
ℓ₁ : L.Level
ℓ₁ = L.suc L.zero

private

  -- distribˡ-*-+ : ∀ {a b c} → a * (b + c) ≡ a * b + a * c
  -- distribˡ-*-+ = ?

  suc-distrib : ∀ {x} → suc x ≡ suc zero + x
  suc-distrib {x} = axiom Prefl (mkBij to from)
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
-- Expansion by distributivity

data Constant : Set where
  :zero : Constant
  :suc : Constant → Constant
  _:+_ : Constant → Constant → Constant
  _:*_ : Constant → Constant → Constant

data Monomial (n : ℕ) : Set ℓ₁ where
  con : Constant → Monomial n
  var : (Fin n) → Monomial n
  fun : :Fun n → Monomial n
  _:*_ : Monomial n → Monomial n → Monomial n

data SumOfMonomials (n : ℕ) : Set ℓ₁ where
  mon : Monomial n → SumOfMonomials n
  _:+_ : SumOfMonomials n → SumOfMonomials n → SumOfMonomials n

⟦_⟧C : Constant → Expr
⟦ :zero ⟧C = zero
⟦ :suc x ⟧C = suc ⟦ x ⟧C
⟦ x :+ y ⟧C = ⟦ x ⟧C + ⟦ y ⟧C
⟦ x :* y ⟧C = ⟦ x ⟧C * ⟦ y ⟧C

⟦_⟧M : ∀ {n} → Monomial n → Env n → Expr
⟦ con x ⟧M Γ = ⟦ x ⟧C
⟦ var x ⟧M Γ = ⟦ :var x ⟧ Γ
⟦ fun f ⟧M Γ = ⟦ :fun f ⟧ Γ
⟦ x :* y ⟧M Γ = ⟦ x ⟧M Γ * ⟦ y ⟧M Γ

⟦_⟧SM : ∀ {n} → SumOfMonomials n → Env n → Expr
⟦ mon x ⟧SM Γ = ⟦ x ⟧M Γ
⟦ x :+ y ⟧SM Γ = ⟦ x ⟧SM Γ + ⟦ y ⟧SM Γ

*-distrib : ∀ {n} → SumOfMonomials n -> SumOfMonomials n → SumOfMonomials n
*-distrib (mon l) (mon r) = mon (l :* r)
*-distrib (mon l) (r₁ :+ r₂) = *-distrib (mon l) r₁ :+ *-distrib (mon l) r₂
*-distrib (l₁ :+ l₂) (mon r) = *-distrib l₁ (mon r) :+ *-distrib l₂ (mon r)
*-distrib (l₁ :+ l₂) (r₁ :+ r₂) = *-distrib l₁ r₁ :+ *-distrib l₁ r₂ :+ *-distrib l₂ r₁ :+ *-distrib l₂ r₂

*-distrib-correct : ∀ {n} Γ → (p : SumOfMonomials n) → (q : SumOfMonomials n) → ⟦ *-distrib p q ⟧SM Γ ≡ ⟦ p ⟧SM Γ * ⟦ q ⟧SM Γ
*-distrib-correct Γ (mon l) (mon r) = refl
*-distrib-correct Γ (mon l) (r₁ :+ r₂) =
  begin
    (⟦ *-distrib (mon l) r₁ ⟧SM Γ) + (⟦ *-distrib (mon l) r₂ ⟧SM Γ)
  ≈⟨ +-cong (*-distrib-correct Γ (mon l) r₁) (*-distrib-correct Γ (mon l) r₂) ⟩
    (⟦ mon l ⟧SM Γ) * (⟦ r₁ ⟧SM Γ) + (⟦ mon l ⟧SM Γ) * (⟦ r₂ ⟧SM Γ)
  ≡⟨⟩
    (⟦ l ⟧M Γ) * (⟦ r₁ ⟧SM Γ) + (⟦ l ⟧M Γ) * (⟦ r₂ ⟧SM Γ)
  ≈⟨ +-cong *-comm *-comm ⟩
    (⟦ r₁ ⟧SM Γ) * (⟦ l ⟧M Γ) + (⟦ r₂ ⟧SM Γ) * (⟦ l ⟧M Γ)
  ≈⟨ sym distribʳ-*-+ ⟩
    (⟦ r₁ ⟧SM Γ + ⟦ r₂ ⟧SM Γ) * ⟦ l ⟧M Γ
  ≈⟨ *-comm ⟩
    ⟦ l ⟧M Γ * (⟦ r₁ ⟧SM Γ + ⟦ r₂ ⟧SM Γ)
  ∎
*-distrib-correct Γ (l₁ :+ l₂) (mon r) =
  begin
    (⟦ *-distrib l₁ (mon r) ⟧SM Γ) + (⟦ *-distrib l₂ (mon r) ⟧SM Γ)
  ≈⟨ +-cong (*-distrib-correct Γ l₁ (mon r)) (*-distrib-correct Γ l₂ (mon r)) ⟩
    ⟦ l₁ ⟧SM Γ * ⟦ mon r ⟧SM Γ + ⟦ l₂ ⟧SM Γ * ⟦ mon r ⟧SM Γ
  ≡⟨⟩
    ⟦ l₁ ⟧SM Γ * ⟦ r ⟧M Γ + ⟦ l₂ ⟧SM Γ * ⟦ r ⟧M Γ
  ≈⟨ sym distribʳ-*-+ ⟩
    (⟦ l₁ ⟧SM Γ + ⟦ l₂ ⟧SM Γ) * ⟦ r ⟧M Γ
  ∎
*-distrib-correct Γ (l₁ :+ l₂) (r₁ :+ r₂) =
  begin
    ((⟦ *-distrib l₁ r₁ ⟧SM Γ + ⟦ *-distrib l₁ r₂ ⟧SM Γ) + ⟦ *-distrib l₂ r₁ ⟧SM Γ) + ⟦ *-distrib l₂ r₂ ⟧SM Γ
  ≈⟨ +-assoc ⟩ -- (⟦ *-distrib l₁ r₁ ⟧SM Γ + ⟦ *-distrib l₁ r₂ ⟧SM Γ) (⟦ *-distrib l₂ r₁ ⟧SM Γ) (⟦ *-distrib l₂ r₂ ⟧SM Γ)
    (⟦ *-distrib l₁ r₁ ⟧SM Γ + ⟦ *-distrib l₁ r₂ ⟧SM Γ) + (⟦ *-distrib l₂ r₁ ⟧SM Γ + ⟦ *-distrib l₂ r₂ ⟧SM Γ)
  ≈⟨ +-cong (+-cong (*-distrib-correct Γ l₁ r₁) (*-distrib-correct Γ l₁ r₂)) (+-cong (*-distrib-correct Γ l₂ r₁) (*-distrib-correct Γ l₂ r₂)) ⟩
    (⟦ l₁ ⟧SM Γ * ⟦ r₁ ⟧SM Γ + ⟦ l₁ ⟧SM Γ * ⟦ r₂ ⟧SM Γ) + (⟦ l₂ ⟧SM Γ * ⟦ r₁ ⟧SM Γ + ⟦ l₂ ⟧SM Γ * ⟦ r₂ ⟧SM Γ)
  ≈⟨ +-cong (sym distribˡ-*-+) (sym distribˡ-*-+) ⟩
    ⟦ l₁ ⟧SM Γ * (⟦ r₁ ⟧SM Γ + ⟦ r₂ ⟧SM Γ) + ⟦ l₂ ⟧SM Γ * (⟦ r₁ ⟧SM Γ + ⟦ r₂ ⟧SM Γ)
  ≈⟨ sym distribʳ-*-+ ⟩
    (⟦ l₁ ⟧SM Γ + ⟦ l₂ ⟧SM Γ) * (⟦ r₁ ⟧SM Γ + ⟦ r₂ ⟧SM Γ)
  ∎

-- TODO: Make sure this is correct
-- TODO: Apply this
distrib : ∀ {n} → :Expr n → SumOfMonomials n
distrib (:var x) = mon (var x)
distrib :zero = mon (con :zero)
distrib (:suc x) = mon (con (:suc :zero)) :+ distrib x
distrib (l :+ r) = distrib l :+ distrib r
distrib (l :* r) = *-distrib (distrib l) (distrib r)
distrib (:fun f) = mon (fun f)

-- distrib (con x) = mon (con x)
-- distrib (var x) = mon (var x)
-- distrib (l :+ r) = distrib l :+ distrib r
-- distrib (l :* r) = *-distrib (distrib l) (distrib r)

distrib-correct : ∀ {n} → (Γ : Env n) → (p : :Expr n) → ⟦ distrib p ⟧SM Γ ≡ ⟦ p ⟧ Γ
-- distrib-correct Γ (:var x) = refl
distrib-correct Γ :zero = refl
distrib-correct Γ (:suc x) =
  begin
    suc zero + ⟦ distrib x ⟧SM Γ
  ≈⟨ +-cong refl (distrib-correct Γ x) ⟩
    suc zero + (⟦ x ⟧ Γ)
  ≈⟨ sym suc-distrib ⟩
    suc (⟦ x ⟧ Γ)
  ∎
distrib-correct Γ (l :+ r) = +-cong (distrib-correct Γ l) (distrib-correct Γ r)
distrib-correct Γ (l :* r) =
  begin
    ⟦ *-distrib (distrib l) (distrib r) ⟧SM Γ
  ≈⟨ *-distrib-correct Γ (distrib l) (distrib r) ⟩
    ⟦ distrib l ⟧SM Γ * ⟦ distrib r ⟧SM Γ
  ≈⟨ *-cong (distrib-correct Γ l) (distrib-correct Γ r) ⟩
    ⟦ l ⟧ Γ * ⟦ r ⟧ Γ
  ∎
distrib-correct Γ (:var x) = refl
distrib-correct Γ (:fun f) = refl
-- distrib-correct Γ (con x) = refl
-- distrib-correct Γ (var x) = refl
-- distrib-correct Γ (p :+ p₁) = +-cong (distrib-correct Γ p) (distrib-correct Γ p₁)
-- distrib-correct Γ (p :* p₁) =
--   begin
--     ⟦ p ⟧ Γ * ⟦ p₁ ⟧ Γ
--   ≡⟨ *-cong (distrib-correct Γ p) (distrib-correct Γ p₁) ⟩
--     ⟦ distrib p ⟧SM Γ * ⟦ distrib p₁ ⟧SM Γ
--   ≡⟨ *-distrib-correct Γ (distrib p) (distrib p₁) ⟩
--     ⟦ *-distrib (distrib p) (distrib p₁) ⟧SM Γ
--   ∎

------------------------------------------------------------------------
-- Right leaning

data RightLeaningSumOfMonomials (n : ℕ) : Set ℓ₁ where
  nil : RightLeaningSumOfMonomials n
  _:+_ : Monomial n → RightLeaningSumOfMonomials n → RightLeaningSumOfMonomials n

⟦_⟧RLSM : ∀ {n} → RightLeaningSumOfMonomials n → Env n → Expr
⟦ nil ⟧RLSM Γ = zero
⟦ l :+ r ⟧RLSM Γ = ⟦ l ⟧M Γ + ⟦ r ⟧RLSM Γ

combine-lean-right : ∀ {n} → RightLeaningSumOfMonomials n → RightLeaningSumOfMonomials n → RightLeaningSumOfMonomials n
combine-lean-right nil r = r
combine-lean-right (x :+ l) r = x :+ (combine-lean-right l r)

combine-lean-right-correct : ∀ {n} → (Γ : Env n) → (p q : RightLeaningSumOfMonomials n) → ⟦ combine-lean-right p q ⟧RLSM Γ ≡ ⟦ p ⟧RLSM Γ + ⟦ q ⟧RLSM Γ
combine-lean-right-correct Γ nil r = sym (trans +-comm +-right-identity)
combine-lean-right-correct Γ (x :+ l) r =
  begin
    ⟦ x ⟧M Γ + ⟦ combine-lean-right l r ⟧RLSM Γ
  ≈⟨ +-cong refl (combine-lean-right-correct Γ l r) ⟩
    ⟦ x ⟧M Γ + (⟦ l ⟧RLSM Γ + ⟦ r ⟧RLSM Γ)
  ≈⟨ sym +-assoc ⟩
    (⟦ x ⟧M Γ + ⟦ l ⟧RLSM Γ) + ⟦ r ⟧RLSM Γ
  ∎

-- TODO: Apply this
lean-right : ∀ {n} → SumOfMonomials n → RightLeaningSumOfMonomials n
lean-right (mon x) = x :+ nil
lean-right (mon x :+ r) = x :+ lean-right r
lean-right ((l₁ :+ l₂) :+ r) = combine-lean-right (lean-right l₁) (lean-right (l₂ :+ r))

lean-right-correct : ∀ {n} → (Γ : Env n) → (p : SumOfMonomials n) → ⟦ lean-right p ⟧RLSM Γ ≡ ⟦ p ⟧SM Γ
lean-right-correct Γ (mon x) = +-right-identity
lean-right-correct Γ (mon x :+ r) = +-cong refl (lean-right-correct Γ r)
lean-right-correct Γ ((l₁ :+ l₂) :+ r) =
  begin
    ⟦ combine-lean-right (lean-right l₁) (lean-right (l₂ :+ r)) ⟧RLSM Γ
  ≈⟨ combine-lean-right-correct Γ (lean-right l₁) (lean-right (l₂ :+ r)) ⟩
    ⟦ lean-right l₁ ⟧RLSM Γ + ⟦ lean-right (l₂ :+ r) ⟧RLSM Γ
  ≈⟨ +-cong (lean-right-correct Γ l₁) (lean-right-correct Γ (l₂ :+ r)) ⟩
    ⟦ l₁ ⟧SM Γ + (⟦ l₂ :+ r ⟧SM Γ)
  ≡⟨⟩
    ⟦ l₁ ⟧SM Γ + (⟦ l₂ ⟧SM Γ + ⟦ r ⟧SM Γ)
  ≈⟨ sym +-assoc ⟩
    (⟦ l₁ ⟧SM Γ + ⟦ l₂ ⟧SM Γ) + ⟦ r ⟧SM Γ
  ∎

------------------------------------------------------------------------
-- Monomial normalization

-- VarProduct : ℕ → Set
-- VarProduct n = Vec ℕ n

-- ⟦_⟧VP_ : ∀ {n} → VarProduct n → Env n → Expr
-- ⟦ [] ⟧VP Γ = suc zero
-- ⟦ ℕzero ∷ xs ⟧VP (Γ₁ ∷ Γ) = ⟦ xs ⟧VP Γ
-- ⟦ ℕsuc x ∷ xs ⟧VP (Γ₁ ∷ Γ) = Γ₁ * ⟦ x ∷ xs ⟧VP (Γ₁ ∷ Γ)

-- varProduct-none : ∀ {n} → VarProduct n
-- varProduct-none {n} = replicate 0

-- varProduct-none-correct : ∀ {n} → (Γ : Env n) → ⟦ varProduct-none {n} ⟧VP Γ ≡ suc zero
-- varProduct-none-correct {ℕzero} Γ = refl
-- varProduct-none-correct {ℕsuc n} (Γ₁ ∷ Γ) = varProduct-none-correct Γ

-- varProduct-one : ∀ {n} → Fin n → VarProduct n
-- varProduct-one Fin.zero = 1 ∷ varProduct-none
-- varProduct-one (Fin.suc i) = 0 ∷ varProduct-one i

-- varProduct-one-correct : ∀ {n} → (Γ : Env n) → (f : Fin n) → ⟦ varProduct-one {n} f ⟧VP Γ ≡ lookup f Γ
-- varProduct-one-correct {ℕsuc n} (Γ₁ ∷ Γ) Fin.zero =
--   begin
--     ⟦ varProduct-one {ℕsuc n} Fin.zero ⟧VP (Γ₁ ∷ Γ)
--   ≡⟨⟩
--     ⟦ 1 ∷ varProduct-none ⟧VP (Γ₁ ∷ Γ)
--   ≡⟨⟩
--     Γ₁ * ⟦ varProduct-none {n} ⟧VP Γ
--   ≈⟨ *-cong refl (varProduct-none-correct Γ) ⟩
--     Γ₁ * (suc zero)
--   ≈⟨ *-right-identity ⟩
--     lookup Fin.zero (Γ₁ ∷ Γ)
--   ∎
-- varProduct-one-correct (Γ₁ ∷ Γ) (Fin.suc f) = varProduct-one-correct Γ f

-- varProduct-mul : ∀ {n} → VarProduct n → VarProduct n → VarProduct n
-- varProduct-mul [] [] = []
-- varProduct-mul (x ∷ l) (x₁ ∷ r) = (x ℕ+ x₁) ∷ varProduct-mul l r

-- varProduct-mul-correct : ∀ {n} → (Γ : Env n) → (l : VarProduct n) → (r : VarProduct n) → ⟦ l ⟧VP Γ * ⟦ r ⟧VP Γ ≡ ⟦ varProduct-mul l r ⟧VP Γ
-- varProduct-mul-correct Γ [] [] = trans *-comm *-right-identity
-- varProduct-mul-correct (Γ ∷ Γ₁) (ℕzero ∷ l) (ℕzero ∷ r) = varProduct-mul-correct Γ₁ l r
-- varProduct-mul-correct (Γ ∷ Γ₁) (ℕzero ∷ l) (ℕsuc x ∷ r) =
--   begin
--     ⟦ ℕzero ∷ l ⟧VP (Γ ∷ Γ₁) * ⟦ ℕsuc x ∷ r ⟧VP (Γ ∷ Γ₁)
--   ≡⟨⟩
--     ⟦ ℕzero ∷ l ⟧VP (Γ ∷ Γ₁) * (Γ * ⟦ x ∷ r ⟧VP (Γ ∷ Γ₁))
--   ≈⟨ *-cong refl *-comm ⟩
--     ⟦ ℕzero ∷ l ⟧VP (Γ ∷ Γ₁) * (⟦ x ∷ r ⟧VP (Γ ∷ Γ₁) * Γ)
--   ≈⟨ sym *-assoc ⟩
--     (⟦ ℕzero ∷ l ⟧VP (Γ ∷ Γ₁) * ⟦ x ∷ r ⟧VP (Γ ∷ Γ₁)) * Γ
--   ≈⟨ *-comm ⟩
--     Γ * (⟦ ℕzero ∷ l ⟧VP (Γ ∷ Γ₁) * ⟦ x ∷ r ⟧VP (Γ ∷ Γ₁))
--   ≈⟨ *-cong refl (varProduct-mul-correct (Γ ∷ Γ₁) (ℕzero ∷ l) (x ∷ r)) ⟩
--     Γ * ⟦ varProduct-mul (ℕzero ∷ l) (x ∷ r) ⟧VP (Γ ∷ Γ₁)
--   ≡⟨⟩
--     Γ * ⟦ (ℕzero ℕ+ x) ∷ varProduct-mul l r ⟧VP (Γ ∷ Γ₁)
--   ≡⟨⟩
--     Γ * ⟦ x ∷ varProduct-mul l r ⟧VP (Γ ∷ Γ₁)
--   ≡⟨⟩
--     ⟦ (ℕsuc x) ∷ varProduct-mul l r ⟧VP (Γ ∷ Γ₁)
--   ≡⟨⟩
--     ⟦ (ℕzero ℕ+ ℕsuc x) ∷ varProduct-mul l r ⟧VP (Γ ∷ Γ₁)
--   ≡⟨⟩
--     ⟦ varProduct-mul (ℕzero ∷ l) (ℕsuc x ∷ r) ⟧VP (Γ ∷ Γ₁)
--   ∎
-- varProduct-mul-correct (Γ ∷ Γ₁) (ℕsuc x ∷ l) (x₁ ∷ r) =
--   begin
--     ⟦ (ℕsuc x ∷ l) ⟧VP (Γ ∷ Γ₁) * ⟦ x₁ ∷ r ⟧VP (Γ ∷ Γ₁)
--   ≡⟨⟩
--     (Γ * ⟦ (x ∷ l) ⟧VP (Γ ∷ Γ₁)) * ⟦ x₁ ∷ r ⟧VP (Γ ∷ Γ₁)
--   ≈⟨ *-assoc ⟩
--     Γ * (⟦ (x ∷ l) ⟧VP (Γ ∷ Γ₁) * ⟦ x₁ ∷ r ⟧VP (Γ ∷ Γ₁))
--   ≈⟨ *-cong refl (varProduct-mul-correct (Γ ∷ Γ₁) (x ∷ l) (x₁ ∷ r)) ⟩
--     Γ * ⟦ varProduct-mul (x ∷ l) (x₁ ∷ r) ⟧VP (Γ ∷ Γ₁)
--   ≡⟨⟩
--     Γ * ⟦ (x ℕ+ x₁) ∷ varProduct-mul l r ⟧VP (Γ ∷ Γ₁)
--   ≡⟨⟩
--     ⟦ (ℕsuc (x ℕ+ x₁)) ∷ varProduct-mul l r ⟧VP (Γ ∷ Γ₁)
--   ≡⟨⟩
--     ⟦ (ℕsuc x ℕ+ x₁) ∷ varProduct-mul l r ⟧VP (Γ ∷ Γ₁)
--   ≡⟨⟩
--     ⟦ varProduct-mul (ℕsuc x ∷ l) (x₁ ∷ r) ⟧VP (Γ ∷ Γ₁)
--   ∎


-- data SemiNormalizedMonomial (n : ℕ) : Set ℓ₁ where
--   con : Constant → SemiNormalizedMonomial n
--   var : Fin n → SemiNormalizedMonomial n
--   fun : :Fun n → SemiNormalizedMonomial n
--   _:*_ : :Expr n → SemiNormalizedMonomial n → SemiNormalizedMonomial n
data SnormalizedMonomial (n : ℕ) : Set ℓ₁ where
  mon : Constant → (vs : List (Fin n)) → (fs : List (:Fun n)) → SnormalizedMonomial n

-- ⟦_⟧LC : ∀ {n} → (cs : List Constant) → (Γ : Env n) → Expr
-- ⟦ [] ⟧LC Γ = suc zero
-- ⟦ x ∷ x₁ ⟧LC Γ = ⟦ x ⟧C * ⟦ x₁ ⟧LC Γ

:⟦_⟧LV : ∀ {n} → (cs : List (Fin n)) → :Expr n
:⟦ [] ⟧LV = :suc :zero
:⟦ x ∷ x₁ ⟧LV = :var x :* :⟦ x₁ ⟧LV

⟦_⟧LV : ∀ {n} → (cs : List (Fin n)) → (Γ : Env n) → Expr
⟦ x ⟧LV = ⟦ :⟦ x ⟧LV ⟧

:⟦_⟧LF : ∀ {n} → (cs : List (:Fun n)) → :Expr n
:⟦ [] ⟧LF = :suc :zero
:⟦ x ∷ x₁ ⟧LF = (:fun x) :* :⟦ x₁ ⟧LF

⟦_⟧LF : ∀ {n} → (cs : List (:Fun n)) → (Γ : Env n) → Expr
⟦ x ⟧LF = ⟦ :⟦ x ⟧LF ⟧

⟦_⟧SNM : ∀ {n} → SnormalizedMonomial n → Env n → Expr
⟦ mon c vs fs ⟧SNM Γ = ⟦ c ⟧C * (⟦ vs ⟧LV Γ * ⟦ fs ⟧LF Γ)


insert-lv : ∀ {n} → Fin n → List (Fin n) → List (Fin n)
insert-lv x [] = x ∷ []
insert-lv x (x₁ ∷ xs) with F.compare x x₁
insert-lv g (.(F.inject l) ∷ xs) | F.greater .g l = (F.inject l) ∷ insert-lv g xs
insert-lv .(F.inject l) (g ∷ xs) | F.less .g l = (F.inject l) ∷ (g ∷ xs)
insert-lv i (.i ∷ xs) | F.equal .i = i ∷ (i ∷ xs)

insert-lv-correct : ∀ {n} → (Γ : Env n) → (x : Fin n) → (xs : List (Fin n)) → ⟦ insert-lv x xs ⟧LV Γ ≡ ⟦ :var x ⟧ Γ * ⟦ xs ⟧LV Γ
insert-lv-correct Γ x [] = refl
insert-lv-correct Γ x (x₁ ∷ xs) with F.compare x x₁
insert-lv-correct Γ g (.(F.inject l) ∷ xs) | F.greater .g l =
  begin
    lookup (F.inject l) Γ * ⟦ insert-lv g xs ⟧LV Γ
  ≈⟨ *-cong refl (insert-lv-correct Γ g xs ) ⟩
    lookup (F.inject l) Γ * (lookup g Γ * ⟦ xs ⟧LV Γ)
  ≈⟨ sym *-assoc ⟩
    (lookup (F.inject l) Γ * lookup g Γ) * ⟦ xs ⟧LV Γ
  ≈⟨ *-cong *-comm refl ⟩
    (lookup g Γ * lookup (F.inject l) Γ) * ⟦ xs ⟧LV Γ
  ≈⟨ *-assoc ⟩
    lookup g Γ * (lookup (F.inject l) Γ * ⟦ xs ⟧LV Γ)
  ∎
insert-lv-correct Γ .(F.inject l) (g ∷ xs) | F.less .g l = refl
insert-lv-correct Γ i (.i ∷ xs) | F.equal .i = refl

sort-lv : ∀ {n} → List (Fin n) → List (Fin n)
sort-lv [] = []
sort-lv (x ∷ xs) = insert-lv x (sort-lv xs)

sort-lv-correct : ∀ {n} → (Γ : Env n) → (xs : List (Fin n)) → ⟦ sort-lv xs ⟧LV Γ ≡ ⟦ xs ⟧LV Γ
sort-lv-correct Γ [] = refl
sort-lv-correct Γ (x ∷ xs) =
  begin
    ⟦ insert-lv x (sort-lv xs) ⟧LV Γ
  ≈⟨ insert-lv-correct Γ x (sort-lv xs) ⟩
    lookup x Γ * ⟦ sort-lv xs ⟧LV Γ
  ≈⟨ *-cong refl (sort-lv-correct Γ xs) ⟩
    lookup x Γ * ⟦ xs ⟧LV Γ
  ∎


insert-lf : ∀ {n} → :Fun n → List (:Fun n) → List (:Fun n)
insert-lf x [] = x ∷ []
insert-lf x (x₁ ∷ xs) with :FunLt x x₁
insert-lf x (x₁ ∷ xs) | true = x ∷ (x₁ ∷ xs)
insert-lf x (x₁ ∷ xs) | false = x₁ ∷ insert-lf x xs

insert-lf-correct : ∀ {n} → (Γ : Env n) → (x : :Fun n) → (xs : List (:Fun n)) → ⟦ insert-lf x xs ⟧LF Γ ≡ ⟦ :fun x ⟧ Γ * ⟦ xs ⟧LF Γ
insert-lf-correct Γ x [] = refl
insert-lf-correct Γ x (x₁ ∷ xs) with :FunLt x x₁
insert-lf-correct Γ x (x₁ ∷ xs) | true = refl
insert-lf-correct Γ x (x₁ ∷ xs) | false =
  begin
    fun (⟦ x₁ ⟧F Γ) * ⟦ insert-lf x xs ⟧LF Γ
  ≈⟨ *-cong refl (insert-lf-correct Γ x xs) ⟩
    fun (⟦ x₁ ⟧F Γ) * (fun (⟦ x ⟧F Γ) * ⟦ xs ⟧LF Γ)
  ≈⟨ sym *-assoc ⟩
    (fun (⟦ x₁ ⟧F Γ) * fun (⟦ x ⟧F Γ)) * ⟦ xs ⟧LF Γ
  ≈⟨ *-cong *-comm refl ⟩
    (fun (⟦ x ⟧F Γ) * fun (⟦ x₁ ⟧F Γ)) * ⟦ xs ⟧LF Γ
  ≈⟨ *-assoc ⟩
    fun (⟦ x ⟧F Γ) * (fun (⟦ x₁ ⟧F Γ) * ⟦ xs ⟧LF Γ)
  ∎

sort-lf : ∀ {n} → List (:Fun n) → List (:Fun n)
sort-lf [] = []
sort-lf (x ∷ xs) = insert-lf x (sort-lf xs)

sort-lf-correct : ∀ {n} → (Γ : Env n) → (xs : List (:Fun n)) → ⟦ sort-lf xs ⟧LF Γ ≡ ⟦ xs ⟧LF Γ
sort-lf-correct Γ [] = refl
sort-lf-correct Γ (x ∷ xs) =
  begin
    ⟦ insert-lf x (sort-lf xs) ⟧LF Γ
  ≈⟨ insert-lf-correct Γ x (sort-lf xs) ⟩
    fun (⟦ x ⟧F Γ) * ⟦ sort-lf xs ⟧LF Γ
  ≈⟨ *-cong refl (sort-lf-correct Γ xs) ⟩
    fun (⟦ x ⟧F Γ) * ⟦ xs ⟧LF Γ
  ∎

-- simplify : ∀ {n a} → (A : Set a) → (A → Env n → Expr) →

-- ⟦ mon [] [] [] ⟧NM Γ = suc zero
-- ⟦ mon [] [] (f ∷ fs) ⟧NM Γ = ⟦ :fun f ⟧ Γ * ⟦ mon [] [] fs ⟧NM Γ
-- ⟦ mon [] (v ∷ vs) fs ⟧NM Γ = ⟦ :var v ⟧ Γ * ⟦ mon [] vs fs ⟧NM Γ
-- ⟦ mon (c ∷ cs) vs fs ⟧NM Γ = ⟦ c ⟧C * ⟦ mon cs vs fs ⟧NM Γ

-- ⟦ con x ⟧NM Γ = ⟦ x ⟧C
-- ⟦ l :* r ⟧NM Γ = ⟦ l ⟧ Γ * ⟦ r ⟧NM Γ
-- ⟦ var x ⟧NM Γ = ⟦ :var x ⟧ Γ
-- ⟦ fun f ⟧NM Γ = ⟦ :fun f ⟧ Γ

-- data NormalizedMonomial : ℕ → Set ℓ₁ where
--   _:*_ : ∀ {n} → Constant → VarProduct n → NormalizedMonomial n

-- ⟦_⟧NM : ∀ {n} → NormalizedMonomial n → Env n → Expr
-- ⟦ x :* x₁ ⟧NM Γ = ⟦ x ⟧C * ⟦ x₁ ⟧VP Γ

-- combine-normalized-monomial : ∀ {n} → NormalizedMonomial n → NormalizedMonomial n → NormalizedMonomial n
-- combine-normalized-monomial (cₗ :* xₗ) (cᵣ :* xᵣ) = (cₗ :* cᵣ) :* (varProduct-mul xₗ xᵣ) -- XXX: How can we normalize cₗ * cᵣ???

-- combine-normalized-monomial-correct : ∀ {n} (Γ : Env n) → (p : NormalizedMonomial n) → (q : NormalizedMonomial n) → ⟦ p ⟧NM Γ * ⟦ q ⟧NM Γ ≡ ⟦ combine-normalized-monomial p q ⟧NM Γ
-- combine-normalized-monomial-correct Γ (x :* x₁) (x₂ :* x₃) = ?
--   -- begin
--   --   (⟦ x ⟧C * ⟦ x₁ ⟧VP Γ) * (⟦ x₂ ⟧C * (⟦ x₃ ⟧VP Γ))
--   -- ≈⟨ *-assoc ⟩
--   --   ⟦ x ⟧C * (⟦ x₁ ⟧VP Γ * (⟦ x₂ ⟧C * (⟦ x₃ ⟧VP Γ)))
--   -- ≈⟨ *-cong refl (sym *-assoc) ⟩
--   --   ⟦ x ⟧C * ((⟦ x₁ ⟧VP Γ * ⟦ x₂ ⟧C) * (⟦ x₃ ⟧VP Γ))
--   -- ≈⟨ *-cong refl (*-cong *-comm refl) ⟩
--   --   ⟦ x ⟧C * ((⟦ x₂ ⟧C * ⟦ x₁ ⟧VP Γ) * (⟦ x₃ ⟧VP Γ))
--   -- ≈⟨ sym *-assoc ⟩
--   --   (⟦ x ⟧C * (⟦ x₂ ⟧C * ⟦ x₁ ⟧VP Γ)) * (⟦ x₃ ⟧VP Γ)
--   -- ≈⟨ *-cong (sym *-assoc) refl ⟩
--   --   ((⟦ x ⟧C * ⟦ x₂ ⟧C) * ⟦ x₁ ⟧VP Γ) * (⟦ x₃ ⟧VP Γ)
--   -- ≈⟨ *-assoc ⟩
--   --   (⟦ x ⟧C * ⟦ x₂ ⟧C) * (⟦ x₁ ⟧VP Γ * ⟦ x₃ ⟧VP Γ)
--   -- ≈⟨ *-cong refl (varProduct-mul-correct Γ x₁ x₃) ⟩
--   --   (⟦ x ⟧C * ⟦ x₂ ⟧C) * (⟦ varProduct-mul x₁ x₃ ⟧VP Γ)
--   -- ∎

-- combine-normalized-monomial : ∀ {n} → SemiNormalizedMonomial n → SemiNormalizedMonomial n → SemiNormalizedMonomial n
-- -- combine-normalized-monomial (con x) (con x₁) = con (x :* x₁)
-- -- combine-normalized-monomial (con x) (x₁ :* r) = x₁ :* combine-normalized-monomial (con x) r
-- -- combine-normalized-monomial (x :* l) r = x :* combine-normalized-monomial l r
-- combine-normalized-monomial (con x) (con x₁) = ?
-- combine-normalized-monomial (con x) (var x₁) = ?
-- combine-normalized-monomial (con x) (fun x₁) = ?
-- combine-normalized-monomial (con x) (x₁ :* b) = ?
-- combine-normalized-monomial (var x) (con x₁) = ?
-- combine-normalized-monomial (var x) (var x₁) = ?
-- combine-normalized-monomial (var x) (fun x₁) = ?
-- combine-normalized-monomial (var x) (x₁ :* b) = ?
-- combine-normalized-monomial (fun x) (con x₁) = ?
-- combine-normalized-monomial (fun x) (var x₁) = ?
-- combine-normalized-monomial (fun x) (fun x₁) = ?
-- combine-normalized-monomial (fun x) (x₁ :* b) = ?
-- combine-normalized-monomial (x :* a) (con x₁) = ?
-- combine-normalized-monomial (x :* a) (var x₁) = ?
-- combine-normalized-monomial (x :* a) (fun x₁) = ?
-- combine-normalized-monomial (x :* a) (x₁ :* b) = ?

-- combine-normalized-monomial-correct : ∀ {n} → (Γ : Env n) → (p q : SemiNormalizedMonomial n) → ⟦ p ⟧SNM Γ * ⟦ q ⟧SNM Γ ≡ ⟦ combine-normalized-monomial p q ⟧SNM Γ
-- combine-normalized-monomial-correct Γ (con x) (con x₁) = refl
-- combine-normalized-monomial-correct Γ (con x) (x₁ :* r) =
--   begin
--     ⟦ x ⟧C * (⟦ x₁ ⟧ Γ * ⟦ r ⟧SNM Γ)
--   ≈⟨ sym *-assoc ⟩
--     (⟦ x ⟧C * ⟦ x₁ ⟧ Γ) * ⟦ r ⟧SNM Γ
--   ≈⟨ *-cong *-comm refl ⟩
--     (⟦ x₁ ⟧ Γ * ⟦ x ⟧C) * ⟦ r ⟧SNM Γ
--   ≈⟨ *-assoc ⟩
--     ⟦ x₁ ⟧ Γ * (⟦ x ⟧C * ⟦ r ⟧SNM Γ)
--   ≈⟨ *-cong refl (combine-normalized-monomial-correct Γ (con x) r) ⟩
--     ⟦ x₁ ⟧ Γ * ⟦ combine-normalized-monomial (con x) r ⟧SNM Γ
--   ∎
-- combine-normalized-monomial-correct Γ (x :* l) r =
--   begin
--     ⟦ x ⟧ Γ * ⟦ l ⟧SNM Γ * ⟦ r ⟧SNM Γ
--   ≈⟨ *-assoc ⟩
--     ⟦ x ⟧ Γ * (⟦ l ⟧SNM Γ * ⟦ r ⟧SNM Γ)
--   ≈⟨ *-cong refl (combine-normalized-monomial-correct Γ l r) ⟩
--     ⟦ x ⟧ Γ * ⟦ combine-normalized-monomial l r ⟧SNM Γ
--   ∎
-- combine-normalized-monomial-correct Γ a b = {!!}

-- normalize-monomial : ∀ {n} → Monomial n → SemiNormalizedMonomial n
-- normalize-monomial (con x) = con x
-- normalize-monomial (var x) = {!!}
-- normalize-monomial (fun f) = {!!}
-- normalize-monomial (l :* r) = combine-normalized-monomial (normalize-monomial l) (normalize-monomial r)

-- normalize-monomial-correct : ∀ {n} → (Γ : Env n) → (p : Monomial n) → ⟦ p ⟧M Γ ≡ ⟦ normalize-monomial p ⟧SNM Γ
-- normalize-monomial-correct Γ (var x) = {!!}
-- normalize-monomial-correct Γ (fun f) = {!!}
-- normalize-monomial-correct Γ (con x) = refl
-- normalize-monomial-correct Γ (x :* x₁) =
--   begin
--     ⟦ x ⟧M Γ * ⟦ x₁ ⟧M Γ
--   ≈⟨ *-cong (normalize-monomial-correct Γ x) (normalize-monomial-correct Γ x₁) ⟩
--     ⟦ normalize-monomial x ⟧SNM Γ * ⟦ normalize-monomial x₁ ⟧SNM Γ
--   ≈⟨ combine-normalized-monomial-correct Γ (normalize-monomial x) (normalize-monomial x₁) ⟩
--     ⟦ combine-normalized-monomial (normalize-monomial x) (normalize-monomial x₁) ⟧SNM Γ
--   ∎

-- insert-normalized-monomial : ∀ {n} → :Expr n → SemiNormalizedMonomial n → SemiNormalizedMonomial n
-- insert-normalized-monomial x (con x₁) = x :* (con x₁)
-- insert-normalized-monomial x (x₁ :* xs) with termLt (quoteTerm x) (quoteTerm x₁)
-- insert-normalized-monomial x (x₁ :* xs) | true = x :* (x₁ :* xs)
-- insert-normalized-monomial x (x₁ :* xs) | false = x₁ :* insert-normalized-monomial x xs
-- insert-normalized-monomial x xs = {!!}

-- insert-normalized-monomial-correct : ∀ {n} → (Γ : Env n) → (p : :Expr n) → (q : SemiNormalizedMonomial n) → (⟦ p ⟧ Γ) * ⟦ q ⟧SNM Γ ≡ ⟦ insert-normalized-monomial p q ⟧SNM Γ
-- insert-normalized-monomial-correct Γ p (con x) = refl
-- insert-normalized-monomial-correct Γ p (x :* q) =
--   begin
--     ⟦ p ⟧ Γ * (⟦ x ⟧ Γ * ⟦ q ⟧SNM Γ)
--   ≈⟨ sym *-assoc ⟩
--     (⟦ p ⟧ Γ * ⟦ x ⟧ Γ) * ⟦ q ⟧SNM Γ
--   ≈⟨ *-cong *-comm refl ⟩
--     (⟦ x ⟧ Γ * ⟦ p ⟧ Γ) * ⟦ q ⟧SNM Γ
--   ≈⟨ *-assoc ⟩
--     ⟦ x ⟧ Γ * (⟦ p ⟧ Γ * ⟦ q ⟧SNM Γ)
--   ≈⟨ *-cong refl (insert-normalized-monomial-correct Γ p q) ⟩
--     ⟦ x ⟧ Γ * ⟦ insert-normalized-monomial p q ⟧SNM Γ
--   ∎
-- insert-normalized-monomial-correct Γ p ps = {!!}

-- sort-normalized-monomial : ∀ {n} → SemiNormalizedMonomial n → SemiNormalizedMonomial n
-- sort-normalized-monomial (con x) = con x
-- sort-normalized-monomial (var x) = var x
-- sort-normalized-monomial (fun f) = fun f
-- sort-normalized-monomial (x :* x₁) = insert-normalized-monomial x (sort-normalized-monomial x₁)

-- sort-normalized-monomial-correct : ∀ {n} → (Γ : Env n) → (p : SemiNormalizedMonomial n) → ⟦ p ⟧SNM Γ ≡ ⟦ sort-normalized-monomial p ⟧SNM Γ
-- sort-normalized-monomial-correct Γ (con x) = refl
-- sort-normalized-monomial-correct Γ (var x) = refl
-- sort-normalized-monomial-correct Γ (fun f) = refl
-- sort-normalized-monomial-correct Γ (x :* x₁) =
--   begin
--     ⟦ x ⟧ Γ * ⟦ x₁ ⟧SNM Γ
--   ≈⟨ *-cong refl (sort-normalized-monomial-correct Γ x₁) ⟩
--     ⟦ x ⟧ Γ * ⟦ sort-normalized-monomial x₁ ⟧SNM Γ
--   ≈⟨ insert-normalized-monomial-correct Γ x (sort-normalized-monomial x₁) ⟩
--     ⟦ insert-normalized-monomial x (sort-normalized-monomial x₁) ⟧SNM Γ
--   ∎

-- squash-normalized-monomial : ∀ {n} → NormalizedMonomial n → NormalizedMonomial n
-- squash-normalized-monomial (con x) = con x
-- squash-normalized-monomial (x :* con x₁) = x :* con x₁
-- squash-normalized-monomial (x :* (x₁ :* xs)) with termEq (quoteTerm x) (quoteTerm x₁)
-- ... | 

-- normalize-monomial : ∀ {n} → Monomial n → NormalizedMonomial n
-- normalize-monomial (con x) = x :* varProduct-none
-- normalize-monomial (var x) = (:suc :zero) :* varProduct-one x
-- normalize-monomial (l :* r) = combine-normalized-monomial (normalize-monomial l) (normalize-monomial r)

-- normalize-monomial-correct : ∀ {n} → (Γ : Env n) → (p : Monomial n) → ⟦ p ⟧M Γ ≡ ⟦ normalize-monomial p ⟧NM Γ
-- normalize-monomial-correct {n} Γ (con x) = ?
--   -- begin
--   --   x
--   -- ≈⟨ sym *-right-identity ⟩
--   --   x * (suc zero)
--   -- ≈⟨ *-cong refl (sym (varProduct-none-correct {n} Γ)) ⟩
--   --   x * ⟦ varProduct-none {n} ⟧VP Γ
--   -- ∎
-- normalize-monomial-correct Γ (var x) = ?
--   -- begin
--   --   lookup x Γ
--   -- ≈⟨ sym (trans *-comm *-right-identity) ⟩
--   --   (suc zero) * lookup x Γ
--   -- ≈⟨ *-cong refl (sym (varProduct-one-correct Γ x)) ⟩
--   --   (suc zero) * (⟦ varProduct-one x ⟧VP Γ)
--   -- ∎
-- normalize-monomial-correct Γ (l :* r) =
--   begin
--     ⟦ l ⟧M Γ * ⟦ r ⟧M Γ
--   ≈⟨ *-cong (normalize-monomial-correct Γ l) (normalize-monomial-correct Γ r) ⟩
--     ⟦ normalize-monomial l ⟧NM Γ * ⟦ normalize-monomial r ⟧NM Γ
--   ≈⟨ combine-normalized-monomial-correct Γ (normalize-monomial l) (normalize-monomial r) ⟩
--     ⟦ combine-normalized-monomial (normalize-monomial l) (normalize-monomial r) ⟧NM Γ
--   ∎

combine-snormalized-monomials : ∀ {n} → SnormalizedMonomial n → SnormalizedMonomial n → SnormalizedMonomial n
combine-snormalized-monomials (mon x [] []) (mon x₁ vs fs) = mon (x :* x₁) vs fs
combine-snormalized-monomials (mon x [] (x₁ ∷ fs)) (mon x₂ vs fs₁) = combine-snormalized-monomials (mon x [] fs) (mon x₂ vs (x₁ ∷ fs₁))
combine-snormalized-monomials (mon x (x₁ ∷ vs) fs) (mon x₂ vs₁ fs₁) = combine-snormalized-monomials (mon x vs fs) (mon x₂ (x₁ ∷ vs₁) fs₁)

combine-snormalized-monomials-correct : ∀ {n} → (Γ : Env n) → (p q : SnormalizedMonomial n) → ⟦ combine-snormalized-monomials p q ⟧SNM Γ ≡ ⟦ p ⟧SNM Γ * ⟦ q ⟧SNM Γ
combine-snormalized-monomials-correct Γ (mon x [] []) (mon x₁ vs fs) =
  begin
    (⟦ x ⟧C * ⟦ x₁ ⟧C) * (⟦ vs ⟧LV Γ * ⟦ fs ⟧LF Γ)
  ≈⟨ *-assoc ⟩
    ⟦ x ⟧C * (⟦ x₁ ⟧C * (⟦ vs ⟧LV Γ * ⟦ fs ⟧LF Γ))
  ≈⟨ *-cong (sym *-right-identity) refl ⟩
    (⟦ x ⟧C * (suc zero)) * (⟦ x₁ ⟧C * (⟦ vs ⟧LV Γ * ⟦ fs ⟧LF Γ))
  ≈⟨ *-cong (*-cong refl (sym *-right-identity)) refl ⟩
    (⟦ x ⟧C * (suc zero * suc zero)) * (⟦ x₁ ⟧C * (⟦ vs ⟧LV Γ * ⟦ fs ⟧LF Γ))
  ∎
combine-snormalized-monomials-correct Γ (mon x [] (x₁ ∷ fs)) (mon x₂ vs fs₁) =
  begin
    ⟦ combine-snormalized-monomials (mon x [] fs) (mon x₂ vs (x₁ ∷ fs₁)) ⟧SNM Γ
  ≈⟨ combine-snormalized-monomials-correct Γ (mon x [] fs) (mon x₂ vs (x₁ ∷ fs₁)) ⟩
    ⟦ mon x [] fs ⟧SNM Γ * ⟦ mon x₂ vs (x₁ ∷ fs₁) ⟧SNM Γ
  ≡⟨⟩
    (⟦ x ⟧C * (suc zero * ⟦ fs ⟧LF Γ)) * (⟦ x₂ ⟧C * (⟦ vs ⟧LV Γ * (fun (⟦ x₁ ⟧F Γ) * ⟦ fs₁ ⟧LF Γ)))
  ≈⟨ *-cong refl (*-cong refl (sym *-assoc)) ⟩
    (⟦ x ⟧C * (suc zero * ⟦ fs ⟧LF Γ)) * (⟦ x₂ ⟧C * ((⟦ vs ⟧LV Γ * fun (⟦ x₁ ⟧F Γ)) * ⟦ fs₁ ⟧LF Γ))
  ≈⟨ *-cong refl (*-cong refl (*-cong *-comm refl)) ⟩
    (⟦ x ⟧C * (suc zero * ⟦ fs ⟧LF Γ)) * (⟦ x₂ ⟧C * ((fun (⟦ x₁ ⟧F Γ) * ⟦ vs ⟧LV Γ) * ⟦ fs₁ ⟧LF Γ))
  ≈⟨ *-cong refl (*-cong refl (*-assoc)) ⟩
    (⟦ x ⟧C * (suc zero * ⟦ fs ⟧LF Γ)) * (⟦ x₂ ⟧C * (fun (⟦ x₁ ⟧F Γ) * (⟦ vs ⟧LV Γ * ⟦ fs₁ ⟧LF Γ)))
  ≈⟨ *-cong refl (sym *-assoc) ⟩
    (⟦ x ⟧C * (suc zero * ⟦ fs ⟧LF Γ)) * ((⟦ x₂ ⟧C * fun (⟦ x₁ ⟧F Γ)) * (⟦ vs ⟧LV Γ * ⟦ fs₁ ⟧LF Γ))
  ≈⟨ *-cong refl (*-cong *-comm refl) ⟩
    (⟦ x ⟧C * (suc zero * ⟦ fs ⟧LF Γ)) * ((fun (⟦ x₁ ⟧F Γ) * ⟦ x₂ ⟧C) * (⟦ vs ⟧LV Γ * ⟦ fs₁ ⟧LF Γ))
  ≈⟨ *-cong refl *-assoc ⟩
    (⟦ x ⟧C * (suc zero * ⟦ fs ⟧LF Γ)) * (fun (⟦ x₁ ⟧F Γ) * (⟦ x₂ ⟧C * (⟦ vs ⟧LV Γ * ⟦ fs₁ ⟧LF Γ)))
  ≈⟨ sym *-assoc ⟩
    ((⟦ x ⟧C * (suc zero * ⟦ fs ⟧LF Γ)) * fun (⟦ x₁ ⟧F Γ)) * (⟦ x₂ ⟧C * (⟦ vs ⟧LV Γ * ⟦ fs₁ ⟧LF Γ))
  ≈⟨ *-cong *-assoc refl ⟩
    (⟦ x ⟧C * ((suc zero * ⟦ fs ⟧LF Γ) * fun (⟦ x₁ ⟧F Γ))) * (⟦ x₂ ⟧C * (⟦ vs ⟧LV Γ * ⟦ fs₁ ⟧LF Γ))
  ≈⟨ *-cong (*-cong refl *-assoc) refl ⟩
    (⟦ x ⟧C * (suc zero * (⟦ fs ⟧LF Γ * fun (⟦ x₁ ⟧F Γ)))) * (⟦ x₂ ⟧C * (⟦ vs ⟧LV Γ * ⟦ fs₁ ⟧LF Γ))
  ≈⟨ *-cong (*-cong refl (*-cong refl *-comm)) refl ⟩
    (⟦ x ⟧C * (suc zero * (fun (⟦ x₁ ⟧F Γ) * ⟦ fs ⟧LF Γ))) * (⟦ x₂ ⟧C * (⟦ vs ⟧LV Γ * ⟦ fs₁ ⟧LF Γ))
  ∎
combine-snormalized-monomials-correct Γ (mon x (x₁ ∷ vs) fs) (mon x₂ vs₁ fs₁) =
  begin
    ⟦ combine-snormalized-monomials (mon x vs fs) (mon x₂ (x₁ ∷ vs₁) fs₁) ⟧SNM Γ
  ≈⟨ combine-snormalized-monomials-correct Γ (mon x vs fs) (mon x₂ (x₁ ∷ vs₁) fs₁) ⟩
    ⟦ mon x vs fs ⟧SNM Γ * ⟦ mon x₂ (x₁ ∷ vs₁) fs₁ ⟧SNM Γ
  ≡⟨⟩
    (⟦ x ⟧C * (⟦ vs ⟧LV Γ * ⟦ fs ⟧LF Γ)) * (⟦ x₂ ⟧C * ((lookup x₁ Γ * ⟦ vs₁ ⟧LV Γ) * ⟦ fs₁ ⟧LF Γ))
  ≈⟨ *-cong refl (*-cong refl *-assoc) ⟩
    (⟦ x ⟧C * (⟦ vs ⟧LV Γ * ⟦ fs ⟧LF Γ)) * (⟦ x₂ ⟧C * (lookup x₁ Γ * (⟦ vs₁ ⟧LV Γ * ⟦ fs₁ ⟧LF Γ)))
  ≈⟨ *-cong refl (sym *-assoc) ⟩
    (⟦ x ⟧C * (⟦ vs ⟧LV Γ * ⟦ fs ⟧LF Γ)) * ((⟦ x₂ ⟧C * lookup x₁ Γ) * (⟦ vs₁ ⟧LV Γ * ⟦ fs₁ ⟧LF Γ))
  ≈⟨ *-cong refl (*-cong *-comm refl) ⟩
    (⟦ x ⟧C * (⟦ vs ⟧LV Γ * ⟦ fs ⟧LF Γ)) * ((lookup x₁ Γ * ⟦ x₂ ⟧C) * (⟦ vs₁ ⟧LV Γ * ⟦ fs₁ ⟧LF Γ))
  ≈⟨ *-cong refl *-assoc ⟩
    (⟦ x ⟧C * (⟦ vs ⟧LV Γ * ⟦ fs ⟧LF Γ)) * (lookup x₁ Γ * (⟦ x₂ ⟧C * (⟦ vs₁ ⟧LV Γ * ⟦ fs₁ ⟧LF Γ)))
  ≈⟨ sym *-assoc ⟩
    ((⟦ x ⟧C * (⟦ vs ⟧LV Γ * ⟦ fs ⟧LF Γ)) * lookup x₁ Γ) * (⟦ x₂ ⟧C * (⟦ vs₁ ⟧LV Γ * ⟦ fs₁ ⟧LF Γ))
  ≈⟨ *-cong *-assoc refl ⟩
    (⟦ x ⟧C * ((⟦ vs ⟧LV Γ * ⟦ fs ⟧LF Γ) * lookup x₁ Γ)) * (⟦ x₂ ⟧C * (⟦ vs₁ ⟧LV Γ * ⟦ fs₁ ⟧LF Γ))
  ≈⟨ *-cong (*-cong refl *-comm) refl ⟩
    (⟦ x ⟧C * (lookup x₁ Γ * (⟦ vs ⟧LV Γ * ⟦ fs ⟧LF Γ))) * (⟦ x₂ ⟧C * (⟦ vs₁ ⟧LV Γ * ⟦ fs₁ ⟧LF Γ))
  ≈⟨ *-cong (*-cong refl (sym *-assoc)) refl ⟩
    (⟦ x ⟧C * ((lookup x₁ Γ * ⟦ vs ⟧LV Γ) * ⟦ fs ⟧LF Γ)) * (⟦ x₂ ⟧C * (⟦ vs₁ ⟧LV Γ * ⟦ fs₁ ⟧LF Γ))
  ∎

-- TODO: Apply this
snormalize-monomial : ∀ {n} → Monomial n → SnormalizedMonomial n
snormalize-monomial (con x) = mon x [] []
snormalize-monomial (var x) = mon (:suc :zero) (x ∷ []) []
snormalize-monomial (fun x) = mon (:suc :zero) [] (x ∷ [])
snormalize-monomial (x :* x₁) = combine-snormalized-monomials (snormalize-monomial x) (snormalize-monomial x₁)

snormalize-monomial-correct : ∀ {n} → (Γ : Env n) → (p : Monomial n) → ⟦ snormalize-monomial p ⟧SNM Γ ≡ ⟦ p ⟧M Γ
snormalize-monomial-correct Γ (con x) =
  begin
    ⟦ x ⟧C * (suc zero * suc zero)
  ≈⟨ *-cong refl *-right-identity ⟩
    ⟦ x ⟧C * (suc zero)
  ≈⟨ *-right-identity ⟩
    ⟦ x ⟧C
  ∎
snormalize-monomial-correct Γ (var x) =
  begin
    suc zero * (lookup x Γ * suc zero * suc zero)
  ≈⟨ *-comm ⟩
    (lookup x Γ * suc zero * suc zero) * suc zero
  ≈⟨ *-right-identity ⟩
    (lookup x Γ * suc zero * suc zero)
  ≈⟨ *-right-identity ⟩
    (lookup x Γ * suc zero)
  ≈⟨ *-right-identity ⟩
    lookup x Γ
  ∎
snormalize-monomial-correct Γ (fun x) =
  begin
    suc zero * (suc zero * (fun (⟦ x ⟧F Γ) * suc zero))
  ≈⟨ *-comm ⟩
    (suc zero * (fun (⟦ x ⟧F Γ) * suc zero)) * suc zero
  ≈⟨ *-right-identity ⟩
    (suc zero * (fun (⟦ x ⟧F Γ) * suc zero))
  ≈⟨ *-comm ⟩
    (fun (⟦ x ⟧F Γ) * suc zero) * suc zero
  ≈⟨ *-right-identity ⟩
    (fun (⟦ x ⟧F Γ) * suc zero)
  ≈⟨ *-right-identity ⟩
    fun (⟦ x ⟧F Γ)
  ∎
snormalize-monomial-correct Γ (x :* x₁) =
  begin
    ⟦ combine-snormalized-monomials (snormalize-monomial x) (snormalize-monomial x₁) ⟧SNM Γ
  ≈⟨ combine-snormalized-monomials-correct Γ (snormalize-monomial x) (snormalize-monomial x₁) ⟩
    ⟦ snormalize-monomial x ⟧SNM Γ * ⟦ snormalize-monomial x₁ ⟧SNM Γ
  ≈⟨ *-cong (snormalize-monomial-correct Γ x) (snormalize-monomial-correct Γ x₁) ⟩
    ⟦ x ⟧M Γ * ⟦ x₁ ⟧M Γ
  ∎

-- TODO: Apply this
sort-snormalized-monomial : ∀ {n} → SnormalizedMonomial n → SnormalizedMonomial n
sort-snormalized-monomial (mon x vs fs) = mon x (sort-lv vs) (sort-lf fs)

sort-snormalized-monomial-correct : ∀ {n} → (Γ : Env n) → (p : SnormalizedMonomial n) → ⟦ sort-snormalized-monomial p ⟧SNM Γ ≡ ⟦ p ⟧SNM Γ
sort-snormalized-monomial-correct Γ (mon x vs fs) = *-cong refl (*-cong (sort-lv-correct Γ vs) (sort-lf-correct Γ fs))

------------------------------------------------------------------------
-- Normalize constants

data NormalizedConstant : Set where
  :zero : NormalizedConstant
  :suc : NormalizedConstant → NormalizedConstant

:⟦_⟧NC : ∀ {n} → NormalizedConstant → :Expr n
:⟦ :zero ⟧NC = :zero
:⟦ :suc x ⟧NC = :suc :⟦ x ⟧NC

⟦_⟧NC : ∀ {n} → NormalizedConstant → Env n → Expr
⟦ x ⟧NC = ⟦ :⟦ x ⟧NC ⟧
-- ⟦ :zero ⟧NC Γ = zero
-- ⟦ :suc x ⟧NC Γ = suc ⟦ x ⟧NC Γ

_C+_ : NormalizedConstant → NormalizedConstant → NormalizedConstant
_C+_ :zero y = y
_C+_ (:suc x) y = :suc (x C+ y)

C+-correct : ∀ {n} → (Γ : Env n) → (p q : NormalizedConstant) → ⟦ p C+ q ⟧NC Γ ≡ ⟦ p ⟧NC Γ + ⟦ q ⟧NC Γ
C+-correct Γ :zero q =
  begin
    ⟦ q ⟧NC Γ
  ≈⟨ sym +-right-identity ⟩
    ⟦ q ⟧NC Γ + zero
  ≈⟨ +-comm ⟩
    zero + ⟦ q ⟧NC Γ
  ∎
C+-correct Γ (:suc p) q =
  begin
    suc (⟦ p C+ q ⟧NC Γ)
  ≈⟨ suc-cong (C+-correct Γ p q) ⟩
    suc (⟦ p ⟧NC Γ + ⟦ q ⟧NC Γ)
  ≈⟨ sym suc-pull ⟩
    suc (⟦ p ⟧NC Γ) + ⟦ q ⟧NC Γ
  ∎

_C*_ : NormalizedConstant → NormalizedConstant → NormalizedConstant
:zero C* y = :zero
:suc x C* y = y C+ x C* y

C*-correct : ∀ {n} → (Γ : Env n) → (p q : NormalizedConstant) → ⟦ p C* q ⟧NC Γ ≡ ⟦ p ⟧NC Γ * ⟦ q ⟧NC Γ
C*-correct Γ :zero y =
  begin
    zero
  ≈⟨ sym *-right-zero ⟩
    ⟦ y ⟧NC Γ * zero
  ≈⟨ *-comm ⟩
    zero * ⟦ y ⟧NC Γ
  ∎
C*-correct Γ (:suc x) y =
  begin
    ⟦ y C+ x C* y ⟧NC Γ
  ≈⟨ C+-correct Γ y (x C* y) ⟩
    ⟦ y ⟧NC Γ + ⟦ x C* y ⟧NC Γ
  ≈⟨ +-cong refl (C*-correct Γ x y) ⟩
    ⟦ y ⟧NC Γ + ⟦ x ⟧NC Γ * ⟦ y ⟧NC Γ
  ≈⟨ sym suc-* ⟩
    suc (⟦ x ⟧NC Γ) * ⟦ y ⟧NC Γ
  ∎

-- data NormalizedMonomial (n : ℕ) : Set ℓ₁ where
--   con : NormalizedConstant → NormalizedMonomial n
--   _:*_ : :Expr n → NormalizedMonomial n → NormalizedMonomial n
data NormalizedMonomial (n : ℕ) : Set ℓ₁ where
  mon : NormalizedConstant → (vs : List (Fin n)) → (fs : List (:Fun n)) → NormalizedMonomial n

:⟦_⟧NM : ∀ {n} → NormalizedMonomial n → :Expr n
:⟦ mon x vs fs ⟧NM = :⟦ x ⟧NC :* (:⟦ vs ⟧LV :* :⟦ fs ⟧LF)

⟦_⟧NM : ∀ {n} → NormalizedMonomial n → Env n → Expr
⟦ x ⟧NM = ⟦ :⟦ x ⟧NM ⟧

normalize-constant : Constant → NormalizedConstant
normalize-constant :zero = :zero
normalize-constant (:suc x) = :suc (normalize-constant x)
normalize-constant (x :+ x₁) = (normalize-constant x) C+ (normalize-constant x₁)
normalize-constant (x :* x₁) = (normalize-constant x) C* (normalize-constant x₁)

normalize-constant-correct : ∀ {n} → (Γ : Env n) → (p : Constant) → ⟦ normalize-constant p ⟧NC Γ ≡ ⟦ p ⟧C
normalize-constant-correct Γ :zero = refl
normalize-constant-correct Γ (:suc p) = suc-cong (normalize-constant-correct Γ p)
normalize-constant-correct Γ (p :+ p₁) =
  begin
    ⟦ normalize-constant p C+ normalize-constant p₁ ⟧NC Γ
  ≈⟨ C+-correct Γ (normalize-constant p) (normalize-constant p₁) ⟩
    ⟦ normalize-constant p ⟧NC Γ + ⟦ normalize-constant p₁ ⟧NC Γ
  ≈⟨ +-cong (normalize-constant-correct Γ p) (normalize-constant-correct Γ p₁) ⟩
    ⟦ p ⟧C + ⟦ p₁ ⟧C
  ∎
normalize-constant-correct Γ (p :* p₁) =
  begin
    ⟦ normalize-constant p C* normalize-constant p₁ ⟧NC Γ
  ≈⟨ C*-correct Γ (normalize-constant p) (normalize-constant p₁) ⟩
    ⟦ normalize-constant p ⟧NC Γ * ⟦ normalize-constant p₁ ⟧NC Γ
  ≈⟨ *-cong (normalize-constant-correct Γ p) (normalize-constant-correct Γ p₁) ⟩
    ⟦ p ⟧C * ⟦ p₁ ⟧C
  ∎

normalize-constants : ∀ {n} → SnormalizedMonomial n → NormalizedMonomial n
normalize-constants (mon x vs fs) = mon (normalize-constant x) vs fs

normalize-constants-correct : ∀ {n} → (Γ : Env n) → (p : SnormalizedMonomial n) → ⟦ normalize-constants p ⟧NM Γ ≡ ⟦ p ⟧SNM Γ
normalize-constants-correct Γ (mon x vs fs) = *-cong (normalize-constant-correct Γ x) refl
-- normalize-constants-correct Γ (con x) = normalize-constant-correct x
-- normalize-constants-correct Γ (var x) = {!!}
-- normalize-constants-correct Γ (fun f) = {!!}
-- normalize-constants-correct Γ (x :* p) = *-cong refl (normalize-constants-correct Γ p)

data RightLeaningSumOfNormalizedMonomials : (n : ℕ) → Set ℓ₁ where
  nil : ∀ {n} → RightLeaningSumOfNormalizedMonomials n
  _:+_ : ∀ {n} → NormalizedMonomial n → RightLeaningSumOfNormalizedMonomials n → RightLeaningSumOfNormalizedMonomials n


:⟦_⟧RLSNM : ∀ {n} → RightLeaningSumOfNormalizedMonomials n → :Expr n
:⟦ nil ⟧RLSNM = :zero
:⟦ x :+ x₁ ⟧RLSNM = :⟦ x ⟧NM :+ :⟦ x₁ ⟧RLSNM

⟦_⟧RLSNM : ∀ {n} → RightLeaningSumOfNormalizedMonomials n → Env n → Expr
⟦ x ⟧RLSNM = ⟦ :⟦ x ⟧RLSNM ⟧

-- TODO: Apply this
normalize-monomials : ∀ {n} → RightLeaningSumOfMonomials n → RightLeaningSumOfNormalizedMonomials n
normalize-monomials nil = nil
normalize-monomials (x :+ p) = normalize-constants (snormalize-monomial x) :+ normalize-monomials p

normalize-monomials-correct : ∀ {n} → (Γ : Env n) → (p : RightLeaningSumOfMonomials n) → ⟦ normalize-monomials p ⟧RLSNM Γ ≡ ⟦ p ⟧RLSM Γ
normalize-monomials-correct Γ nil = refl
normalize-monomials-correct Γ (x :+ x₁) =
  begin
    ⟦ normalize-constants (snormalize-monomial x) ⟧NM Γ + ⟦ normalize-monomials x₁ ⟧RLSNM Γ
  ≈⟨ +-cong (normalize-constants-correct Γ (snormalize-monomial x)) (normalize-monomials-correct Γ x₁) ⟩
    ⟦ snormalize-monomial x ⟧SNM Γ + ⟦ x₁ ⟧RLSM Γ
  ≈⟨ +-cong (snormalize-monomial-correct Γ x) refl ⟩
    ⟦ x ⟧M Γ + ⟦ x₁ ⟧RLSM Γ
  ∎

-- normalize-monomials-correct Γ nil = refl
-- normalize-monomials-correct Γ (x :+ xs) =
--   begin
--     ⟦ x ⟧M Γ + ⟦ xs ⟧RLSM Γ
--   ≈⟨ +-cong (normalize-monomial-correct Γ x) (normalize-monomials-correct Γ xs) ⟩
--     ⟦ normalize-monomial x ⟧SNM Γ + ⟦ normalize-monomials xs ⟧RLSNM Γ
--   ≈⟨ +-cong (normalize-constants-correct Γ (normalize-monomial x)) refl ⟩
--     ⟦ normalize-constants (normalize-monomial x) ⟧NM Γ + ⟦ normalize-monomials xs ⟧RLSNM Γ
--   ∎
-- +-cong (normalize-monomial-correct Γ x) (normalize-monomials-correct Γ xs)

------------------------------------------------------------------------
-- Throw out zero monomials

is-zero? : ∀ {n} → (p : NormalizedMonomial n) → Maybe (∀ Γ → ⟦ p ⟧NM Γ ≡ zero)
is-zero? (mon (:suc x) vs fs) = nothing
is-zero? (mon :zero vs fs) = just (λ Γ → begin
    zero * (⟦ vs ⟧LV Γ * ⟦ fs ⟧LF Γ)
  ≈⟨ *-comm ⟩
    (⟦ vs ⟧LV Γ * ⟦ fs ⟧LF Γ) * zero
  ≈⟨ *-right-zero ⟩
    zero
  ∎)
-- is-zero (con :zero) = just (λ Γ → refl)
-- is-zero (con (:suc x)) = nothing
-- is-zero (x :* p) with is-zero p
-- is-zero (x :* p) | just prf = just (λ Γ → begin
--     ⟦ x ⟧ Γ * ⟦ p ⟧NM Γ
--   ≈⟨ *-cong refl (prf Γ) ⟩
--     ⟦ x ⟧ Γ * zero
--   ≈⟨ *-right-zero ⟩
--     zero
--   ∎)
-- is-zero (x :* p) | nothing = nothing

-- TODO: Apply this!
throw-out-zeros : ∀ {n} → RightLeaningSumOfNormalizedMonomials n → RightLeaningSumOfNormalizedMonomials n
throw-out-zeros nil = nil
throw-out-zeros (x :+ x₁) with is-zero? x
throw-out-zeros (x :+ x₂) | just x₁ = throw-out-zeros x₂
throw-out-zeros (x :+ x₁) | nothing = x :+ throw-out-zeros x₁

throw-out-zeros-correct : ∀ {n} → (Γ : Env n) → (p : RightLeaningSumOfNormalizedMonomials n) → ⟦ throw-out-zeros p ⟧RLSNM Γ ≡ ⟦ p ⟧RLSNM Γ
throw-out-zeros-correct Γ nil = refl
throw-out-zeros-correct Γ (x :+ p) with is-zero? x
throw-out-zeros-correct Γ (x :+ p) | just prf =
  begin
    ⟦ throw-out-zeros p ⟧RLSNM Γ
  ≈⟨ throw-out-zeros-correct Γ p ⟩
    ⟦ p ⟧RLSNM Γ
  ≈⟨ sym +-right-identity ⟩
    ⟦ p ⟧RLSNM Γ + zero
  ≈⟨ +-comm ⟩
    zero + ⟦ p ⟧RLSNM Γ
  ≈⟨ +-cong (sym (prf Γ)) refl ⟩
    ⟦ x ⟧NM Γ + ⟦ p ⟧RLSNM Γ
  ≡⟨⟩
    ⟦ x :+ p ⟧RLSNM Γ
  ∎
throw-out-zeros-correct Γ (x :+ p) | nothing = +-cong refl (throw-out-zeros-correct Γ p)

-- mutual
--   no-zeros' : ∀ {n} → (c : Expr) → Dec (c ≡ zero) → VarProduct n → RightLeaningSumOfNormalizedMonomials n → L.List (NormalizedMonomial n)
--   no-zeros' c (yes prf) x p = no-zeros p
--   no-zeros' c (no ¬prf) x p = ? -- (c :* x) L.∷ no-zeros p

--   no-zeros : ∀ {n} → RightLeaningSumOfNormalizedMonomials n → L.List (NormalizedMonomial n)
--   no-zeros nil = L.[]
--   no-zeros (c :* x :+ p) = ? -- no-zeros' c (c ≟0) x p

-- to-sum : ∀ {n} → L.List (NormalizedMonomial n) → RightLeaningSumOfNormalizedMonomials n
-- to-sum L.[] = nil
-- to-sum (x L.∷ xs) = x :+ to-sum xs

-- throw-out-zeros : ∀ {n} → RightLeaningSumOfNormalizedMonomials n → RightLeaningSumOfNormalizedMonomials n
-- throw-out-zeros p = to-sum (no-zeros p)

-- mutual
--   throw-out-zeros-correct' : ∀ {n}
--                           → (Γ : Env n)
--                           → (c : Constant)
--                           → (d : Dec (c P≡ :zero))
--                           → ((c ≟0) P≡ d)
--                           → (x : VarProduct n)
--                           → (p : RightLeaningSumOfNormalizedMonomials n)
--                           → ⟦ (c :* x) :+ p ⟧RLSNM Γ ≡ ⟦ throw-out-zeros ((c :* x) :+ p) ⟧RLSNM Γ
--   throw-out-zeros-correct' Γ c (yes prf) prf2 x p rewrite prf2 =
--     begin
--       c * (⟦ x ⟧VP Γ) + ⟦ p ⟧RLSNM Γ
--     ≈⟨ +-cong (*-cong prf refl) refl ⟩
--       zero * (⟦ x ⟧VP Γ) + ⟦ p ⟧RLSNM Γ
--     ≈⟨ +-cong *-comm refl ⟩
--       (⟦ x ⟧VP Γ) * zero + ⟦ p ⟧RLSNM Γ
--     ≈⟨ +-cong *-right-zero refl ⟩
--       zero + ⟦ p ⟧RLSNM Γ
--     ≈⟨ +-comm ⟩
--       ⟦ p ⟧RLSNM Γ + zero
--     ≈⟨ +-right-identity ⟩
--       ⟦ p ⟧RLSNM Γ
--     ≈⟨ throw-out-zeros-correct Γ p ⟩
--       ⟦ to-sum (no-zeros p) ⟧RLSNM Γ
--     ∎
--   throw-out-zeros-correct' Γ c (no ¬prf) prf2 x p rewrite prf2 =
--     begin
--       c * (⟦ x ⟧VP Γ) + ⟦ p ⟧RLSNM Γ
--     ≈⟨ +-cong refl (throw-out-zeros-correct Γ p) ⟩
--       c * (⟦ x ⟧VP Γ) + ⟦ to-sum (no-zeros p) ⟧RLSNM Γ
--     ∎

--   throw-out-zeros-correct : ∀ {n} → (Γ : Env n) → (p : RightLeaningSumOfNormalizedMonomials n) → ⟦ p ⟧RLSNM Γ ≡ ⟦ throw-out-zeros p ⟧RLSNM Γ
--   throw-out-zeros-correct Γ nil = refl
--   throw-out-zeros-correct Γ (c :* x :+ p) = throw-out-zeros-correct' Γ c (c ≟0) Prefl x p

------------------------------------------------------------------------
-- Sorting

-- infixr 6 _∧_
-- _∧_ : Bool → Bool → Bool
-- true ∧ true = true
-- _ ∧ _ = false

-- exprEq : ∀ {n} → :Expr n → :Expr n → Bool
-- exprEq a b = termEq (quoteTerm a) (quoteTerm b)

-- exprLt : ∀ {n} → :Expr n → :Expr n → Bool
-- exprLt a b = termLt (quoteTerm a) (quoteTerm b)

-- -- (Mostly) generated using https://github.com/SuprDewd/generate-agda-comparators

-- mutual

--   -- normalizedConstantEq : NormalizedConstant → NormalizedConstant → Bool
--   -- normalizedConstantEq :zero :zero = true
--   -- normalizedConstantEq (:suc l1) (:suc r1) = normalizedConstantEq l1 r1
--   -- normalizedConstantEq _ _ = false

--   normalizedMonomialEq : ∀ {n} → NormalizedMonomial n → NormalizedMonomial n → Bool
--   -- normalizedMonomialEq (con l1) (con r1) = normalizedConstantEq l1 r1
--   normalizedMonomialEq (con l1) (con r1) = true -- Monomials are equal if everything but their constants are equal
--   normalizedMonomialEq (_:*_ l1 l2) (_:*_ r1 r2) = exprEq l1 r1 Translate.Solver.Reflection.∧ normalizedMonomialEq l2 r2
--   normalizedMonomialEq _ _ = false

-- isLt : ∀ {n} → Vec Bool n → Vec Bool n → Bool
-- isLt [] [] = false
-- isLt (true ∷ xs) (_ ∷ ys) = isLt xs ys
-- isLt (false ∷ xs) (y ∷ ys) = y

-- mutual

--   -- normalizedConstantLt : NormalizedConstant → NormalizedConstant → Bool
--   -- normalizedConstantLt :zero :zero = false
--   -- normalizedConstantLt (:suc l1) (:suc r1) = isLt (normalizedConstantEq l1 r1 ∷ []) (normalizedConstantLt l1 r1 ∷ [])
--   -- normalizedConstantLt :zero (:suc _) = true
--   -- normalizedConstantLt _ _ = false

--   normalizedMonomialLt : ∀ {n} → NormalizedMonomial n → NormalizedMonomial n → Bool
--   normalizedMonomialLt (con l1) (con r1) = false -- isLt (normalizedConstantEq l1 r1 ∷ []) (normalizedConstantLt l1 r1 ∷ [])
--   normalizedMonomialLt (_:*_ l1 l2) (_:*_ r1 r2) = isLt (exprEq l1 r1 ∷ normalizedMonomialEq l2 r2 ∷ []) (exprLt l1 r1 ∷ normalizedMonomialLt l2 r2 ∷ [])
--   normalizedMonomialLt (con _) (_:*_ _ _) = true
--   normalizedMonomialLt _ _ = false


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

open import Data.Fin.Properties using () renaming (_≟_ to _F≟_)
open import Data.List.Properties

lv-eq : ∀ {n} → (p q : List (Fin n)) → Dec (p P≡ q)
lv-eq [] [] = yes Prefl
lv-eq [] (x ∷ b) = no (λ ())
lv-eq (x ∷ a) [] = no (λ ())
lv-eq (x ∷ a) (x₁ ∷ b) with x F≟ x₁ | lv-eq a b
lv-eq (x ∷ a) (.x ∷ .a) | yes Prefl | yes Prefl = yes Prefl
lv-eq (x ∷ a) (x₁ ∷ b) | yes p | no ¬p = no (λ p₂ → ¬p (proj₂ (∷-injective p₂)))
lv-eq (x ∷ a) (x₁ ∷ b) | no ¬p | yes p = no (λ p₂ → ¬p (proj₁ (∷-injective p₂)))
lv-eq (x ∷ a) (x₁ ∷ b) | no ¬p | no ¬p₁ = no (λ p₂ → ¬p₁ (proj₂ (∷-injective p₂)))

lv-lt : ∀ {n} → (p q : List (Fin n)) → Bool
lv-lt [] [] = false
lv-lt [] (x ∷ b) = true
lv-lt (x ∷ a) [] = false
lv-lt (x ∷ a) (x₁ ∷ b) with finEq x x₁
lv-lt (x ∷ a) (x₁ ∷ b) | no _ = finLt x x₁
lv-lt (x ∷ a) (x₁ ∷ b) | yes _ = lv-lt a b

lf-eq : ∀ {n} → (p q : List (:Fun n)) → Dec (p P≡ q)
lf-eq [] [] = yes Prefl
lf-eq [] (x ∷ q) = no (λ ())
lf-eq (x ∷ p) [] = no (λ ())
lf-eq (x ∷ p) (x₁ ∷ q) with :FunEq x x₁ | lf-eq p q
lf-eq (x ∷ p) (.x ∷ .p) | yes Prefl | yes Prefl = yes Prefl
lf-eq (x ∷ p) (.x ∷ q) | yes Prefl | no ¬p = no (λ x₁ → ¬p (proj₂ (∷-injective x₁)))
lf-eq (x ∷ p) (x₁ ∷ q) | no ¬p | b = no (λ x₂ → ¬p (proj₁ (∷-injective x₂)))


lf-lt : ∀ {n} → (p q : List (:Fun n)) → Bool
lf-lt [] [] = false
lf-lt [] (x ∷ b) = true
lf-lt (x ∷ a) [] = false
lf-lt (x ∷ a) (x₁ ∷ b) = isLt (toBool (:FunEq x x₁) ∷ toBool (lf-eq a b) ∷ [])
                              (:FunLt x x₁ ∷ lf-lt a b ∷ [])

normalizedMonomialLt : ∀ {n} → (p q : NormalizedMonomial n) → Bool
normalizedMonomialLt (mon x vs fs) (mon x₁ vs₁ fs₁) = isLt (toBool (lv-eq vs vs₁) ∷ toBool (lf-eq fs fs₁) ∷ [])
                                                           (lv-lt vs vs₁ ∷ lf-lt fs fs₁ ∷ [])

insert : ∀ {n} → NormalizedMonomial n → RightLeaningSumOfNormalizedMonomials n → RightLeaningSumOfNormalizedMonomials n
insert x nil = x :+ nil
insert x (x₁ :+ xs) with normalizedMonomialLt x x₁
insert x (x₁ :+ xs) | true = x :+ (x₁ :+ xs)
insert x (x₁ :+ xs) | false = x₁ :+ insert x xs

insert-correct : ∀ {n} → (Γ : Env n) → (x : NormalizedMonomial n) → (xs : RightLeaningSumOfNormalizedMonomials n) → ⟦ insert x xs ⟧RLSNM Γ ≡ ⟦ x ⟧NM Γ + ⟦ xs ⟧RLSNM Γ
insert-correct Γ x nil = refl
insert-correct Γ x (x₁ :+ xs) with normalizedMonomialLt x x₁
insert-correct Γ x (x₁ :+ xs) | true = refl
insert-correct Γ x (x₁ :+ xs) | false =
  begin
    ⟦ x₁ :+ insert x xs ⟧RLSNM Γ
  ≈⟨ +-cong refl (insert-correct Γ x xs) ⟩
    ⟦ x₁ ⟧NM Γ + (⟦ x ⟧NM Γ + ⟦ xs ⟧RLSNM Γ)
  ≈⟨ sym +-assoc ⟩
    (⟦ x₁ ⟧NM Γ + ⟦ x ⟧NM Γ) + ⟦ xs ⟧RLSNM Γ
  ≈⟨ +-cong +-comm refl ⟩
    (⟦ x ⟧NM Γ + ⟦ x₁ ⟧NM Γ) + ⟦ xs ⟧RLSNM Γ
  ≈⟨ +-assoc ⟩
    ⟦ x ⟧NM Γ + (⟦ x₁ ⟧NM Γ + ⟦ xs ⟧RLSNM Γ)
  ∎

-- -- insert-correct Γ y nil = refl
-- -- insert-correct Γ (c₁ :* x₁) (c₂ :* x₂ :+ xs) with VarProductComparison.compare x₁ x₂
-- -- insert-correct Γ (c₁ :* x₁) (c₂ :* x₂ :+ xs) | VarProductComparison.less = refl
-- -- insert-correct Γ (c₁ :* x₁) (c₂ :* x₂ :+ xs) | VarProductComparison.equal = refl
-- -- insert-correct Γ (c₁ :* x₁) (c₂ :* x₂ :+ xs) | VarProductComparison.greater =
-- --   begin
-- --     c₁ * ⟦ x₁ ⟧VP Γ + (c₂ * ⟦ x₂ ⟧VP Γ + ⟦ xs ⟧RLSNM Γ)
-- --   ≈⟨ sym +-assoc ⟩
-- --     (c₁ * ⟦ x₁ ⟧VP Γ + c₂ * ⟦ x₂ ⟧VP Γ) + ⟦ xs ⟧RLSNM Γ
-- --   ≈⟨ +-cong +-comm refl ⟩
-- --     (c₂ * ⟦ x₂ ⟧VP Γ + c₁ * ⟦ x₁ ⟧VP Γ) + ⟦ xs ⟧RLSNM Γ
-- --   ≈⟨ +-assoc ⟩
-- --     c₂ * ⟦ x₂ ⟧VP Γ + (c₁ * ⟦ x₁ ⟧VP Γ + ⟦ xs ⟧RLSNM Γ)
-- --   ≡⟨⟩
-- --     c₂ * (⟦ x₂ ⟧VP Γ) + (⟦ (c₁ :* x₁) ⟧NM Γ + ⟦ xs ⟧RLSNM Γ)
-- --   ≈⟨ +-cong refl (insert-correct Γ (c₁ :* x₁) xs) ⟩
-- --     c₂ * (⟦ x₂ ⟧VP Γ) + ⟦ insert (c₁ :* x₁) xs ⟧RLSNM Γ
-- --   ∎

-- TODO: Apply this
sort : ∀ {n} → RightLeaningSumOfNormalizedMonomials n → RightLeaningSumOfNormalizedMonomials n
sort nil = nil
sort (x :+ xs) = insert x (sort xs)

sort-correct : ∀ {n} → (Γ : Env n) → (p : RightLeaningSumOfNormalizedMonomials n) → ⟦ sort p ⟧RLSNM Γ ≡ ⟦ p ⟧RLSNM Γ
sort-correct Γ nil = refl
sort-correct Γ (x :+ xs) =
  begin
    ⟦ insert x (sort xs) ⟧RLSNM Γ
  ≈⟨ insert-correct Γ x (sort xs) ⟩
    ⟦ x ⟧NM Γ + ⟦ sort xs ⟧RLSNM Γ
  ≈⟨ +-cong refl (sort-correct Γ xs) ⟩
    ⟦ x ⟧NM Γ + ⟦ xs ⟧RLSNM Γ
  ∎

------------------------------------------------------------------------
-- Squashing

squash' : ∀ {n} → NormalizedConstant → List (Fin n) → List (:Fun n) → RightLeaningSumOfNormalizedMonomials n → RightLeaningSumOfNormalizedMonomials n
squash' c x f nil = mon c x f :+ nil -- c :* x :+ nil
squash' c₁ x₁ f₁ (mon c₂ x₂ f₂ :+ xs) with lv-eq x₁ x₂ | lf-eq f₁ f₂
squash' c₁ x₁ f₁ (mon c₂ x₂ f₂ :+ xs) | yes p | yes p₁ = squash' (c₁ C+ c₂) x₁ f₁ xs
squash' c₁ x₁ f₁ (mon c₂ x₂ f₂ :+ xs) | yes p | no ¬p = mon c₁ x₁ f₁ :+ squash' c₂ x₂ f₂ xs
squash' c₁ x₁ f₁ (mon c₂ x₂ f₂ :+ xs) | no ¬p | b = mon c₁ x₁ f₁ :+ squash' c₂ x₂ f₂ xs

-- {!!} -- with VarProductComparison.decEq x₁ x₂
-- ... | yes p = squash' (c₁ + c₂) x₁ xs  -- XXX: How can we normalize c₁ + c₂???
-- ... | no ¬p = c₁ :* x₁ :+ squash' c₂ x₂ xs

squash'-correct : ∀ {n} → (Γ : Env n) → (c : NormalizedConstant) → (x : List (Fin n)) → (f : List (:Fun n)) → (xs : RightLeaningSumOfNormalizedMonomials n) → ⟦ squash' c x f xs ⟧RLSNM Γ ≡ ⟦ c ⟧NC Γ * (⟦ x ⟧LV Γ * ⟦ f ⟧LF Γ) + ⟦ xs ⟧RLSNM Γ
squash'-correct Γ c x f nil = refl
squash'-correct Γ c₁ x₁ f₁ (mon c₂ x₂ f₂ :+ xs) with lv-eq x₁ x₂ | lf-eq f₁ f₂
squash'-correct Γ c₁ x₁ f₁ (mon c₂ .x₁ .f₁ :+ xs) | yes Prefl | yes Prefl =
  begin
    ⟦ squash' (c₁ C+ c₂) x₁ f₁ xs ⟧RLSNM Γ
  ≈⟨ squash'-correct Γ (c₁ C+ c₂) x₁ f₁ xs ⟩
    ⟦ c₁ C+ c₂ ⟧NC Γ * (⟦ x₁ ⟧LV Γ * ⟦ f₁ ⟧LF Γ) + ⟦ xs ⟧RLSNM Γ
  ≈⟨ +-cong (*-cong (C+-correct Γ c₁ c₂) refl) refl ⟩
    (⟦ c₁ ⟧NC Γ + ⟦ c₂ ⟧NC Γ) * (⟦ x₁ ⟧LV Γ * ⟦ f₁ ⟧LF Γ) + ⟦ xs ⟧RLSNM Γ
  ≈⟨ +-cong distribʳ-*-+ refl ⟩
    (⟦ c₁ ⟧NC Γ * (⟦ x₁ ⟧LV Γ * ⟦ f₁ ⟧LF Γ) + ⟦ c₂ ⟧NC Γ * (⟦ x₁ ⟧LV Γ * ⟦ f₁ ⟧LF Γ)) + ⟦ xs ⟧RLSNM Γ
  ≈⟨ +-assoc ⟩
    ⟦ c₁ ⟧NC Γ * (⟦ x₁ ⟧LV Γ * ⟦ f₁ ⟧LF Γ) + (⟦ c₂ ⟧NC Γ * (⟦ x₁ ⟧LV Γ * ⟦ f₁ ⟧LF Γ) + ⟦ xs ⟧RLSNM Γ)
  ∎
squash'-correct Γ c₁ x₁ f₁ (mon c₂ x₂ f₂ :+ xs) | yes p | no ¬p = +-cong refl (squash'-correct Γ c₂ x₂ f₂ xs)
squash'-correct Γ c₁ x₁ f₁ (mon c₂ x₂ f₂ :+ xs) | no ¬p | b = +-cong refl (squash'-correct Γ c₂ x₂ f₂ xs)

-- TODO: Apply this
squash : ∀ {n} → RightLeaningSumOfNormalizedMonomials n → RightLeaningSumOfNormalizedMonomials n
squash nil = nil
squash (mon c x f :+ xs) = squash' c x f xs

-- open import Translate.Support
-- open import Data.Product

-- postulate
--   -- XXX: THIS MAY NOT BE TRUE WHEN COINDUCTION IS INVOLVED!
--   quote-correct : ∀ {n} {x y : :Expr n} → quoteTerm x P≡ quoteTerm y → x P≡ y

-- exprEq' : ∀ {n} → (x y : :Expr n) → Maybe (x P≡ y)
-- exprEq' {n} x y with (quoteTerm x) Term≟ (quoteTerm y)
-- exprEq' x y | yes p = {!!}
-- exprEq' x y | no ¬p = {!!}

-- try-combine : ∀ {n} → (l r : NormalizedMonomial n) → Maybe (Σ (NormalizedMonomial n) (λ p → (∀ Γ → ⟦ l ⟧NM Γ + ⟦ r ⟧NM Γ ≡ ⟦ p ⟧NM Γ)))
-- try-combine (con x) (con x₁) = just (con (x C+ x₁) , (λ Γ → C+-correct x x₁))
-- try-combine (x₁ :* l) (x₂ :* r) with (quoteTerm x₁) Term≟ (quoteTerm x₂) | try-combine l r
-- try-combine {n} (x₁ :* l) (x₂ :* r) | yes eq | just (xs , prf) = just (x₁ :* xs , (λ Γ → begin
--       ⟦ x₁ ⟧ Γ * ⟦ l ⟧NM Γ + ⟦ x₂ ⟧ Γ * ⟦ r ⟧NM Γ
--     ≈⟨ +-cong refl {!quote-correct {n} {x₁} {x₂} eq !} ⟩
--       ⟦ x₁ ⟧ Γ * ⟦ l ⟧NM Γ + ⟦ x₁ ⟧ Γ * ⟦ r ⟧NM Γ
--     ≈⟨ sym (distribˡ-*-+) ⟩
--       ⟦ x₁ ⟧ Γ * (⟦ l ⟧NM Γ + ⟦ r ⟧NM Γ)
--     ≈⟨ *-cong refl (prf Γ) ⟩
--       ⟦ x₁ ⟧ Γ * ⟦ xs ⟧NM Γ
--     ∎
--   ))
-- try-combine (x :* l) (x₁ :* r) | _ | nothing = nothing
-- try-combine (x₁ :* l) (x₂ :* r) | no _ | _ = nothing
-- try-combine _ _ = nothing

squash-correct : ∀ {n} → (Γ : Env n) → (xs : RightLeaningSumOfNormalizedMonomials n) → ⟦ squash xs ⟧RLSNM Γ ≡ ⟦ xs ⟧RLSNM Γ
squash-correct Γ nil = refl
squash-correct Γ (mon c x f :+ xs) = squash'-correct Γ c x f xs


mutual
  ------------------------------------------------------------------------
  -- Function expansion

  {-# TERMINATING #-} -- NOTE: We trust the user not to abuse expand-funs (such as expand-funs x = normalize x)
  expand-funs : ∀ {n} → :Expr n → :Expr n
  expand-funs (:var x) = :var x
  expand-funs :zero = :zero
  expand-funs (:suc x) = :suc (expand-funs x)
  expand-funs (x :+ x₁) = expand-funs x :+ expand-funs x₁
  expand-funs (x :* x₁) = expand-funs x :* expand-funs x₁
  expand-funs (:fun f) = proj₁ (expand normalize) f

  expand-funs-correct : ∀ {n} → (Γ : Env n) → (p : :Expr n) → ⟦ expand-funs p ⟧ Γ ≡ ⟦ p ⟧ Γ
  expand-funs-correct Γ (:var x) = refl
  expand-funs-correct Γ :zero = refl
  expand-funs-correct Γ (:suc x) = suc-cong (expand-funs-correct Γ x)
  expand-funs-correct Γ (x :+ x₁) = +-cong (expand-funs-correct Γ x) (expand-funs-correct Γ x₁)
  expand-funs-correct Γ (x :* x₁) = *-cong (expand-funs-correct Γ x) (expand-funs-correct Γ x₁)
  expand-funs-correct Γ (:fun f) = proj₂ (expand normalize) Γ f

  ------------------------------------------------------------------------
  -- Normalization

  normalize : ∀ {n} → CorrectTransform n
  normalize = (λ x → :⟦ squash $ sort $ throw-out-zeros $ normalize-monomials $ lean-right $ distrib $ expand-funs $ x ⟧RLSNM)
            , (λ Γ p → begin
                        ⟦ squash $ sort $ throw-out-zeros $ normalize-monomials $ lean-right $ distrib $ expand-funs $ p ⟧RLSNM Γ
                      ≈⟨ squash-correct Γ (sort $ throw-out-zeros $ normalize-monomials $ lean-right $ distrib $ expand-funs $ p) ⟩
                        ⟦ sort $ throw-out-zeros $ normalize-monomials $ lean-right $ distrib $ expand-funs $ p ⟧RLSNM Γ
                      ≈⟨ sort-correct Γ (throw-out-zeros $ normalize-monomials $ lean-right $ distrib $ expand-funs $ p) ⟩
                        ⟦ throw-out-zeros $ normalize-monomials $ lean-right $ distrib $ expand-funs $ p ⟧RLSNM Γ
                      ≈⟨ throw-out-zeros-correct Γ (normalize-monomials $ lean-right $ distrib $ expand-funs $ p) ⟩
                        ⟦ normalize-monomials $ lean-right $ distrib $ expand-funs $ p ⟧RLSNM Γ
                      ≈⟨ normalize-monomials-correct Γ (lean-right $ distrib $ expand-funs $ p) ⟩
                        ⟦ lean-right $ distrib $ expand-funs $ p ⟧RLSM Γ
                      ≈⟨ lean-right-correct Γ (distrib $ expand-funs $ p) ⟩
                        ⟦ distrib $ expand-funs $ p ⟧SM Γ
                      ≈⟨ distrib-correct Γ (expand-funs $ p) ⟩
                        ⟦ expand-funs $ p ⟧ Γ
                      ≈⟨ expand-funs-correct Γ p ⟩
                        ⟦ p ⟧ Γ
                      ∎)

⟦_⇓⟧ : ∀ {n} → :Expr n → Env n → Expr
⟦ p ⇓⟧ Γ = ⟦ (proj₁ normalize) p ⟧ Γ

correct : ∀ {n} (e : :Expr n) Γ → ⟦ e ⇓⟧ Γ ≡ ⟦ e ⟧ Γ
correct e Γ = (proj₂ normalize) Γ e
--   begin
--     ⟦ e ⇓⟧ Γ
--   ≡⟨⟩
--     ⟦ squash (sort (throw-out-zeros (normalize-monomials (lean-right (distrib e))))) ⟧RLSNM Γ
--   ≈⟨ sym (squash-correct Γ (sort (throw-out-zeros (normalize-monomials (lean-right (distrib e)))))) ⟩
--     ⟦ sort (throw-out-zeros (normalize-monomials (lean-right (distrib e)))) ⟧RLSNM Γ
--   ≈⟨ sym (sort-correct Γ (throw-out-zeros (normalize-monomials (lean-right (distrib e))))) ⟩
--     ⟦ throw-out-zeros (normalize-monomials (lean-right (distrib e))) ⟧RLSNM Γ
--   ≈⟨ sym (throw-out-zeros-correct Γ (normalize-monomials (lean-right (distrib e)))) ⟩
--     ⟦ normalize-monomials (lean-right (distrib e)) ⟧RLSNM Γ
--   ≈⟨ sym (normalize-monomials-correct Γ (lean-right (distrib e))) ⟩
--     ⟦ lean-right (distrib e) ⟧RLSM Γ
--   ≈⟨ sym (lean-right-correct Γ (distrib e)) ⟩
--     ⟦ distrib e ⟧SM Γ
--   ≈⟨ sym (distrib-correct Γ e) ⟩
--     ⟦ e ⟧ Γ
--   ∎


open Reflection ≡-setoid :var ⟦_⟧ ⟦_⇓⟧ correct public
  using (prove; solve) renaming (_⊜_ to _:=_)

