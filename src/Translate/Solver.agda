
module Translate.Solver where

open import Translate.Support
open import Translate.Base
open import Translate.EqReasoning
open import Translate.Support
open import Translate.Types
open import Translate.Axioms
open import Translate.Semiring
open import Translate.Properties
open import Translate.Combinatorics

open import Translate.Solver.Semiring
open import Translate.Solver.Reflection
open import Translate.Solver.Types public
open import Translate.Solver.Combinatorics

open import Data.Vec as V
open import Data.List as L

open import Relation.Nullary
open import Function
import Data.Fin as F
open import Data.Product
open import Data.Fin.Properties using () renaming (_≟_ to _F≟_)
open import Data.List.Properties

import Relation.Binary.Reflection as Reflection

-- TODO: Can I combine function definitions and correctness proofs using something like CorrectTransform?

-- TODO: Clean this up and integrate into new AST design

infixl 6 _C*_
infixl 5 _C+_


private

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

data Monomial (n : ℕ) : Set₂ where
  con : Constant → Monomial n
  var : (Fin n) → Monomial n
  fun : :Fun n → Monomial n
  _:*_ : Monomial n → Monomial n → Monomial n

data SumOfMonomials (n : ℕ) : Set₂ where
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
  ≈⟨ +-assoc ⟩
    (⟦ *-distrib l₁ r₁ ⟧SM Γ + ⟦ *-distrib l₁ r₂ ⟧SM Γ) + (⟦ *-distrib l₂ r₁ ⟧SM Γ + ⟦ *-distrib l₂ r₂ ⟧SM Γ)
  ≈⟨ +-cong (+-cong (*-distrib-correct Γ l₁ r₁) (*-distrib-correct Γ l₁ r₂)) (+-cong (*-distrib-correct Γ l₂ r₁) (*-distrib-correct Γ l₂ r₂)) ⟩
    (⟦ l₁ ⟧SM Γ * ⟦ r₁ ⟧SM Γ + ⟦ l₁ ⟧SM Γ * ⟦ r₂ ⟧SM Γ) + (⟦ l₂ ⟧SM Γ * ⟦ r₁ ⟧SM Γ + ⟦ l₂ ⟧SM Γ * ⟦ r₂ ⟧SM Γ)
  ≈⟨ +-cong (sym distribˡ-*-+) (sym distribˡ-*-+) ⟩
    ⟦ l₁ ⟧SM Γ * (⟦ r₁ ⟧SM Γ + ⟦ r₂ ⟧SM Γ) + ⟦ l₂ ⟧SM Γ * (⟦ r₁ ⟧SM Γ + ⟦ r₂ ⟧SM Γ)
  ≈⟨ sym distribʳ-*-+ ⟩
    (⟦ l₁ ⟧SM Γ + ⟦ l₂ ⟧SM Γ) * (⟦ r₁ ⟧SM Γ + ⟦ r₂ ⟧SM Γ)
  ∎

-- TODO: Make sure this is correct
distrib : ∀ {n} → :Expr n → SumOfMonomials n
distrib (:var x) = mon (var x)
distrib :zero = mon (con :zero)
distrib (:suc x) = mon (con (:suc :zero)) :+ distrib x
distrib (l :+ r) = distrib l :+ distrib r
distrib (l :* r) = *-distrib (distrib l) (distrib r)
distrib (:fun f) = mon (fun f)

distrib-correct : ∀ {n} → (Γ : Env n) → (p : :Expr n) → ⟦ distrib p ⟧SM Γ ≡ ⟦ p ⟧ Γ
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

------------------------------------------------------------------------
-- Right leaning

data RightLeaningSumOfMonomials (n : ℕ) : Set₂ where
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

data SnormalizedMonomial (n : ℕ) : Set₂ where
  mon : Constant → (vs : List (Fin n)) → (fs : List (:Fun n)) → SnormalizedMonomial n

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
insert-lf x (x₁ ∷ xs) with :FunnLt x x₁
insert-lf x (x₁ ∷ xs) | true = x ∷ (x₁ ∷ xs)
insert-lf x (x₁ ∷ xs) | false = x₁ ∷ insert-lf x xs

insert-lf-correct : ∀ {n} → (Γ : Env n) → (x : :Fun n) → (xs : List (:Fun n)) → ⟦ insert-lf x xs ⟧LF Γ ≡ ⟦ :fun x ⟧ Γ * ⟦ xs ⟧LF Γ
insert-lf-correct Γ x [] = refl
insert-lf-correct Γ x (x₁ ∷ xs) with :FunnLt x x₁
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

sort-snormalized-monomial : ∀ {n} → SnormalizedMonomial n → SnormalizedMonomial n
sort-snormalized-monomial (mon x vs fs) = mon x (sort-lv vs) (sort-lf fs)

sort-snormalized-monomial-correct : ∀ {n} → (Γ : Env n) → (p : SnormalizedMonomial n) → ⟦ sort-snormalized-monomial p ⟧SNM Γ ≡ ⟦ p ⟧SNM Γ
sort-snormalized-monomial-correct Γ (mon x vs fs) = *-cong refl (*-cong (sort-lv-correct Γ vs) (sort-lf-correct Γ fs))

------------------------------------------------------------------------
-- Normalize constants

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

data NormalizedMonomial (n : ℕ) : Set₂ where
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

data RightLeaningSumOfNormalizedMonomials : (n : ℕ) → Set₂ where
  nil : ∀ {n} → RightLeaningSumOfNormalizedMonomials n
  _:+_ : ∀ {n} → NormalizedMonomial n → RightLeaningSumOfNormalizedMonomials n → RightLeaningSumOfNormalizedMonomials n


:⟦_⟧RLSNM : ∀ {n} → RightLeaningSumOfNormalizedMonomials n → :Expr n
:⟦ nil ⟧RLSNM = :zero
:⟦ x :+ x₁ ⟧RLSNM = :⟦ x ⟧NM :+ :⟦ x₁ ⟧RLSNM

⟦_⟧RLSNM : ∀ {n} → RightLeaningSumOfNormalizedMonomials n → Env n → Expr
⟦ x ⟧RLSNM = ⟦ :⟦ x ⟧RLSNM ⟧

normalize-monomials : ∀ {n} → RightLeaningSumOfMonomials n → RightLeaningSumOfNormalizedMonomials n
normalize-monomials nil = nil
normalize-monomials (x :+ p) = normalize-constants (sort-snormalized-monomial (snormalize-monomial x)) :+ normalize-monomials p

normalize-monomials-correct : ∀ {n} → (Γ : Env n) → (p : RightLeaningSumOfMonomials n) → ⟦ normalize-monomials p ⟧RLSNM Γ ≡ ⟦ p ⟧RLSM Γ
normalize-monomials-correct Γ nil = refl
normalize-monomials-correct Γ (x :+ x₁) =
  begin
    ⟦ normalize-constants (sort-snormalized-monomial (snormalize-monomial x)) ⟧NM Γ + ⟦ normalize-monomials x₁ ⟧RLSNM Γ
  ≈⟨ +-cong (normalize-constants-correct Γ (sort-snormalized-monomial (snormalize-monomial x))) (normalize-monomials-correct Γ x₁) ⟩
    ⟦ sort-snormalized-monomial (snormalize-monomial x) ⟧SNM Γ + ⟦ x₁ ⟧RLSM Γ
  ≈⟨ +-cong (sort-snormalized-monomial-correct Γ (snormalize-monomial x)) refl ⟩
    ⟦ snormalize-monomial x ⟧SNM Γ + ⟦ x₁ ⟧RLSM Γ
  ≈⟨ +-cong (snormalize-monomial-correct Γ x) refl ⟩
    ⟦ x ⟧M Γ + ⟦ x₁ ⟧RLSM Γ
  ∎

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

------------------------------------------------------------------------
-- Sorting

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
lv-lt (x ∷ a) (x₁ ∷ b) with finnEq x x₁
lv-lt (x ∷ a) (x₁ ∷ b) | no _ = finnLt x x₁
lv-lt (x ∷ a) (x₁ ∷ b) | yes _ = lv-lt a b

lf-eq : ∀ {n} → (p q : List (:Fun n)) → Dec (p P≡ q)
lf-eq [] [] = yes Prefl
lf-eq [] (x ∷ q) = no (λ ())
lf-eq (x ∷ p) [] = no (λ ())
lf-eq (x ∷ p) (x₁ ∷ q) with :FunnEq x x₁ | lf-eq p q
lf-eq (x ∷ p) (.x ∷ .p) | yes Prefl | yes Prefl = yes Prefl
lf-eq (x ∷ p) (.x ∷ q) | yes Prefl | no ¬p = no (λ x₁ → ¬p (proj₂ (∷-injective x₁)))
lf-eq (x ∷ p) (x₁ ∷ q) | no ¬p | b = no (λ x₂ → ¬p (proj₁ (∷-injective x₂)))


lf-lt : ∀ {n} → (p q : List (:Fun n)) → Bool
lf-lt [] [] = false
lf-lt [] (x ∷ b) = true
lf-lt (x ∷ a) [] = false
lf-lt (x ∷ a) (x₁ ∷ b) = isLt (toBool (:FunnEq x x₁) ∷ toBool (lf-eq a b) ∷ [])
                              (:FunnLt x x₁ ∷ lf-lt a b ∷ [])

normalizedMonomialLt : ∀ {n} → (p q : NormalizedMonomial n) → Bool
normalizedMonomialLt (mon x vs fs) (mon x₁ vs₁ fs₁) = isLt (toBool (lv-eq vs vs₁) ∷ toBool (lf-eq fs fs₁) ∷ [])
                                                           (lv-lt vs vs₁ ∷ lf-lt fs fs₁ ∷ [])

sort-insert : ∀ {n} → NormalizedMonomial n → RightLeaningSumOfNormalizedMonomials n → RightLeaningSumOfNormalizedMonomials n
sort-insert x nil = x :+ nil
sort-insert x (x₁ :+ xs) with normalizedMonomialLt x x₁
sort-insert x (x₁ :+ xs) | true = x :+ (x₁ :+ xs)
sort-insert x (x₁ :+ xs) | false = x₁ :+ sort-insert x xs

sort-insert-correct : ∀ {n} → (Γ : Env n) → (x : NormalizedMonomial n) → (xs : RightLeaningSumOfNormalizedMonomials n) → ⟦ sort-insert x xs ⟧RLSNM Γ ≡ ⟦ x ⟧NM Γ + ⟦ xs ⟧RLSNM Γ
sort-insert-correct Γ x nil = refl
sort-insert-correct Γ x (x₁ :+ xs) with normalizedMonomialLt x x₁
sort-insert-correct Γ x (x₁ :+ xs) | true = refl
sort-insert-correct Γ x (x₁ :+ xs) | false =
  begin
    ⟦ x₁ :+ sort-insert x xs ⟧RLSNM Γ
  ≈⟨ +-cong refl (sort-insert-correct Γ x xs) ⟩
    ⟦ x₁ ⟧NM Γ + (⟦ x ⟧NM Γ + ⟦ xs ⟧RLSNM Γ)
  ≈⟨ sym +-assoc ⟩
    (⟦ x₁ ⟧NM Γ + ⟦ x ⟧NM Γ) + ⟦ xs ⟧RLSNM Γ
  ≈⟨ +-cong +-comm refl ⟩
    (⟦ x ⟧NM Γ + ⟦ x₁ ⟧NM Γ) + ⟦ xs ⟧RLSNM Γ
  ≈⟨ +-assoc ⟩
    ⟦ x ⟧NM Γ + (⟦ x₁ ⟧NM Γ + ⟦ xs ⟧RLSNM Γ)
  ∎

sort : ∀ {n} → RightLeaningSumOfNormalizedMonomials n → RightLeaningSumOfNormalizedMonomials n
sort nil = nil
sort (x :+ xs) = sort-insert x (sort xs)

sort-correct : ∀ {n} → (Γ : Env n) → (p : RightLeaningSumOfNormalizedMonomials n) → ⟦ sort p ⟧RLSNM Γ ≡ ⟦ p ⟧RLSNM Γ
sort-correct Γ nil = refl
sort-correct Γ (x :+ xs) =
  begin
    ⟦ sort-insert x (sort xs) ⟧RLSNM Γ
  ≈⟨ sort-insert-correct Γ x (sort xs) ⟩
    ⟦ x ⟧NM Γ + ⟦ sort xs ⟧RLSNM Γ
  ≈⟨ +-cong refl (sort-correct Γ xs) ⟩
    ⟦ x ⟧NM Γ + ⟦ xs ⟧RLSNM Γ
  ∎

------------------------------------------------------------------------
-- Squashing

squash' : ∀ {n} → NormalizedConstant → List (Fin n) → List (:Fun n) → RightLeaningSumOfNormalizedMonomials n → RightLeaningSumOfNormalizedMonomials n
squash' c x f nil = mon c x f :+ nil
squash' c₁ x₁ f₁ (mon c₂ x₂ f₂ :+ xs) with lv-eq x₁ x₂ | lf-eq f₁ f₂
squash' c₁ x₁ f₁ (mon c₂ x₂ f₂ :+ xs) | yes p | yes p₁ = squash' (c₁ C+ c₂) x₁ f₁ xs
squash' c₁ x₁ f₁ (mon c₂ x₂ f₂ :+ xs) | yes p | no ¬p = mon c₁ x₁ f₁ :+ squash' c₂ x₂ f₂ xs
squash' c₁ x₁ f₁ (mon c₂ x₂ f₂ :+ xs) | no ¬p | b = mon c₁ x₁ f₁ :+ squash' c₂ x₂ f₂ xs

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

squash : ∀ {n} → RightLeaningSumOfNormalizedMonomials n → RightLeaningSumOfNormalizedMonomials n
squash nil = nil
squash (mon c x f :+ xs) = squash' c x f xs

squash-correct : ∀ {n} → (Γ : Env n) → (xs : RightLeaningSumOfNormalizedMonomials n) → ⟦ squash xs ⟧RLSNM Γ ≡ ⟦ xs ⟧RLSNM Γ
squash-correct Γ nil = refl
squash-correct Γ (mon c x f :+ xs) = squash'-correct Γ c x f xs

private

  decNull :  ∀ {a} {A : Set a} → (xs : List A) → Dec (xs P≡ [])
  decNull [] = yes Prefl
  decNull (x ∷ xs) = no (λ ())

mutual

  uncon : ∀ {n} → :Expr n → NormalizedConstant × :Expr n
  uncon x with normalize x
  uncon x | nil = :zero , :zero
  uncon x | mon x₁ vs fs :+ p with decNull vs | decNull fs
  uncon x | mon x₁ .[] .[] :+ p₂ | yes Prefl | yes Prefl = x₁ , :⟦ p₂ ⟧RLSNM
  uncon x | mon x₁ .[] fs :+ p₁ | yes Prefl | no ¬p = :zero , :⟦ mon x₁ [] fs :+ p₁ ⟧RLSNM
  uncon x | mon x₁ vs .[] :+ p₁ | no ¬p | yes Prefl = :zero , :⟦ mon x₁ vs [] :+ p₁ ⟧RLSNM
  uncon x | mon x₁ vs fs :+ p | no ¬p | no ¬p₁ = :zero , :⟦ mon x₁ vs fs :+ p ⟧RLSNM

  uncon-correct : ∀ {n} → (Γ : Env n) → (x : :Expr n) → ⟦ proj₁ (uncon x) ⟧NC Γ + ⟦ proj₂ (uncon x) ⟧ Γ ≡ ⟦ x ⟧ Γ
  uncon-correct Γ x with normalize x | normalize-correct Γ x
  uncon-correct Γ x | nil | qc =
    begin
      zero + zero
    ≈⟨ +-right-identity ⟩
      zero
    ≈⟨ qc ⟩
      ⟦ x ⟧ Γ
    ∎
  uncon-correct Γ x | mon x₁ vs fs :+ p | qc with decNull vs | decNull fs
  uncon-correct Γ x | mon x₁ .[] .[] :+ p₂ | qc | yes Prefl | yes Prefl =
    begin
      ⟦ :⟦ x₁ ⟧NC ⟧ Γ + ⟦ :⟦ p₂ ⟧RLSNM ⟧ Γ
    ≈⟨ +-cong (sym *-right-identity) refl ⟩
      ⟦ :⟦ x₁ ⟧NC ⟧ Γ * suc zero + ⟦ :⟦ p₂ ⟧RLSNM ⟧ Γ
    ≈⟨ +-cong (sym *-right-identity) refl ⟩
      (⟦ :⟦ x₁ ⟧NC ⟧ Γ * suc zero) * suc zero + ⟦ :⟦ p₂ ⟧RLSNM ⟧ Γ
    ≈⟨ +-cong *-assoc refl ⟩
      ⟦ :⟦ x₁ ⟧NC ⟧ Γ * (suc zero * suc zero) + ⟦ :⟦ p₂ ⟧RLSNM ⟧ Γ
    ≈⟨ qc ⟩
      ⟦ x ⟧ Γ
    ∎
  uncon-correct Γ x | mon x₁ .[] fs :+ p₁ | qc | yes Prefl | no ¬p = trans +-comm (trans +-right-identity qc)
  uncon-correct Γ x | mon x₁ vs .[] :+ p₁ | qc | no ¬p | yes Prefl = trans +-comm (trans +-right-identity qc)
  uncon-correct Γ x | mon x₁ vs fs :+ p | qc | no ¬p | no ¬p₁ = trans +-comm (trans +-right-identity qc)

  -- NOTE: Please normalize the result
  expand : ∀ {n} → :Fun n → :Expr n
  expand (:fib' n) with uncon n
  expand (:fib' n) | :zero , x = :fib :⟦ x ⇓⟧
  expand (:fib' n) | :suc :zero , x = :fib :⟦ :suc :zero :+ x ⇓⟧
  expand (:fib' n) | :suc (:suc c) , x = :⟦ :fib (:suc (:⟦ c ⟧NC :+ x)) :+ :fib (:⟦ c ⟧NC :+ x) ⇓⟧
  expand (:2^' n) = :2^ n -- TODO: Expand

  expand-correct : ∀ {n} → (Γ : Env n) → (f : :Fun n) → ⟦ expand f ⟧ Γ ≡ ⟦ :fun f ⟧ Γ
  expand-correct Γ (:fib' n) with uncon n | uncon-correct Γ n
  expand-correct Γ (:fib' n) | :zero , x | p rewrite toEquality (correct x Γ) | toEquality p = refl
  expand-correct Γ (:fib' n) | :suc :zero , x | p rewrite toEquality (correct (:suc :zero :+ x) Γ) | toEquality p = refl
  expand-correct Γ (:fib' n) | :suc (:suc c) , x | p =
    begin
      ⟦ :⟦ :fib (:suc (:⟦ c ⟧NC :+ x)) :+ :fib (:⟦ c ⟧NC :+ x) ⇓⟧ ⟧ Γ
    ≈⟨ correct (:fib (:suc (:⟦ c ⟧NC :+ x)) :+ :fib (:⟦ c ⟧NC :+ x)) Γ ⟩
      ⟦ :fib (:suc (:⟦ c ⟧NC :+ x)) :+ :fib (:⟦ c ⟧NC :+ x) ⟧ Γ
    ≈⟨ sym fib-def ⟩
      ⟦ :fib (:suc (:suc (:⟦ c ⟧NC :+ x))) ⟧ Γ
    ≡⟨⟩
      fib (ℕsuc (ℕsuc (value (⟦ c ⟧NC Γ) ℕ+ value (⟦ x ⟧ Γ))))
    ≡⟨ Pcong (λ t → fib t) (toEquality p) ⟩
      fib (value (⟦ n ⟧ Γ))
    ∎
  expand-correct Γ (:2^' n) = refl

  ------------------------------------------------------------------------
  -- Function expansion

  {-# TERMINATING #-} -- NOTE: We trust the user not to abuse expand-funs (such as expand-funs x = normalize x)
  expand-funs : ∀ {n} → :Expr n → :Expr n
  expand-funs (:var x) = :var x
  expand-funs :zero = :zero
  expand-funs (:suc x) = :suc (expand-funs x)
  expand-funs (x :+ x₁) = expand-funs x :+ expand-funs x₁
  expand-funs (x :* x₁) = expand-funs x :* expand-funs x₁
  -- expand-funs (:fun f) = proj₁ (expand normalize (uncon , uncon-correct)) f
  expand-funs (:fun f) = expand f

  expand-funs-correct : ∀ {n} → (Γ : Env n) → (p : :Expr n) → ⟦ expand-funs p ⟧ Γ ≡ ⟦ p ⟧ Γ
  expand-funs-correct Γ (:var x) = refl
  expand-funs-correct Γ :zero = refl
  expand-funs-correct Γ (:suc x) = suc-cong (expand-funs-correct Γ x)
  expand-funs-correct Γ (x :+ x₁) = +-cong (expand-funs-correct Γ x) (expand-funs-correct Γ x₁)
  expand-funs-correct Γ (x :* x₁) = *-cong (expand-funs-correct Γ x) (expand-funs-correct Γ x₁)
  -- expand-funs-correct Γ (:fun f) = proj₂ (expand normalize (uncon , uncon-correct)) Γ f
  expand-funs-correct Γ (:fun f) = expand-correct Γ f

  ------------------------------------------------------------------------
  -- Normalization

  normalize : ∀ {n} → :Expr n → RightLeaningSumOfNormalizedMonomials n
  normalize = squash ∘ sort ∘ throw-out-zeros ∘ normalize-monomials ∘ lean-right ∘ distrib ∘ expand-funs

  normalize-correct : ∀ {n} → (Γ : Env n) → (x : :Expr n) → ⟦ normalize x ⟧RLSNM Γ ≡ ⟦ x ⟧ Γ
  normalize-correct Γ p =
     begin
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
     ∎

  :⟦_⇓⟧ : ∀ {n} → :Expr n → :Expr n
  :⟦ p ⇓⟧ = :⟦ normalize p ⟧RLSNM

  correct : ∀ {n} (e : :Expr n) Γ → ⟦ :⟦ e ⇓⟧ ⟧ Γ ≡ ⟦ e ⟧ Γ
  correct e Γ = normalize-correct Γ e

  -- normalize : ∀ {n} → CorrectTransform n
  -- normalize = (λ x → :⟦ normalize' x ⟧RLSNM)
  --           , (λ Γ p → normalize'-correct Γ p)

-- normalize : ∀ {n} → :Expr n → :Expr n
-- normalize e = {!!}

-- normalize-correct : ∀ {n} → (Γ : Env n) → (e : :Expr n) → ⟦ normalize e ⟧ Γ ≡ ⟦ e ⟧ Γ
-- normalize-correct Γ e = {!!}


⟦_⇓⟧ : ∀ {n} → :Expr n → Env n → Expr
⟦ p ⇓⟧ Γ = ⟦ :⟦ p ⇓⟧ ⟧ Γ

-- correct : ∀ {n} (e : :Expr n) Γ → ⟦ e ⇓⟧ Γ ≡ ⟦ e ⟧ Γ
-- correct e Γ = normalize-correct Γ e

open Reflection ≡-setoid :var ⟦_⟧ ⟦_⇓⟧ correct public
  using (prove; solve) renaming (_⊜_ to _:=_)

