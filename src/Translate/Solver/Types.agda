------------------------------------------------------------------------
-- The Translate library
--
-- Main building blocks for expressions
------------------------------------------------------------------------

module Translate.Solver.Types where

open import Translate.Support
open import Translate.Base
open import Translate.Types
open import Translate.Axioms
open import Coinduction
open import Function
open import Data.Vec
import Data.List as L
open import Data.Bool
open import Relation.Nullary
open import Data.Empty
open import Data.Product

infixl 6 _:*_
infixl 5 _:+_

------------------------------------------------------------------------
-- Intermediate representations used by the solver

-- data Constant : Set where
--   ∗zero : Constant
--   ∗suc : Constant → Constant
--   _∗+_ : Constant → Constant → Constant
--   _∗*_ : Constant → Constant → Constant

-- TODO: Move other types in here?

mutual
  data :Fun (m : ℕ) : Set where
    :fib' : (n : :Expr m) → :Fun m
    :2^' : (n : :Expr m) → :Fun m

  data :Expr (n : ℕ) : Set where
    :var : Fin n → :Expr n
    :zero : :Expr n
    :suc : (x : :Expr n) → :Expr n
    _:+_ : (l r : :Expr n) → :Expr n
    _:*_ : (l r : :Expr n) → :Expr n
    :fun : (f : :Fun n) → :Expr n

Env : ℕ → Set
Env = Vec Expr

mutual
  ⟦_⟧F : ∀ {n} → (x : :Fun n) → (Γ : Env n) → Fun
  ⟦ :fib' n ⟧F Γ = fib' (value (⟦ n ⟧ Γ))
  ⟦ :2^' n ⟧F Γ = 2^' (value (⟦ n ⟧ Γ))

  ⟦_⟧ : ∀ {n} → (x : :Expr n) → (Γ : Env n) → Expr
  ⟦ :var x ⟧ Γ = lookup x Γ
  ⟦ :zero ⟧ Γ = zero
  ⟦ :suc x ⟧ Γ = suc (⟦ x ⟧ Γ)
  ⟦ l :+ r ⟧ Γ = ⟦ l ⟧ Γ + ⟦ r ⟧ Γ
  ⟦ l :* r ⟧ Γ = ⟦ l ⟧ Γ * ⟦ r ⟧ Γ
  ⟦ :fun f ⟧ Γ = fun (⟦ f ⟧F Γ)

CorrectTransform : ℕ → Set₂
CorrectTransform n = Σ (:Expr n → :Expr n) (λ f → (Γ : Env n) → (p : :Expr n) → ⟦ f p ⟧ Γ ≡ ⟦ p ⟧ Γ)

CorrectFunTransform : ℕ → Set₂
CorrectFunTransform n = Σ (:Fun n → :Expr n) (λ f → (Γ : Env n) → (p : :Fun n) → ⟦ f p ⟧ Γ ≡ ⟦ :fun p ⟧ Γ)

-- expand : ∀ {n} → :Fun n → :Expr n
-- -- TODO: Implement more aggressive expansions
-- expand (:fib' n) = :fun (:fib' n)
-- expand (:2^' n) = :fun (:2^' n)

-- expand-correct : ∀ {n} → (Γ : Env n) → (f : :Fun n) → ⟦ expand f ⟧ Γ ≡ fun (⟦ f ⟧F Γ)
-- expand-correct ρ (:fib' n) = refl
-- expand-correct ρ (:2^' n) = refl

:fib : ∀ {n} → :Expr n → :Expr n
:fib n = :fun (:fib' n)

:2^ : ∀ {n} → :Expr n → :Expr n
:2^ n = :fun (:2^' n)

open import Translate.EqReasoning

-- NOTE: Please normalize the result
expand : ∀ {n} → CorrectTransform n → CorrectFunTransform n
expand (norm , norm-correct)
  = (λ { (:fib' n) → :fun (:fib' (norm n))
       ; (:2^' n) → :fun (:2^' (norm n))
       })
  , (λ { Γ (:fib' n) → fib-cong (toEquality (norm-correct Γ n))
       ; Γ (:2^' n) → 2^-cong (toEquality (norm-correct Γ n))
       })


-- fun (fib' (value (⟦ norm n ⟧ Γ)))
-- fun (fib' (value (⟦ n ⟧ Γ)))


------------------------------------------------------------------------
-- Generated comparators

private
  finCtr : ∀ {n} → ∀ {a b : Fin n} → (a P≡ b → ⊥) → Fsuc a P≡ Fsuc b → ⊥
  finCtr f Prefl = f Prefl

  exprVarCtr : ∀ {n} → ∀ {a b : Fin n} → (a P≡ b → ⊥) → :var a P≡ :var b → ⊥
  exprVarCtr f Prefl = f Prefl

  exprSucCtr : ∀ {n} → ∀ {a b : :Expr n} → (a P≡ b → ⊥) → :suc a P≡ :suc b → ⊥
  exprSucCtr f Prefl = f Prefl

  expr+Ctr1 : ∀ {n} → ∀ {a b₁ b₂ : :Expr n} → (b₁ P≡ b₂ → ⊥) → a :+ b₁ P≡ a :+ b₂ → ⊥
  expr+Ctr1 f Prefl = f Prefl

  expr+Ctr2 : ∀ {n} → ∀ {v1 v2 v3 v4 : :Expr n} → (v1 P≡ v2 → ⊥) → v1 :+ v3 P≡ v2 :+ v4 → ⊥
  expr+Ctr2 f Prefl = f Prefl

  expr*Ctr1 : ∀ {n} → ∀ {a b₁ b₂ : :Expr n} → (b₁ P≡ b₂ → ⊥) → a :* b₁ P≡ a :* b₂ → ⊥
  expr*Ctr1 f Prefl = f Prefl

  expr*Ctr2 : ∀ {n} → ∀ {v1 v2 v3 v4 : :Expr n} → (v1 P≡ v2 → ⊥) → v1 :* v3 P≡ v2 :* v4 → ⊥
  expr*Ctr2 f Prefl = f Prefl

  exprFunCtr : ∀ {n} → ∀ {a b : :Fun n} → (a P≡ b → ⊥) → :fun a P≡ :fun b → ⊥
  exprFunCtr f Prefl = f Prefl

  funFibCtr : ∀ {n} → ∀ {a b : :Expr n} → (a P≡ b → ⊥) → :fib' a P≡ :fib' b → ⊥
  funFibCtr f Prefl = f Prefl

  fun2^Ctr : ∀ {n} → ∀ {a b : :Expr n} → (a P≡ b → ⊥) → :2^' a P≡ :2^' b → ⊥
  fun2^Ctr f Prefl = f Prefl

mutual

  :ExprEq : ∀ {n} → (p q : :Expr n) → Dec (p P≡ q)
  :ExprEq :zero :zero = yes Prefl
  :ExprEq (:var x) (:var x₁) with finEq x x₁
  :ExprEq (:var x) (:var .x) | yes Prefl = yes Prefl
  :ExprEq (:var x) (:var x₁) | no ¬p = no (exprVarCtr ¬p)
  :ExprEq (:suc a) (:suc b) with :ExprEq a b
  :ExprEq (:suc a) (:suc .a) | yes Prefl = yes Prefl
  :ExprEq (:suc a) (:suc b) | no ¬p = no (exprSucCtr ¬p)
  :ExprEq (a :+ a₁) (b :+ b₁) with :ExprEq a b | :ExprEq a₁ b₁
  :ExprEq (a :+ a₁) (.a :+ .a₁) | yes Prefl | yes Prefl = yes Prefl
  :ExprEq (a :+ a₁) (.a :+ b₁) | yes Prefl | no ¬p = no (expr+Ctr1 ¬p)
  :ExprEq (a :+ a₁) (b :+ b₁) | no ¬p | q = no (expr+Ctr2 ¬p)
  :ExprEq (a :* a₁) (b :* b₁) with :ExprEq a b | :ExprEq a₁ b₁
  :ExprEq (a :* a₁) (.a :* .a₁) | yes Prefl | yes Prefl = yes Prefl
  :ExprEq (a :* a₁) (.a :* b₁) | yes Prefl | no ¬p = no (expr*Ctr1 ¬p)
  :ExprEq (a :* a₁) (b :* b₁) | no ¬p | q = no (expr*Ctr2 ¬p)
  :ExprEq (:fun f) (:fun f₁) with :FunEq f f₁
  :ExprEq (:fun f) (:fun .f) | yes Prefl = yes Prefl
  :ExprEq (:fun f) (:fun f₁) | no ¬p = no (exprFunCtr ¬p)
  :ExprEq (:var x) :zero = no (λ ())
  :ExprEq (:var x) (:suc b) = no (λ ())
  :ExprEq (:var x) (b :+ b₁) = no (λ ())
  :ExprEq (:var x) (b :* b₁) = no (λ ())
  :ExprEq (:var x) (:fun f) = no (λ ())
  :ExprEq :zero (:var x) = no (λ ())
  :ExprEq :zero (:suc b) = no (λ ())
  :ExprEq :zero (b :+ b₁) = no (λ ())
  :ExprEq :zero (b :* b₁) = no (λ ())
  :ExprEq :zero (:fun f) = no (λ ())
  :ExprEq (:suc a) (:var x) = no (λ ())
  :ExprEq (:suc a) :zero = no (λ ())
  :ExprEq (:suc a) (b :+ b₁) = no (λ ())
  :ExprEq (:suc a) (b :* b₁) = no (λ ())
  :ExprEq (:suc a) (:fun f) = no (λ ())
  :ExprEq (a :+ a₁) (:var x) = no (λ ())
  :ExprEq (a :+ a₁) :zero = no (λ ())
  :ExprEq (a :+ a₁) (:suc b) = no (λ ())
  :ExprEq (a :+ a₁) (b :* b₁) = no (λ ())
  :ExprEq (a :+ a₁) (:fun f) = no (λ ())
  :ExprEq (a :* a₁) (:var x) = no (λ ())
  :ExprEq (a :* a₁) :zero = no (λ ())
  :ExprEq (a :* a₁) (:suc b) = no (λ ())
  :ExprEq (a :* a₁) (b :+ b₁) = no (λ ())
  :ExprEq (a :* a₁) (:fun f) = no (λ ())
  :ExprEq (:fun f) (:var x) = no (λ ())
  :ExprEq (:fun f) :zero = no (λ ())
  :ExprEq (:fun f) (:suc b) = no (λ ())
  :ExprEq (:fun f) (b :+ b₁) = no (λ ())
  :ExprEq (:fun f) (b :* b₁) = no (λ ())
  -- :ExprEq :zero :zero = yes Prefl
  -- :ExprEq (:var l1) (:var r1) = ? -- finEq l1 r1
  -- :ExprEq (:suc l1) (:suc r1) = ? -- :ExprEq l1 r1
  -- :ExprEq (_:+_ l1 l2) (_:+_ r1 r2) = ? -- :ExprEq l1 r1 ∧ :ExprEq l2 r2
  -- :ExprEq (_:*_ l1 l2) (_:*_ r1 r2) = ? -- :ExprEq l1 r1 ∧ :ExprEq l2 r2
  -- :ExprEq (:fun l1) (:fun r1) = ? -- :FunEq l1 r1
  -- :ExprEq _ _ = false

  :FunEq : ∀ {n} → (p q : :Fun n) → Dec (p P≡ q)
  :FunEq (:fib' n₁) (:fib' n₂) with :ExprEq n₁ n₂
  :FunEq (:fib' n₁) (:fib' .n₁) | yes Prefl = yes Prefl
  :FunEq (:fib' n₁) (:fib' n₂) | no ¬p = no (funFibCtr ¬p)
  :FunEq (:2^' n₁) (:2^' n₂) with :ExprEq n₁ n₂
  :FunEq (:2^' n₁) (:2^' .n₁) | yes Prefl = yes Prefl
  :FunEq (:2^' n₁) (:2^' n₂) | no ¬p = no (fun2^Ctr ¬p)
  :FunEq (:fib' n₁) (:2^' n₂) = no (λ ())
  :FunEq (:2^' n₁) (:fib' n₂) = no (λ ())
  -- :FunEq (:fib' l1) (:fib' r1) = :ExprEq l1 r1
  -- :FunEq (:2^' l1) (:2^' r1) = :ExprEq l1 r1
  -- :FunEq _ _ = false

  finEq : ∀ {n} → (p q : Fin n) → Dec (p P≡ q)
  finEq Fzero Fzero = yes Prefl
  finEq Fzero (Fsuc b) = no (λ ())
  finEq (Fsuc a) Fzero = no (λ ())
  finEq {ℕsuc n} (Fsuc a) (Fsuc b) with finEq a b
  finEq {ℕsuc n} (Fsuc a) (Fsuc .a) | yes Prefl = yes Prefl
  finEq {ℕsuc n} (Fsuc a) (Fsuc b) | no ¬p = no (finCtr ¬p)

private
  isLt : ∀ {n} → Vec Bool n → Vec Bool n → Bool
  isLt [] [] = false
  isLt (true ∷ xs) (_ ∷ ys) = isLt xs ys
  isLt (false ∷ xs) (y ∷ ys) = y

toBool : ∀ {a} {A : Set a} {b c : A} → Dec (b P≡ c) → Bool
toBool (yes p) = true
toBool (no ¬p) = false

mutual

  :ExprLt : ∀ {n} → :Expr n → :Expr n → Bool
  :ExprLt :zero :zero = false
  :ExprLt (:var l1) (:var r1) = isLt ((toBool (finEq l1 r1)) ∷ []) (finLt l1 r1 ∷ [])
  :ExprLt (:suc l1) (:suc r1) = isLt (toBool (:ExprEq l1 r1) ∷ []) (:ExprLt l1 r1 ∷ [])
  :ExprLt (_:+_ l1 l2) (_:+_ r1 r2) = isLt (toBool (:ExprEq l1 r1) ∷ toBool (:ExprEq l2 r2) ∷ []) (:ExprLt l1 r1 ∷ :ExprLt l2 r2 ∷ [])
  :ExprLt (_:*_ l1 l2) (_:*_ r1 r2) = isLt (toBool (:ExprEq l1 r1) ∷ toBool (:ExprEq l2 r2) ∷ []) (:ExprLt l1 r1 ∷ :ExprLt l2 r2 ∷ [])
  :ExprLt (:fun l1) (:fun r1) = isLt (toBool (:FunEq l1 r1) ∷ []) (:FunLt l1 r1 ∷ [])
  :ExprLt (:var _) :zero = true
  :ExprLt (:var _) (:suc _) = true
  :ExprLt (:var _) (_:+_ _ _) = true
  :ExprLt (:var _) (_:*_ _ _) = true
  :ExprLt (:var _) (:fun _) = true
  :ExprLt :zero (:suc _) = true
  :ExprLt :zero (_:+_ _ _) = true
  :ExprLt :zero (_:*_ _ _) = true
  :ExprLt :zero (:fun _) = true
  :ExprLt (:suc _) (_:+_ _ _) = true
  :ExprLt (:suc _) (_:*_ _ _) = true
  :ExprLt (:suc _) (:fun _) = true
  :ExprLt (_:+_ _ _) (_:*_ _ _) = true
  :ExprLt (_:+_ _ _) (:fun _) = true
  :ExprLt (_:*_ _ _) (:fun _) = true
  :ExprLt _ _ = false

  :FunLt : ∀ {n} → :Fun n → :Fun n → Bool
  :FunLt (:fib' l1) (:fib' r1) = isLt (toBool (:ExprEq l1 r1) ∷ []) (:ExprLt l1 r1 ∷ [])
  :FunLt (:2^' l1) (:2^' r1) = isLt (toBool (:ExprEq l1 r1) ∷ []) (:ExprLt l1 r1 ∷ [])
  :FunLt (:fib' _) (:2^' _) = true
  :FunLt _ _ = false

  finLt : ∀ {n} → Fin n → Fin n → Bool
  finLt Fzero Fzero = false
  finLt (Fsuc l1) (Fsuc r1) = isLt (toBool (finEq l1 r1) ∷ []) (finLt l1 r1 ∷ [])
  finLt Fzero (Fsuc _) = true
  finLt _ _ = false
