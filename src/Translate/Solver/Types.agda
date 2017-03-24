------------------------------------------------------------------------
-- The Translate library
--
-- Main building blocks for expressions
------------------------------------------------------------------------

module Translate.Solver.Types where

open import Translate.Common
open import Translate.Base
open import Translate.Types
open import Translate.Arithmetic
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


data NormalizedConstant : Set where
  :zero : NormalizedConstant
  :suc : NormalizedConstant → NormalizedConstant

:⟦_⟧NC : ∀ {n} → NormalizedConstant → :Expr n
:⟦ :zero ⟧NC = :zero
:⟦ :suc x ⟧NC = :suc :⟦ x ⟧NC

⟦_⟧NC : ∀ {n} → NormalizedConstant → Env n → Expr
⟦ x ⟧NC = ⟦ :⟦ x ⟧NC ⟧

-- CorrectTransform : ℕ → Set₂
-- CorrectTransform n = Σ (:Expr n → :Expr n) (λ f → (Γ : Env n) → (p : :Expr n) → ⟦ f p ⟧ Γ ≡ ⟦ p ⟧ Γ)

-- CorrectFunTransform : ℕ → Set₂
-- CorrectFunTransform n = Σ (:Fun n → :Expr n) (λ f → (Γ : Env n) → (p : :Fun n) → ⟦ f p ⟧ Γ ≡ ⟦ :fun p ⟧ Γ)

-- CorrectUncon : ℕ → Set₂
-- CorrectUncon n = Σ (:Expr n → NormalizedConstant × :Expr n) (λ f → (Γ : Env n) → (x : :Expr n) → ⟦ proj₁ (f x) ⟧NC Γ + ⟦ proj₂ (f x) ⟧ Γ ≡ ⟦ x ⟧ Γ)

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

-- -- NOTE: Please normalize the result
-- expand : ∀ {n} → CorrectTransform n → CorrectUncon n → CorrectFunTransform n
-- expand (norm , norm-correct)
--        (uncon , uncon-correct)
--   = (λ { (:fib' n) → :fun (:fib' (norm n))
--        ; (:2^' n) → :fun (:2^' (norm n))
--        })
--   , (λ { Γ (:fib' n) → fib-cong (toEquality (norm-correct Γ n))
--        ; Γ (:2^' n) → 2^-cong (toEquality (norm-correct Γ n))
--        })


-- fun (fib' (value (⟦ norm n ⟧ Γ)))
-- fun (fib' (value (⟦ n ⟧ Γ)))


------------------------------------------------------------------------
-- Generated comparators

-- private
--   finCtr : ∀ {n} → ∀ {a b : Fin n} → (a P≡ b → ⊥) → Fsuc a P≡ Fsuc b → ⊥
--   finCtr f Prefl = f Prefl

--   exprVarCtr : ∀ {n} → ∀ {a b : Fin n} → (a P≡ b → ⊥) → :var a P≡ :var b → ⊥
--   exprVarCtr f Prefl = f Prefl

--   exprSucCtr : ∀ {n} → ∀ {a b : :Expr n} → (a P≡ b → ⊥) → :Expr.:suc a P≡ :Expr.:suc b → ⊥
--   exprSucCtr f Prefl = f Prefl

--   expr+Ctr1 : ∀ {n} → ∀ {a b₁ b₂ : :Expr n} → (b₁ P≡ b₂ → ⊥) → a :+ b₁ P≡ a :+ b₂ → ⊥
--   expr+Ctr1 f Prefl = f Prefl

--   expr+Ctr2 : ∀ {n} → ∀ {v1 v2 v3 v4 : :Expr n} → (v1 P≡ v2 → ⊥) → v1 :+ v3 P≡ v2 :+ v4 → ⊥
--   expr+Ctr2 f Prefl = f Prefl

--   expr*Ctr1 : ∀ {n} → ∀ {a b₁ b₂ : :Expr n} → (b₁ P≡ b₂ → ⊥) → a :* b₁ P≡ a :* b₂ → ⊥
--   expr*Ctr1 f Prefl = f Prefl

--   expr*Ctr2 : ∀ {n} → ∀ {v1 v2 v3 v4 : :Expr n} → (v1 P≡ v2 → ⊥) → v1 :* v3 P≡ v2 :* v4 → ⊥
--   expr*Ctr2 f Prefl = f Prefl

--   exprFunCtr : ∀ {n} → ∀ {a b : :Fun n} → (a P≡ b → ⊥) → :fun a P≡ :fun b → ⊥
--   exprFunCtr f Prefl = f Prefl

--   funFibCtr : ∀ {n} → ∀ {a b : :Expr n} → (a P≡ b → ⊥) → :fib' a P≡ :fib' b → ⊥
--   funFibCtr f Prefl = f Prefl

--   fun2^Ctr : ∀ {n} → ∀ {a b : :Expr n} → (a P≡ b → ⊥) → :2^' a P≡ :2^' b → ⊥
--   fun2^Ctr f Prefl = f Prefl

--   expr:+-inj1 : ∀ {n} → ∀ {l1 r1 : :Expr n} → {l2 r2 : :Expr n} → _:+_ l1 l2 P≡ _:+_ r1 r2 → l1 P≡ r1
--   expr:+-inj1 Prefl = Prefl

--   expr:+-inj2 : ∀ {n} → ∀ {l1 r1 : :Expr n} → {l2 r2 : :Expr n} → _:+_ l1 l2 P≡ _:+_ r1 r2 → l2 P≡ r2
--   expr:+-inj2 Prefl = Prefl

-- mutual

--   :ExprEq : ∀ {n} → (p q : :Expr n) → Dec (p P≡ q)
--   :ExprEq :zero :zero = yes Prefl
--   :ExprEq (:var x) (:var x₁) with finEq x x₁
--   :ExprEq (:var x) (:var .x) | yes Prefl = yes Prefl
--   :ExprEq (:var x) (:var x₁) | no ¬p = no (exprVarCtr ¬p)
--   :ExprEq (:suc a) (:suc b) with :ExprEq a b
--   :ExprEq (:suc a) (:suc .a) | yes Prefl = yes Prefl
--   :ExprEq (:suc a) (:suc b) | no ¬p = no (exprSucCtr ¬p)
--   :ExprEq (_:+_ l1 l2) (_:+_ r1 r2) with :ExprEq l1 r1 | :ExprEq l2 r2
--   :ExprEq (l1 :+ l2) (.l1 :+ .l2) | yes Prefl | yes Prefl = yes Prefl
--   :ExprEq (l1 :+ l2) (.l1 :+ r2) | yes Prefl | no ¬p = no (λ p → ¬p (expr:+-inj2 p))
--   :ExprEq (l1 :+ l2) (r1 :+ r2) | no ¬p | _ = no (λ p → ¬p (expr:+-inj1 p))
--   -- :ExprEq (a :+ a₁) (b :+ b₁) with :ExprEq a b | :ExprEq a₁ b₁
--   -- :ExprEq (a :+ a₁) (.a :+ .a₁) | yes Prefl | yes Prefl = yes Prefl
--   -- :ExprEq (a :+ a₁) (.a :+ b₁) | yes Prefl | no ¬p = no (expr+Ctr1 ¬p)
--   -- :ExprEq (a :+ a₁) (b :+ b₁) | no ¬p | q = no (expr+Ctr2 ¬p)
--   :ExprEq (a :* a₁) (b :* b₁) with :ExprEq a b | :ExprEq a₁ b₁
--   :ExprEq (a :* a₁) (.a :* .a₁) | yes Prefl | yes Prefl = yes Prefl
--   :ExprEq (a :* a₁) (.a :* b₁) | yes Prefl | no ¬p = no (expr*Ctr1 ¬p)
--   :ExprEq (a :* a₁) (b :* b₁) | no ¬p | q = no (expr*Ctr2 ¬p)
--   :ExprEq (:fun f) (:fun f₁) with :FunEq f f₁
--   :ExprEq (:fun f) (:fun .f) | yes Prefl = yes Prefl
--   :ExprEq (:fun f) (:fun f₁) | no ¬p = no (exprFunCtr ¬p)
--   :ExprEq (:var x) :zero = no (λ ())
--   :ExprEq (:var x) (:suc b) = no (λ ())
--   :ExprEq (:var x) (b :+ b₁) = no (λ ())
--   :ExprEq (:var x) (b :* b₁) = no (λ ())
--   :ExprEq (:var x) (:fun f) = no (λ ())
--   :ExprEq :zero (:var x) = no (λ ())
--   :ExprEq :zero (:suc b) = no (λ ())
--   :ExprEq :zero (b :+ b₁) = no (λ ())
--   :ExprEq :zero (b :* b₁) = no (λ ())
--   :ExprEq :zero (:fun f) = no (λ ())
--   :ExprEq (:suc a) (:var x) = no (λ ())
--   :ExprEq (:suc a) :zero = no (λ ())
--   :ExprEq (:suc a) (b :+ b₁) = no (λ ())
--   :ExprEq (:suc a) (b :* b₁) = no (λ ())
--   :ExprEq (:suc a) (:fun f) = no (λ ())
--   :ExprEq (a :+ a₁) (:var x) = no (λ ())
--   :ExprEq (a :+ a₁) :zero = no (λ ())
--   :ExprEq (a :+ a₁) (:suc b) = no (λ ())
--   :ExprEq (a :+ a₁) (b :* b₁) = no (λ ())
--   :ExprEq (a :+ a₁) (:fun f) = no (λ ())
--   :ExprEq (a :* a₁) (:var x) = no (λ ())
--   :ExprEq (a :* a₁) :zero = no (λ ())
--   :ExprEq (a :* a₁) (:suc b) = no (λ ())
--   :ExprEq (a :* a₁) (b :+ b₁) = no (λ ())
--   :ExprEq (a :* a₁) (:fun f) = no (λ ())
--   :ExprEq (:fun f) (:var x) = no (λ ())
--   :ExprEq (:fun f) :zero = no (λ ())
--   :ExprEq (:fun f) (:suc b) = no (λ ())
--   :ExprEq (:fun f) (b :+ b₁) = no (λ ())
--   :ExprEq (:fun f) (b :* b₁) = no (λ ())
--   -- :ExprEq :zero :zero = yes Prefl
--   -- :ExprEq (:var l1) (:var r1) = ? -- finEq l1 r1
--   -- :ExprEq (:suc l1) (:suc r1) = ? -- :ExprEq l1 r1
--   -- :ExprEq (_:+_ l1 l2) (_:+_ r1 r2) = ? -- :ExprEq l1 r1 ∧ :ExprEq l2 r2
--   -- :ExprEq (_:*_ l1 l2) (_:*_ r1 r2) = ? -- :ExprEq l1 r1 ∧ :ExprEq l2 r2
--   -- :ExprEq (:fun l1) (:fun r1) = ? -- :FunEq l1 r1
--   -- :ExprEq _ _ = false

--   :FunEq : ∀ {n} → (p q : :Fun n) → Dec (p P≡ q)
--   :FunEq (:fib' n₁) (:fib' n₂) with :ExprEq n₁ n₂
--   :FunEq (:fib' n₁) (:fib' .n₁) | yes Prefl = yes Prefl
--   :FunEq (:fib' n₁) (:fib' n₂) | no ¬p = no (funFibCtr ¬p)
--   :FunEq (:2^' n₁) (:2^' n₂) with :ExprEq n₁ n₂
--   :FunEq (:2^' n₁) (:2^' .n₁) | yes Prefl = yes Prefl
--   :FunEq (:2^' n₁) (:2^' n₂) | no ¬p = no (fun2^Ctr ¬p)
--   :FunEq (:fib' n₁) (:2^' n₂) = no (λ ())
--   :FunEq (:2^' n₁) (:fib' n₂) = no (λ ())
--   -- :FunEq (:fib' l1) (:fib' r1) = :ExprEq l1 r1
--   -- :FunEq (:2^' l1) (:2^' r1) = :ExprEq l1 r1
--   -- :FunEq _ _ = false

--   finEq : ∀ {n} → (p q : Fin n) → Dec (p P≡ q)
--   finEq Fzero Fzero = yes Prefl
--   finEq Fzero (Fsuc b) = no (λ ())
--   finEq (Fsuc a) Fzero = no (λ ())
--   finEq {ℕsuc n} (Fsuc a) (Fsuc b) with finEq a b
--   finEq {ℕsuc n} (Fsuc a) (Fsuc .a) | yes Prefl = yes Prefl
--   finEq {ℕsuc n} (Fsuc a) (Fsuc b) | no ¬p = no (finCtr ¬p)

-- private
--   isLt : ∀ {n} → Vec Bool n → Vec Bool n → Bool
--   isLt [] [] = false
--   isLt (true ∷ xs) (_ ∷ ys) = isLt xs ys
--   isLt (false ∷ xs) (y ∷ ys) = y

-- toBool : ∀ {a} {A : Set a} {b c : A} → Dec (b P≡ c) → Bool
-- toBool (yes p) = true
-- toBool (no ¬p) = false

-- mutual

--   :ExprLt : ∀ {n} → :Expr n → :Expr n → Bool
--   :ExprLt :zero :zero = false
--   :ExprLt (:var l1) (:var r1) = isLt ((toBool (finEq l1 r1)) ∷ []) (finLt l1 r1 ∷ [])
--   :ExprLt (:suc l1) (:suc r1) = isLt (toBool (:ExprEq l1 r1) ∷ []) (:ExprLt l1 r1 ∷ [])
--   :ExprLt (_:+_ l1 l2) (_:+_ r1 r2) = isLt (toBool (:ExprEq l1 r1) ∷ toBool (:ExprEq l2 r2) ∷ []) (:ExprLt l1 r1 ∷ :ExprLt l2 r2 ∷ [])
--   :ExprLt (_:*_ l1 l2) (_:*_ r1 r2) = isLt (toBool (:ExprEq l1 r1) ∷ toBool (:ExprEq l2 r2) ∷ []) (:ExprLt l1 r1 ∷ :ExprLt l2 r2 ∷ [])
--   :ExprLt (:fun l1) (:fun r1) = isLt (toBool (:FunEq l1 r1) ∷ []) (:FunLt l1 r1 ∷ [])
--   :ExprLt (:var _) :zero = true
--   :ExprLt (:var _) (:suc _) = true
--   :ExprLt (:var _) (_:+_ _ _) = true
--   :ExprLt (:var _) (_:*_ _ _) = true
--   :ExprLt (:var _) (:fun _) = true
--   :ExprLt :zero (:suc _) = true
--   :ExprLt :zero (_:+_ _ _) = true
--   :ExprLt :zero (_:*_ _ _) = true
--   :ExprLt :zero (:fun _) = true
--   :ExprLt (:suc _) (_:+_ _ _) = true
--   :ExprLt (:suc _) (_:*_ _ _) = true
--   :ExprLt (:suc _) (:fun _) = true
--   :ExprLt (_:+_ _ _) (_:*_ _ _) = true
--   :ExprLt (_:+_ _ _) (:fun _) = true
--   :ExprLt (_:*_ _ _) (:fun _) = true
--   :ExprLt _ _ = false

--   :FunLt : ∀ {n} → :Fun n → :Fun n → Bool
--   :FunLt (:fib' l1) (:fib' r1) = isLt (toBool (:ExprEq l1 r1) ∷ []) (:ExprLt l1 r1 ∷ [])
--   :FunLt (:2^' l1) (:2^' r1) = isLt (toBool (:ExprEq l1 r1) ∷ []) (:ExprLt l1 r1 ∷ [])
--   :FunLt (:fib' _) (:2^' _) = true
--   :FunLt _ _ = false

--   finLt : ∀ {n} → Fin n → Fin n → Bool
--   finLt Fzero Fzero = false
--   finLt (Fsuc l1) (Fsuc r1) = isLt (toBool (finEq l1 r1) ∷ []) (finLt l1 r1 ∷ [])
--   finLt Fzero (Fsuc _) = true
--   finLt _ _ = false

-- infixr 6 _∧_
-- _∧_ : Bool → Bool → Bool
-- true ∧ true = true
-- _ ∧ _ = false

private

  :Exprn-:var-inj1 : ∀ {n} → ∀ {l1 r1 : Fin n} → :var l1 P≡ :var r1 → l1 P≡ r1
  :Exprn-:var-inj1 Prefl = Prefl
  :Exprn-:suc-inj1 : ∀ {n} → ∀ {l1 r1 : :Expr n} → :Expr.:suc l1 P≡ :Expr.:suc r1 → l1 P≡ r1
  :Exprn-:suc-inj1 Prefl = Prefl
  :Exprn-_:+_-inj1 : ∀ {n} → ∀ {l1 r1 : :Expr n} → ∀ {l2 r2 : :Expr n} → _:+_ l1 l2 P≡ _:+_ r1 r2 → l1 P≡ r1
  :Exprn-_:+_-inj1 Prefl = Prefl
  :Exprn-_:+_-inj2 : ∀ {n} → ∀ {l1 r1 : :Expr n} → ∀ {l2 r2 : :Expr n} → _:+_ l1 l2 P≡ _:+_ r1 r2 → l2 P≡ r2
  :Exprn-_:+_-inj2 Prefl = Prefl
  :Exprn-_:*_-inj1 : ∀ {n} → ∀ {l1 r1 : :Expr n} → ∀ {l2 r2 : :Expr n} → _:*_ l1 l2 P≡ _:*_ r1 r2 → l1 P≡ r1
  :Exprn-_:*_-inj1 Prefl = Prefl
  :Exprn-_:*_-inj2 : ∀ {n} → ∀ {l1 r1 : :Expr n} → ∀ {l2 r2 : :Expr n} → _:*_ l1 l2 P≡ _:*_ r1 r2 → l2 P≡ r2
  :Exprn-_:*_-inj2 Prefl = Prefl
  :Exprn-:fun-inj1 : ∀ {n} → ∀ {l1 r1 : :Fun n} → :fun l1 P≡ :fun r1 → l1 P≡ r1
  :Exprn-:fun-inj1 Prefl = Prefl

  :Funn-:fib'-inj1 : ∀ {n} → ∀ {l1 r1 : :Expr n} → :fib' l1 P≡ :fib' r1 → l1 P≡ r1
  :Funn-:fib'-inj1 Prefl = Prefl
  :Funn-:2^'-inj1 : ∀ {n} → ∀ {l1 r1 : :Expr n} → :2^' l1 P≡ :2^' r1 → l1 P≡ r1
  :Funn-:2^'-inj1 Prefl = Prefl

  finn-Fsuc-inj1 : ∀ {n} → ∀ {l1 r1 : Fin n} → Fsuc l1 P≡ Fsuc r1 → l1 P≡ r1
  finn-Fsuc-inj1 Prefl = Prefl

mutual

  :ExprnEq : ∀ {n} → (p q : :Expr n) → Dec (p P≡ q)
  :ExprnEq :zero :zero = yes Prefl
  :ExprnEq (:var l1) (:var r1) with finnEq l1 r1
  :ExprnEq (:var l1) (:var r1) | no ¬p = no (λ p → ¬p (:Exprn-:var-inj1 p))
  :ExprnEq (:var l1) (:var .l1) | yes Prefl = yes Prefl
  :ExprnEq (:suc l1) (:suc r1) with :ExprnEq l1 r1
  :ExprnEq (:suc l1) (:suc r1) | no ¬p = no (λ p → ¬p (:Exprn-:suc-inj1 p))
  :ExprnEq (:suc l1) (:suc .l1) | yes Prefl = yes Prefl
  :ExprnEq (_:+_ l1 l2) (_:+_ r1 r2) with :ExprnEq l1 r1 | :ExprnEq l2 r2
  :ExprnEq (_:+_ l1 l2) (_:+_ r1 r2) | no ¬p | _ = no (λ p → ¬p (:Exprn-_:+_-inj1 p))
  :ExprnEq (_:+_ l1 l2) (_:+_ .l1 r2) | yes Prefl | no ¬p = no (λ p → ¬p (:Exprn-_:+_-inj2 p))
  :ExprnEq (_:+_ l1 l2) (_:+_ .l1 .l2) | yes Prefl | yes Prefl = yes Prefl
  :ExprnEq (_:*_ l1 l2) (_:*_ r1 r2) with :ExprnEq l1 r1 | :ExprnEq l2 r2
  :ExprnEq (_:*_ l1 l2) (_:*_ r1 r2) | no ¬p | _ = no (λ p → ¬p (:Exprn-_:*_-inj1 p))
  :ExprnEq (_:*_ l1 l2) (_:*_ .l1 r2) | yes Prefl | no ¬p = no (λ p → ¬p (:Exprn-_:*_-inj2 p))
  :ExprnEq (_:*_ l1 l2) (_:*_ .l1 .l2) | yes Prefl | yes Prefl = yes Prefl
  :ExprnEq (:fun l1) (:fun r1) with :FunnEq l1 r1
  :ExprnEq (:fun l1) (:fun r1) | no ¬p = no (λ p → ¬p (:Exprn-:fun-inj1 p))
  :ExprnEq (:fun l1) (:fun .l1) | yes Prefl = yes Prefl
  :ExprnEq (:var _) (:zero) = no (λ ())
  :ExprnEq (:var _) (:suc _) = no (λ ())
  :ExprnEq (:var _) (_:+_ _ _) = no (λ ())
  :ExprnEq (:var _) (_:*_ _ _) = no (λ ())
  :ExprnEq (:var _) (:fun _) = no (λ ())
  :ExprnEq (:zero) (:var _) = no (λ ())
  :ExprnEq (:zero) (:suc _) = no (λ ())
  :ExprnEq (:zero) (_:+_ _ _) = no (λ ())
  :ExprnEq (:zero) (_:*_ _ _) = no (λ ())
  :ExprnEq (:zero) (:fun _) = no (λ ())
  :ExprnEq (:suc _) (:var _) = no (λ ())
  :ExprnEq (:suc _) (:zero) = no (λ ())
  :ExprnEq (:suc _) (_:+_ _ _) = no (λ ())
  :ExprnEq (:suc _) (_:*_ _ _) = no (λ ())
  :ExprnEq (:suc _) (:fun _) = no (λ ())
  :ExprnEq (_:+_ _ _) (:var _) = no (λ ())
  :ExprnEq (_:+_ _ _) (:zero) = no (λ ())
  :ExprnEq (_:+_ _ _) (:suc _) = no (λ ())
  :ExprnEq (_:+_ _ _) (_:*_ _ _) = no (λ ())
  :ExprnEq (_:+_ _ _) (:fun _) = no (λ ())
  :ExprnEq (_:*_ _ _) (:var _) = no (λ ())
  :ExprnEq (_:*_ _ _) (:zero) = no (λ ())
  :ExprnEq (_:*_ _ _) (:suc _) = no (λ ())
  :ExprnEq (_:*_ _ _) (_:+_ _ _) = no (λ ())
  :ExprnEq (_:*_ _ _) (:fun _) = no (λ ())
  :ExprnEq (:fun _) (:var _) = no (λ ())
  :ExprnEq (:fun _) (:zero) = no (λ ())
  :ExprnEq (:fun _) (:suc _) = no (λ ())
  :ExprnEq (:fun _) (_:+_ _ _) = no (λ ())
  :ExprnEq (:fun _) (_:*_ _ _) = no (λ ())

  :FunnEq : ∀ {n} → (p q : :Fun n) → Dec (p P≡ q)
  :FunnEq (:fib' l1) (:fib' r1) with :ExprnEq l1 r1
  :FunnEq (:fib' l1) (:fib' r1) | no ¬p = no (λ p → ¬p (:Funn-:fib'-inj1 p))
  :FunnEq (:fib' l1) (:fib' .l1) | yes Prefl = yes Prefl
  :FunnEq (:2^' l1) (:2^' r1) with :ExprnEq l1 r1
  :FunnEq (:2^' l1) (:2^' r1) | no ¬p = no (λ p → ¬p (:Funn-:2^'-inj1 p))
  :FunnEq (:2^' l1) (:2^' .l1) | yes Prefl = yes Prefl
  :FunnEq (:fib' _) (:2^' _) = no (λ ())
  :FunnEq (:2^' _) (:fib' _) = no (λ ())

  finnEq : ∀ {n} → (p q : Fin n) → Dec (p P≡ q)
  finnEq Fzero Fzero = yes Prefl
  finnEq (Fsuc l1) (Fsuc r1) with finnEq l1 r1
  finnEq (Fsuc l1) (Fsuc r1) | no ¬p = no (λ p → ¬p (finn-Fsuc-inj1 p))
  finnEq (Fsuc l1) (Fsuc .l1) | yes Prefl = yes Prefl
  finnEq (Fzero) (Fsuc _) = no (λ ())
  finnEq (Fsuc _) (Fzero) = no (λ ())

isLt : ∀ {n} → Vec Bool n → Vec Bool n → Bool
isLt [] [] = false
isLt (true ∷ xs) (_ ∷ ys) = isLt xs ys
isLt (false ∷ xs) (y ∷ ys) = y

toBool : ∀ {a} {A : Set a} → {x y : A} → Dec (x P≡ y) → Bool
toBool (yes _) = true
toBool (no _) = false

mutual

  :ExprnLt : ∀ {n} → (p q : :Expr n) → Bool
  :ExprnLt :zero :zero = false
  :ExprnLt (:var l1) (:var r1) = isLt (toBool (finnEq l1 r1) ∷ []) (finnLt l1 r1 ∷ [])
  :ExprnLt (:suc l1) (:suc r1) = isLt (toBool (:ExprnEq l1 r1) ∷ []) (:ExprnLt l1 r1 ∷ [])
  :ExprnLt (_:+_ l1 l2) (_:+_ r1 r2) = isLt (toBool (:ExprnEq l1 r1) ∷ toBool (:ExprnEq l2 r2) ∷ []) (:ExprnLt l1 r1 ∷ :ExprnLt l2 r2 ∷ [])
  :ExprnLt (_:*_ l1 l2) (_:*_ r1 r2) = isLt (toBool (:ExprnEq l1 r1) ∷ toBool (:ExprnEq l2 r2) ∷ []) (:ExprnLt l1 r1 ∷ :ExprnLt l2 r2 ∷ [])
  :ExprnLt (:fun l1) (:fun r1) = isLt (toBool (:FunnEq l1 r1) ∷ []) (:FunnLt l1 r1 ∷ [])
  :ExprnLt (:var _) :zero = true
  :ExprnLt (:var _) (:suc _) = true
  :ExprnLt (:var _) (_:+_ _ _) = true
  :ExprnLt (:var _) (_:*_ _ _) = true
  :ExprnLt (:var _) (:fun _) = true
  :ExprnLt :zero (:suc _) = true
  :ExprnLt :zero (_:+_ _ _) = true
  :ExprnLt :zero (_:*_ _ _) = true
  :ExprnLt :zero (:fun _) = true
  :ExprnLt (:suc _) (_:+_ _ _) = true
  :ExprnLt (:suc _) (_:*_ _ _) = true
  :ExprnLt (:suc _) (:fun _) = true
  :ExprnLt (_:+_ _ _) (_:*_ _ _) = true
  :ExprnLt (_:+_ _ _) (:fun _) = true
  :ExprnLt (_:*_ _ _) (:fun _) = true
  :ExprnLt _ _ = false

  :FunnLt : ∀ {n} → (p q : :Fun n) → Bool
  :FunnLt (:fib' l1) (:fib' r1) = isLt (toBool (:ExprnEq l1 r1) ∷ []) (:ExprnLt l1 r1 ∷ [])
  :FunnLt (:2^' l1) (:2^' r1) = isLt (toBool (:ExprnEq l1 r1) ∷ []) (:ExprnLt l1 r1 ∷ [])
  :FunnLt (:fib' _) (:2^' _) = true
  :FunnLt _ _ = false

  finnLt : ∀ {n} → (p q : Fin n) → Bool
  finnLt Fzero Fzero = false
  finnLt (Fsuc l1) (Fsuc r1) = isLt (toBool (finnEq l1 r1) ∷ []) (finnLt l1 r1 ∷ [])
  finnLt Fzero (Fsuc _) = true
  finnLt _ _ = false
