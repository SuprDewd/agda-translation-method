
module Translate.Types where

open import Translate.Support
open import Function
open import Coinduction
open import Data.String
  using (String; _++_; toList)
import Data.List as L
open import Data.Char using (Char)

private
  -- Helper for show* functions
  paren : String → String
  paren x = if has-space (toList x) then "(" ++ x ++ ")" else x
    where
      has-space : L.List Char → Bool
      has-space L[] = false
      has-space (' ' L∷ _) = true
      has-space (_ L∷ s) = has-space s

-- mutual

  -- An expression
  -- record Expr : Set₁ where
  --   inductive
  --   field
  --     value : ∞ ℕ
  --     lift : Set
  --     -- expand : ∞ Polynomial

  -- data Polynomial : Set₁ where
  --   ∗atom : (x : Expr) → Polynomial
  --   -- ∗var : Fin ℕzero → Polynomial
  --   ∗zero : Polynomial
  --   ∗suc : (x : Polynomial) → Polynomial
  --   _∗+_ : (x y : Polynomial) → Polynomial
  --   _∗*_ : (x y : Polynomial) → Polynomial

-- An environment with n variables
-- Env : ∀ n → Set₁
-- Env n = Vec Expr n

-- Some shortcuts for ♭

-- value : Expr → ℕ
-- value e = ♭ $ Expr.value e

-- lift : Expr → Set
-- lift e = Expr.lift e

-- expand : Expr → Polynomial
-- expand e = ♭ $ Expr.expand e

-- Helpers for converting between zero-variable Expressions and Polynomials

-- mutual

  -- expr : :Expr ℕzero → Expr
  -- expr x = record
  --   { value = ♯ :value x []
  --   ; lift = ♯ :lift x []
  --   ; expand = ♯ polynomial (:expand x)
  --   }

  -- :expr : Expr → :Expr ℕzero
  -- :expr x = record
  --   { :value = λ Γ → ♯ value x
  --   ; :lift = λ Γ → ♯ lift x
  --   ; :expand = ♯ (:polynomial (expand x))
  --   ; :semantics = λ Γ → ♯ x
  --   }

  -- polynomial : :Polynomial ℕzero → Polynomial
  -- polynomial (∗atom x) = ∗atom (expr x)
  -- polynomial (∗var ())
  -- polynomial ∗zero = ∗zero
  -- polynomial (∗suc x) = ∗suc (polynomial x)
  -- polynomial (x ∗+ y) = (polynomial x) ∗+ (polynomial y)
  -- polynomial (x ∗* y) = (polynomial x) ∗* (polynomial y)

  -- :polynomial : Polynomial → :Polynomial ℕzero
  -- :polynomial (∗atom x) = ∗atom (:expr x)
  -- :polynomial ∗zero = ∗zero
  -- :polynomial (∗suc x) = ∗suc (:polynomial x)
  -- :polynomial (x ∗+ y) = (:polynomial x) ∗+ (:polynomial y)
  -- :polynomial (x ∗* y) = (:polynomial x) ∗* (:polynomial y)


infixl 6 _*_
infixl 5 _+_

data Fun : Set where
  fib' : (n : ℕ) → Fun
  2^' : (n : ℕ) → Fun

data Expr : Set where
  zero : Expr
  suc : (x : Expr) → Expr
  _+_ : (l r : Expr) → Expr
  _*_ : (l r : Expr) → Expr
  fun : (f : Fun) → Expr

fib : ℕ → Expr
fib n = fun (fib' n)

2^ : ℕ → Expr
2^ n = fun (2^' n)

------------------------------------------------------------------------
-- Fibonacci strings

-- Enumeration

ℕfib : ℕ → ℕ
ℕfib 0 = 1
ℕfib 1 = 1
ℕfib (ℕsuc (ℕsuc n)) = ℕfib (ℕsuc n) ℕ+ ℕfib n

-- Combinatorial interpretation

data FibStr : ℕ → Set where
  [] : FibStr ℕzero
  _∷1 : ∀ {n} → FibStr n → FibStr (ℕsuc n)
  _∷2 : ∀ {n} → FibStr n → FibStr (ℕsuc (ℕsuc n))

showFibStr : ∀ {n} → FibStr n → String
showFibStr [] = "[]"
showFibStr (x ∷1) = showFibStr x ++ " ∷1"
showFibStr (x ∷2) = showFibStr x ++ " ∷2"

generateFibStr : ∀ {n} → List (FibStr n)
generateFibStr {ℕzero} = [] L∷ L[]
generateFibStr {ℕsuc ℕzero} = ([] ∷1) L∷ L[]
generateFibStr {ℕsuc (ℕsuc n)} = L.map _∷1 (generateFibStr {ℕsuc n}) L.++ L.map _∷2 (generateFibStr {n})

------------------------------------------------------------------------
-- Binary strings

-- Enumeration

ℕ2^ : ℕ → ℕ
ℕ2^ 0 = 1
ℕ2^ (ℕsuc n) = ℕ2^ n ℕ+ ℕ2^ n

-- Combinatorial interpretation

data BinStr : ℕ → Set where
  [] : BinStr ℕzero
  _∷_ : ∀ {n} → Fin 2 → BinStr n → BinStr (ℕsuc n)

showBinStr : ∀ {n} → BinStr n → String
showBinStr [] = "[]"
showBinStr (Fzero ∷ x₁) = "0 ∷ " ++ showBinStr x₁
showBinStr (Fsuc Fzero ∷ x₁) = "1 ∷ " ++ showBinStr x₁
showBinStr (Fsuc (Fsuc ()) ∷ _)

generateBinStr : ∀ {n} → List (BinStr n)
generateBinStr {ℕzero} = [] L∷ L[]
generateBinStr {ℕsuc n} = L.map (_∷_ Fzero) (generateBinStr {n}) L.++ L.map (_∷_ (Fsuc Fzero)) (generateBinStr {n})

------------------------------------------------------------------------
-- Evaluating and lifting

valueF : Fun → ℕ
valueF (fib' n) = ℕfib n
valueF (2^' n) = ℕ2^ n

liftF : Fun → Set
liftF (fib' n) = FibStr n
liftF (2^' n) = BinStr n

value : Expr → ℕ
value zero = ℕzero
value (suc x) = ℕsuc (value x)
value (l + r) = value l ℕ+ value r
value (l * r) = value l ℕ* value r
value (fun f) = valueF f

lift : Expr → Set
lift zero = Fin (ℕzero)
lift (suc x) = Maybe (lift x)
lift (l + r) = lift l ⊎ lift r
lift (l * r) = lift l × lift r
lift (fun f) = liftF f

------------------------------------------------------------------------
-- Show

showF : (F : Fun) → (x : liftF F) → String
showF (fib' n) = showFibStr
showF (2^' n) = showBinStr

show : ∀ (E : Expr) → (x : lift E) → String
show (zero) ()
show (suc E) (just x) = "just " ++ paren (show E x)
show (suc E) nothing = "nothing"
show (E + E₁) (inj₁ x) = "inj₁ " ++ paren (show E x)
show (E + E₁) (inj₂ y) = "inj₂ " ++ paren (show E₁ y)
show (E * E₁) (a , b) = paren (show E a) ++ " , " ++ paren (show E₁ b)
show (fun f) = showF f

generateF : ∀ (F : Fun) → List (liftF F)
generateF (fib' n) = generateFibStr
generateF (2^' n) = generateBinStr

generate : ∀ (E : Expr) → List (lift E)
generate zero = L[]
generate (suc E) = nothing L∷ L.map just (generate E)
generate (E + E₁) = L.map inj₁ (generate E) L.++ L.map inj₂ (generate E₁)
generate (E * E₁) = L.concatMap (λ l → L.concatMap (λ r → (l , r) L∷ L[]) (generate E₁)) (generate E)
-- generate (E * E₁) = listProd (generate E) (generate E₁)
--   where
--     listProd : ∀ {A B : Set} → List A → List B → List (A × B)
--     listProd L[] bs = L[]
--     listProd (a L∷ as) bs = L.map (_,_ a) bs L.++ listProd as bs
generate (fun f) = generateF f

