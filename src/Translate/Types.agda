
module Translate.Types where

open import Translate.Support
open import Function
open import Coinduction
open import Data.String
  using (String; _++_; toList)
import Data.List as L
import Data.List.Any
import Data.Vec as V
import Data.Fin as F
open import Data.Char using (Char)
import Data.Nat.Properties.Simple as NPS
open import Data.Nat.Show
  using ()
  renaming (show to ℕshow)
open import Data.Nat
  using (_≤?_)

private
  -- Helper for show* functions
  paren : String → String
  paren x = if has-space (toList x) then "(" ++ x ++ ")" else x
    where
      has-space : L.List Char → Bool
      has-space L[] = false
      has-space (' ' L∷ _) = true
      has-space (_ L∷ s) = has-space s

  showVec : ∀ {n a} → {A : Set a} → (A → String) → Vec A n → String
  showVec {n} {a} {A} f xs = "[" ++ rec xs ++ "]"
    where
      rec : ∀ {n} → Vec A n → String
      rec V[] = ""
      rec (x V∷ V[]) = f x
      rec (x V∷ x₁ V∷ xs₁) = f x ++ ", " ++ rec (x₁ V∷ xs₁)

  showList : ∀ {a} → {A : Set a} → (A → String) → List A → String
  showList {a} {A} f xs = "[" ++ rec xs ++ "]"
    where
      rec : List A → String
      rec L[] = ""
      rec (x L∷ L[]) = f x
      rec (x L∷ x₁ L∷ xs₁) = f x ++ ", " ++ rec (x₁ L∷ xs₁)

  generateFin : ∀ {n} → List (Fin n)
  generateFin {ℕzero} = L[]
  generateFin {ℕsuc n} = L.map F.inject₁ (generateFin {n}) L.++ F.fromℕ n L∷ L[]

  equalFin : ∀ {n} → (a b : Fin n) → Bool
  equalFin Fzero Fzero = true
  equalFin (Fsuc a) (Fsuc b) = equalFin a b
  equalFin _ _ = false

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
  S₂' : (l r : ℕ) → Fun
  CS₂' : (l r : ℕ) → Fun

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

S₂ : ℕ → ℕ → Expr
S₂ l r = fun (S₂' l r)

CS₂ : ℕ → ℕ → Expr
CS₂ l r = fun (CS₂' l r)

------------------------------------------------------------------------
-- Natural numbers

nat : ℕ → Expr
nat ℕzero = zero
nat (ℕsuc n) = suc (nat n)

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

equalFibStr : ∀ {n} → FibStr n → FibStr n → Bool
equalFibStr [] [] = true
equalFibStr (a ∷1) (b ∷1) = equalFibStr a b
equalFibStr (a ∷2) (b ∷2) = equalFibStr a b
equalFibStr _ _ = false

------------------------------------------------------------------------
-- Set partitions

-- Enumeration

-- l parts, (l + r) elements
ℕS₂ : (l r : ℕ) → ℕ
ℕS₂ ℕzero ℕzero = 1
ℕS₂ ℕzero (ℕsuc r) = 0
ℕS₂ (ℕsuc l) ℕzero = ℕS₂ l ℕzero -- Or just 1
ℕS₂ (ℕsuc l) (ℕsuc r) = (ℕsuc l) ℕ* ℕS₂ (ℕsuc l) r ℕ+ ℕS₂ l (ℕsuc r)

-- Combinatorial interpretation

data SetPartitionK : ℕ → ℕ → Set where
  empty : SetPartitionK ℕzero ℕzero
  add : ∀ {l r} → SetPartitionK l r → SetPartitionK (ℕsuc l) r
  insert : ∀ {l r} → Fin l → SetPartitionK l r → SetPartitionK l (ℕsuc r)

showSetPartitionK : ∀ {l r} → SetPartitionK l r → String
showSetPartitionK {l} {r} p = showVec (λ xs → showList (λ y → ℕshow y) xs) (convert p)
  where
    convert : ∀ {l r} → SetPartitionK l r → Vec (List ℕ) l
    convert {l} {r} empty = V[]
    convert {ℕsuc l} {r} (add p) rewrite NPS.+-comm 1 l = convert p V.++ (((ℕsuc l) ℕ+ r) L∷ L[]) V∷ V[]
    convert {l} {r} (insert x p) =
      let xs = convert p
      in xs V.[ x ]≔ (V.lookup x xs L.++ (l ℕ+ r) L∷ L[])

generateSetPartitionK : ∀ {l r} → List (SetPartitionK l r)
generateSetPartitionK {ℕzero} {ℕzero} = empty L∷ L[]
generateSetPartitionK {ℕzero} {ℕsuc r} = L[]
generateSetPartitionK {ℕsuc l} {ℕzero} = L.map add generateSetPartitionK
generateSetPartitionK {ℕsuc l} {ℕsuc r} = L.concatMap (λ i → L.map (λ p → insert i p) (generateSetPartitionK {ℕsuc l} {r})) (generateFin {ℕsuc l}) L.++ L.map add generateSetPartitionK

equalSetPartitionK : ∀ {l r} → (p q : SetPartitionK l r) → Bool
equalSetPartitionK {ℕzero} {ℕzero} empty empty = true
equalSetPartitionK {ℕzero} {ℕsuc r} (insert () p) (insert x₁ q)
equalSetPartitionK {ℕsuc l} {ℕzero} (add p) (add q) = equalSetPartitionK p q
equalSetPartitionK {ℕsuc l} {ℕsuc r} (add p) (add q) = equalSetPartitionK p q
equalSetPartitionK {ℕsuc l} {ℕsuc r} (insert i₁ p) (insert i₂ q) = equalFin i₁ i₂ ∧ equalSetPartitionK p q
equalSetPartitionK {ℕsuc l} {ℕsuc r} _ _ = false

------------------------------------------------------------------------
-- Set partitions with no consecutive numbers in a part

-- Enumeration

-- l parts, (l + r) elements
ℕCS₂ : (l r : ℕ) → ℕ
ℕCS₂ ℕzero ℕzero = 1
ℕCS₂ ℕzero (ℕsuc r) = 0
ℕCS₂ (ℕsuc l) ℕzero = ℕCS₂ l ℕzero -- Or just 1
ℕCS₂ (ℕsuc l) (ℕsuc r) = l ℕ* ℕCS₂ (ℕsuc l) r ℕ+ ℕCS₂ l (ℕsuc r)

-- Combinatorial interpretation

data CSetPartitionK : ℕ → ℕ → Set where
  empty : CSetPartitionK ℕzero ℕzero
  add : ∀ {l r} → CSetPartitionK l r → CSetPartitionK (ℕsuc l) r
  insert : ∀ {l r} → Fin l → CSetPartitionK (ℕsuc l) r → CSetPartitionK (ℕsuc l) (ℕsuc r)

showCSetPartitionK : ∀ {l r} → CSetPartitionK l r → String
showCSetPartitionK {l} {r} p = showVec (λ xs → showList (λ y → ℕshow y) xs) (convert p)
  where
    app' : ∀ {l} → ℕ → Fin l → Vec (List ℕ) l → Vec (List ℕ) l
    app' x i xs = xs V.[ i ]≔ (V.lookup i xs L.++ x L∷ L[])

    app : ∀ {l} → ℕ → Fin l → Vec (List ℕ) (ℕsuc l) → Vec (List ℕ) (ℕsuc l)
    app x Fzero (x₁ V∷ xs) with Data.List.Any.any (λ y → (ℕsuc y) Data.Nat.≟ x) x₁
    app x Fzero (x₁ V∷ xs) | yes p = x₁ V∷ (app' x Fzero xs)
    app x Fzero (x₁ V∷ xs) | no ¬p = (x₁ L.++ (x L∷ L[])) V∷ xs
    app x (Fsuc i) (x₁ V∷ xs) with Data.List.Any.any (λ y → (ℕsuc y) Data.Nat.≟ x) x₁
    app x (Fsuc i) (x₁ V∷ xs) | yes p = x₁ V∷ (app' x (Fsuc i) xs)
    app x (Fsuc i) (x₁ V∷ xs) | no ¬p = x₁ V∷ (app x i xs)

    convert : ∀ {l r} → CSetPartitionK l r → Vec (List ℕ) l
    convert empty = V[]
    convert {ℕsuc l} {r} (add p) rewrite NPS.+-comm 1 l = convert p V.++ (((ℕsuc l) ℕ+ r) L∷ L[]) V∷ V[]
    convert {ℕsuc l} {ℕsuc r} (insert x p) = let xs = convert p in app ((ℕsuc l) ℕ+ (ℕsuc r)) x xs

generateCSetPartitionK : ∀ {l r} → List (CSetPartitionK l r)
generateCSetPartitionK {ℕzero} {ℕzero} = empty L∷ L[]
generateCSetPartitionK {ℕzero} {ℕsuc r} = L[]
generateCSetPartitionK {ℕsuc l} {ℕzero} = L.map add generateCSetPartitionK
generateCSetPartitionK {ℕsuc l} {ℕsuc r} = L.concatMap (λ i → L.map (λ p → insert i p) (generateCSetPartitionK {ℕsuc l} {r})) (generateFin {l}) L.++ L.map add generateCSetPartitionK

equalCSetPartitionK : ∀ {l r} → (p q : CSetPartitionK l r) → Bool
equalCSetPartitionK {ℕzero} {ℕzero} empty empty = true
equalCSetPartitionK {ℕzero} {ℕsuc r} () q
equalCSetPartitionK {ℕsuc l} {ℕzero} (add p) (add q) = equalCSetPartitionK p q
equalCSetPartitionK {ℕsuc l} {ℕsuc r} (add p) (add q) = equalCSetPartitionK p q
equalCSetPartitionK {ℕsuc l} {ℕsuc r} (insert x p) (insert x₁ q) = equalFin x x₁ ∧ equalCSetPartitionK p q
equalCSetPartitionK {ℕsuc l} {ℕsuc r} _ _ = false

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

equalBinStr : ∀ {n} → BinStr n → BinStr n → Bool
equalBinStr [] [] = true
equalBinStr (Fzero ∷ a) (Fzero ∷ b) = equalBinStr a b
equalBinStr (Fsuc Fzero ∷ a) (Fsuc Fzero ∷ b) = equalBinStr a b
equalBinStr _ _ = false

------------------------------------------------------------------------
-- Evaluating and lifting

valueF : Fun → ℕ
valueF (fib' n) = ℕfib n
valueF (2^' n) = ℕ2^ n
valueF (S₂' l r) = ℕS₂ l r
valueF (CS₂' l r) = ℕCS₂ l r

liftF : Fun → Set
liftF (fib' n) = FibStr n
liftF (2^' n) = BinStr n
liftF (S₂' l r) = SetPartitionK l r
liftF (CS₂' l r) = CSetPartitionK l r

value : Expr → ℕ
value zero = ℕzero
value (suc x) = ℕsuc (value x)
value (l + r) = value l ℕ+ value r
value (l * r) = value l ℕ* value r
value (fun f) = valueF f

lift : Expr → Set
lift zero = ⊥
lift (suc x) = Maybe (lift x)
lift (l + r) = lift l ⊎ lift r
lift (l * r) = lift l × lift r
lift (fun f) = liftF f

------------------------------------------------------------------------
-- Various tools

showF : (F : Fun) → (x : liftF F) → String
showF (fib' n) = showFibStr
showF (2^' n) = showBinStr
showF (S₂' l r) = showSetPartitionK
showF (CS₂' l r) = showCSetPartitionK

show : (E : Expr) → (x : lift E) → String
show (zero) ()
show (suc E) (just x) = "just " ++ paren (show E x)
show (suc E) nothing = "nothing"
show (E + E₁) (inj₁ x) = "inj₁ " ++ paren (show E x)
show (E + E₁) (inj₂ y) = "inj₂ " ++ paren (show E₁ y)
show (E * E₁) (a , b) = paren (show E a) ++ " , " ++ paren (show E₁ b)
show (fun f) = showF f

generateF : (F : Fun) → List (liftF F)
generateF (fib' n) = generateFibStr
generateF (2^' n) = generateBinStr
generateF (S₂' l r) = generateSetPartitionK
generateF (CS₂' l r) = generateCSetPartitionK

generate : (E : Expr) → List (lift E)
generate zero = L[]
generate (suc E) = nothing L∷ L.map just (generate E)
generate (E + E₁) = L.map inj₁ (generate E) L.++ L.map inj₂ (generate E₁)
generate (E * E₁) = L.concatMap (λ l → L.concatMap (λ r → (l , r) L∷ L[]) (generate E₁)) (generate E)
generate (fun f) = generateF f

equalF : (A : Fun) → liftF A → liftF A → Bool
equalF (fib' n) x y = equalFibStr x y
equalF (2^' n) x y = equalBinStr x y
equalF (S₂' l r) x y = equalSetPartitionK x y
equalF (CS₂' l r) x y = equalCSetPartitionK x y

equal : (A : Expr) → lift A → lift A → Bool
equal zero () ()
equal (suc A) (just x) (just x₁) = equal A x x₁
equal (suc A) nothing nothing = true
equal (A + A₁) (inj₁ x) (inj₁ x₁) = equal A x x₁
equal (A + A₁) (inj₂ y) (inj₂ y₁) = equal A₁ y y₁
equal (A * A₁) (p , q) (p₁ , q₁) = equal A p p₁ ∧ equal A₁ q q₁
equal (fun f) x y = equalF f x y
equal _ _ _ = false

------------------------------------------------------------------------
-- Properties

nat-value : ∀ n → value (nat n) P≡ n
nat-value ℕzero = Prefl
nat-value (ℕsuc n) = Pcong ℕsuc (nat-value n)

nat-lift : ∀ n → lift (nat n) B≡ Fin n
nat-lift ℕzero = mkBij (λ ()) (λ ()) (λ ()) (λ ())
nat-lift (ℕsuc n) = mkBij to from toFrom (fromTo {n})
  where
    to : ∀ {n} → Maybe (lift (nat n)) → Fin (ℕsuc n)
    to {ℕzero} (just ())
    to {ℕzero} nothing = Fzero
    to {ℕsuc n} nothing = Fzero
    to {ℕsuc n} (just x) = Fsuc (to x)

    from : ∀ {n} → Fin (ℕsuc n) → Maybe (lift (nat n))
    from {ℕzero} (Fsuc ())
    from {ℕzero} Fzero = nothing
    from {ℕsuc n} Fzero = nothing
    from {ℕsuc n} (Fsuc x) = just (from x)

    toFrom : ∀ {n} y → to {n} (from {n} y) P≡ y
    toFrom {ℕzero} (Fsuc ())
    toFrom {ℕzero} Fzero = Prefl
    toFrom {ℕsuc n} Fzero = Prefl
    toFrom {ℕsuc n} (Fsuc y) = Pcong Fsuc (toFrom {n} y)

    fromTo : ∀ {n} x → from {n} (to {n} x) P≡ x
    fromTo {ℕzero} (just ())
    fromTo {ℕzero} nothing = Prefl
    fromTo {ℕsuc n} nothing = Prefl
    fromTo {ℕsuc n} (just x) = Pcong just (fromTo {n} x)

