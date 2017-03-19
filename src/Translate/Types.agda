
module Translate.Types where

open import Translate.Support
open import Function
open import Coinduction
open import Data.String
  using (String; _++_; toList)
import Data.List as L
open import Data.List.Any
open Data.List.Any.Membership-≡
import Data.Vec as V
import Data.Fin as F
open import Data.Char using (Char)
import Data.Nat.Properties.Simple as NPS
open import Data.Nat.Show
  using ()
  renaming (show to ℕshow)
open import Data.Nat
  using (_≤?_)
open import Data.Product

private
  -- Helper for show functions
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

  -- TODO: Use the builtin ∈ helpers
  ∈++ˡ : ∀  {S : Set} {A B : List S}{x : S} → x ∈ A → x ∈ (A L.++ B)
  ∈++ˡ (here p) = here p
  ∈++ˡ (there p) = there (∈++ˡ p)

  ∈++ʳ : ∀ {S : Set} {A B : List S} {x : S} → x ∈ B → x ∈ (A L.++ B)
  ∈++ʳ {S} {L[]} (here p) = here p
  ∈++ʳ {S} {L[]} (there p) = there (∈++ʳ {S} {L[]} p)
  ∈++ʳ {S} {x L∷ A} p = there (∈++ʳ {S} {A} p)

  ∈map : ∀ {A B : Set} {x : A} {xs : List A} {f : A → B} → x ∈ xs → f x ∈ L.map f xs
  ∈map {A} {B} {x} {xs} {f} (here p) = here (Pcong f p)
  ∈map (there p) = there (∈map p)

  ∈concatMap : ∀ {A B : Set} {x : A} {y : B} {xs : List A} {f : A → List B} → x ∈ xs → y ∈ f x → y ∈ L.concatMap f xs
  ∈concatMap {A} {B} {.x₁} {y} {x₁ L∷ xs} {f} (here Prefl) q = ∈++ˡ {_} {f x₁} q
  ∈concatMap {A} {B} {x} {y} {(x₁ L∷ xs)} {f} (there p) q = ∈++ʳ {_} {f x₁} (∈concatMap p q)

  generateFin : ∀ {n} → List (Fin n)
  generateFin {ℕzero} = L[]
  generateFin {ℕsuc n} = Fzero L∷ L.map Fsuc (generateFin {n})

  exhaustiveFin : ∀ {n} → (x : Fin n) → x ∈ generateFin {n}
  exhaustiveFin {ℕzero} ()
  exhaustiveFin {ℕsuc n} Fzero = here Prefl
  exhaustiveFin {ℕsuc n} (Fsuc x) = there (∈map (exhaustiveFin x))

  equalFin : ∀ {n} → (a b : Fin n) → Dec (a P≡ b)
  equalFin Fzero Fzero = yes Prefl
  equalFin Fzero (Fsuc b) = no (λ ())
  equalFin (Fsuc a) Fzero = no (λ ())
  equalFin (Fsuc a) (Fsuc b) with equalFin a b
  equalFin (Fsuc a) (Fsuc b) | yes Prefl = yes Prefl
  equalFin (Fsuc a) (Fsuc b) | no ¬p = no (λ { Prefl → ¬p Prefl })

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

  ∑ : (n : ℕ) → (Fin n → Expr) → Expr
  ∏ : (n : ℕ) → (Fin n → Expr) → Expr

  fun : (f : Fun) → Expr


------------------------------------------------------------------------
-- Natural numbers

-- TODO: Maybe nat should be a part of Expr?
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

module FibStrExpr where

  show : ∀ {n} → FibStr n → String
  show [] = "[]"
  show (x ∷1) = show x ++ " ∷1"
  show (x ∷2) = show x ++ " ∷2"

  generate : ∀ {n} → List (FibStr n)
  generate {ℕzero} = [] L∷ L[]
  generate {ℕsuc ℕzero} = ([] ∷1) L∷ L[]
  generate {ℕsuc (ℕsuc n)} = L.map _∷1 (generate {ℕsuc n}) L.++ L.map _∷2 (generate {n})

  exhaustive : ∀ {n} x → x ∈ (generate {n})
  exhaustive {ℕzero} [] = here Prefl
  exhaustive {ℕsuc ℕzero} ([] ∷1) = here Prefl
  exhaustive {ℕsuc (ℕsuc n)} (x ∷1) = ∈++ˡ {_} {L.map _∷1 (generate {ℕsuc n})} {L.map _∷2 (generate {n})} (∈map (exhaustive x))
  exhaustive {ℕsuc (ℕsuc n)} (x ∷2) = ∈++ʳ {_} {L.map _∷1 (generate {ℕsuc n})} {L.map _∷2 (generate {n})} (∈map (exhaustive x))

  equal : ∀ {n} → (x y : FibStr n) → Dec (x P≡ y)
  equal [] [] = yes Prefl
  equal (x ∷1) (y ∷1) with equal x y
  equal (x ∷1) (y ∷1) | yes Prefl = yes Prefl
  equal (x ∷1) (y ∷1) | no ¬p = no (λ { Prefl → ¬p Prefl })
  equal (x ∷1) (y ∷2) = no (λ ())
  equal (x ∷2) (y ∷1) = no (λ ())
  equal (x ∷2) (y ∷2) with equal x y
  equal (x ∷2) (y ∷2) | yes Prefl = yes Prefl
  equal (x ∷2) (y ∷2) | no ¬p = no (λ { Prefl → ¬p Prefl })

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

module SetPartitionKExpr where

  show : ∀ {l r} → SetPartitionK l r → String
  show {l} {r} p = showVec (λ xs → showList (λ y → ℕshow y) xs) (convert p)
    where
      convert : ∀ {l r} → SetPartitionK l r → Vec (List ℕ) l
      convert {l} {r} empty = V[]
      convert {ℕsuc l} {r} (add p) rewrite NPS.+-comm 1 l = convert p V.++ (((ℕsuc l) ℕ+ r) L∷ L[]) V∷ V[]
      convert {l} {r} (insert x p) =
        let xs = convert p
        in xs V.[ x ]≔ (V.lookup x xs L.++ (l ℕ+ r) L∷ L[])

  generate : ∀ {l r} → List (SetPartitionK l r)
  generate {ℕzero} {ℕzero} = empty L∷ L[]
  generate {ℕzero} {ℕsuc r} = L[]
  generate {ℕsuc l} {ℕzero} = L.map add generate
  generate {ℕsuc l} {ℕsuc r} = L.concatMap (λ i → L.map (λ p → insert i p) (generate {ℕsuc l} {r})) (generateFin {ℕsuc l}) L.++ L.map add generate

  exhaustive : ∀ {l r} → (x : SetPartitionK l r) → x ∈ generate {l} {r}
  exhaustive {ℕzero} {ℕzero} empty = here Prefl
  exhaustive {ℕzero} {ℕsuc r} (insert () _)
  exhaustive {ℕsuc l} {ℕzero} (add x) = ∈map (exhaustive x)
  exhaustive {ℕsuc l} {ℕsuc r} (add x) = ∈++ʳ {SetPartitionK (ℕsuc l) (ℕsuc r)} {L.concatMap (λ i → L.map (λ p → insert i p) (generate {ℕsuc l} {r})) (generateFin {ℕsuc l})} (∈map (exhaustive x))
  exhaustive {ℕsuc l} {ℕsuc r} (insert x x₁) = ∈++ˡ {SetPartitionK (ℕsuc l) (ℕsuc r)} {L.concatMap (λ i → L.map (λ p → insert i p) (generate {ℕsuc l} {r})) (generateFin {ℕsuc l})}
    (∈concatMap {Fin (ℕsuc l)} {SetPartitionK (ℕsuc l) (ℕsuc r)} {x} {insert x x₁} {generateFin {ℕsuc l}} {λ i → L.map (λ p → insert i p) (generate {ℕsuc l} {r})} (exhaustiveFin x) (∈map (exhaustive x₁)))

  equal : ∀ {l r} → (x y : SetPartitionK l r) → Dec (x P≡ y)
  equal empty empty = yes Prefl
  equal (add x) (add y) with equal x y
  equal (add x) (add y) | yes Prefl = yes Prefl
  equal (add x) (add y) | no ¬p = no (λ { Prefl → ¬p Prefl })
  equal (add x) (insert x₁ y) = no (λ ())
  equal (insert x x₁) (add y) = no (λ ())
  equal (insert x x₁) (insert y y₁) with equalFin x y | equal x₁ y₁
  equal (insert x x₁) (insert .x .x₁) | yes Prefl | yes Prefl = yes Prefl
  equal (insert x x₁) (insert y y₁) | yes p | no ¬p = no (λ { Prefl → ¬p Prefl })
  equal (insert x x₁) (insert y y₁) | no ¬p | yes p = no (λ { Prefl → ¬p Prefl })
  equal (insert x x₁) (insert y y₁) | no ¬p | no ¬p₁ = no (λ { Prefl → ¬p Prefl })

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

module CSetPartitionKExpr where

  show : ∀ {l r} → CSetPartitionK l r → String
  show {l} {r} p = showVec (λ xs → showList (λ y → ℕshow y) xs) (convert p)
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

  generate : ∀ {l r} → List (CSetPartitionK l r)
  generate {ℕzero} {ℕzero} = empty L∷ L[]
  generate {ℕzero} {ℕsuc r} = L[]
  generate {ℕsuc l} {ℕzero} = L.map add generate
  generate {ℕsuc l} {ℕsuc r} = L.concatMap (λ i → L.map (λ p → insert i p) (generate {ℕsuc l} {r})) (generateFin {l}) L.++ L.map add generate

  exhaustive : ∀ {l r} → (x : CSetPartitionK l r) → x ∈ generate {l} {r}
  exhaustive {ℕzero} {ℕzero} empty = here Prefl
  exhaustive {ℕzero} {ℕsuc r} ()
  exhaustive {ℕsuc l} {ℕzero} (add x) = ∈map (exhaustive x)
  exhaustive {ℕsuc l} {ℕsuc r} (add x) = ∈++ʳ {CSetPartitionK (ℕsuc l) (ℕsuc r)} {L.concatMap (λ i → L.map (λ p → insert i p) (generate {ℕsuc l} {r})) (generateFin {l})} (∈map (exhaustive x))
  exhaustive {ℕsuc l} {ℕsuc r} (insert x x₁) = ∈++ˡ {CSetPartitionK (ℕsuc l) (ℕsuc r)} {L.concatMap (λ i → L.map (λ p → insert i p) (generate {ℕsuc l} {r})) (generateFin {l})}
    (∈concatMap {Fin l} {CSetPartitionK (ℕsuc l) (ℕsuc r)} {x} {insert x x₁} {generateFin {l}} {λ i → L.map (λ p → insert i p) (generate {ℕsuc l} {r})} (exhaustiveFin x) (∈map (exhaustive x₁)))

  equal : ∀ {l r} → (x y : CSetPartitionK l r) → Dec (x P≡ y)
  equal empty empty = yes Prefl
  equal (add x) (add y) with equal x y
  equal (add x) (add y) | yes Prefl = yes Prefl
  equal (add x) (add y) | no ¬p = no (λ { Prefl → ¬p Prefl })
  equal (add x) (insert x₁ y) = no (λ ())
  equal (insert x x₁) (add y) = no (λ ())
  equal (insert x x₁) (insert y y₁) with equalFin x y | equal x₁ y₁
  equal (insert x x₁) (insert y y₁) | yes Prefl | yes Prefl = yes Prefl
  equal (insert x x₁) (insert y y₁) | yes p | no ¬p = no (λ { Prefl → ¬p Prefl })
  equal (insert x x₁) (insert y y₁) | no ¬p | yes p = no (λ { Prefl → ¬p Prefl })
  equal (insert x x₁) (insert y y₁) | no ¬p | no ¬p₁ = no (λ { Prefl → ¬p Prefl })

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

module BinStrExpr where

  show : ∀ {n} → BinStr n → String
  show [] = "[]"
  show (Fzero ∷ x₁) = "0 ∷ " ++ show x₁
  show (Fsuc Fzero ∷ x₁) = "1 ∷ " ++ show x₁
  show (Fsuc (Fsuc ()) ∷ _)

  generate : ∀ {n} → List (BinStr n)
  generate {ℕzero} = [] L∷ L[]
  generate {ℕsuc n} = L.map (_∷_ Fzero) (generate {n}) L.++ L.map (_∷_ (Fsuc Fzero)) (generate {n})

  exhaustive : ∀ {n} → (x : BinStr n) → x ∈ generate {n}
  exhaustive {ℕzero} [] = here Prefl
  exhaustive {ℕsuc n} (Fzero ∷ x) = ∈++ˡ (∈map (exhaustive x))
  exhaustive {ℕsuc n} (Fsuc Fzero ∷ x) = ∈++ʳ {BinStr (ℕsuc n)} {L.map (_∷_ Fzero) (generate {n})} (∈map (exhaustive x))
  exhaustive {ℕsuc n} (Fsuc (Fsuc ()) ∷ _)

  equal : ∀ {n} → (x y : BinStr n) → Dec (x P≡ y)
  equal [] [] = yes Prefl
  equal (Fzero ∷ xs) (Fzero ∷ ys) with equal xs ys
  equal (Fzero ∷ xs) (Fzero ∷ ys) | yes Prefl = yes Prefl
  equal (Fzero ∷ xs) (Fzero ∷ ys) | no ¬p = no (λ { Prefl → ¬p Prefl })
  equal (Fzero ∷ xs) (Fsuc y ∷ ys) = no (λ ())
  equal (Fsuc x ∷ xs) (Fzero ∷ ys) = no (λ ())
  equal (Fsuc Fzero ∷ xs) (Fsuc Fzero ∷ ys) with equal xs ys
  equal (Fsuc Fzero ∷ xs) (Fsuc Fzero ∷ ys) | yes Prefl = yes Prefl
  equal (Fsuc Fzero ∷ xs) (Fsuc Fzero ∷ ys) | no ¬p = no (λ { Prefl → ¬p Prefl})
  equal (Fsuc Fzero ∷ xs) (Fsuc (Fsuc ()) ∷ ys)
  equal (Fsuc (Fsuc ()) ∷ xs) (Fsuc Fzero ∷ ys)
  equal (Fsuc (Fsuc ()) ∷ xs) (Fsuc (Fsuc y) ∷ ys)

------------------------------------------------------------------------
-- Shorthands

fib : ℕ → Expr
fib n = fun (fib' n)

2^ : ℕ → Expr
2^ n = fun (2^' n)

S₂ : ℕ → ℕ → Expr
S₂ l r = fun (S₂' l r)

CS₂ : ℕ → ℕ → Expr
CS₂ l r = fun (CS₂' l r)

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
-- value (∑ 0 f) = 0
-- value (∑ (ℕsuc n) f) = value (∑ n (λ x → f (F.inject₁ x))) ℕ+ value (f (F.fromℕ n))
-- value (∑ n f) = L.foldr (_ℕ+_) 0 (L.map value (L.map f (generateFin {n})))
value (∑ n f) = L.foldr (_ℕ+_ ∘ value ∘ f) 0 (generateFin {n})
value (∏ n f) = {!!}
value (fun f) = valueF f

lift : Expr → Set
lift zero = ⊥
lift (suc x) = Maybe (lift x)
lift (l + r) = lift l ⊎ lift r
lift (l * r) = lift l × lift r
lift (∑ n f) = Σ (Fin n) (λ x → {!!})
lift (∏ n f) = (Fin n → {!!})
lift (fun f) = liftF f

------------------------------------------------------------------------
-- Various tools

showF : (F : Fun) → (x : liftF F) → String
showF (fib' n) = FibStrExpr.show
showF (2^' n) = BinStrExpr.show
showF (S₂' l r) = SetPartitionKExpr.show
showF (CS₂' l r) = CSetPartitionKExpr.show

show : (E : Expr) → (x : lift E) → String
show (zero) ()
show (suc E) (just x) = "just " ++ paren (show E x)
show (suc E) nothing = "nothing"
show (E + E₁) (inj₁ x) = "inj₁ " ++ paren (show E x)
show (E + E₁) (inj₂ y) = "inj₂ " ++ paren (show E₁ y)
show (E * E₁) (a , b) = paren (show E a) ++ " , " ++ paren (show E₁ b)
show (∑ n f) = {!!}
show (∏ n f) = {!!}
show (fun f) = showF f

generateF : (F : Fun) → List (liftF F)
generateF (fib' n) = FibStrExpr.generate
generateF (2^' n) = BinStrExpr.generate
generateF (S₂' l r) = SetPartitionKExpr.generate
generateF (CS₂' l r) = CSetPartitionKExpr.generate

exhaustiveF : (F : Fun) → (f : liftF F) → f ∈ generateF F
exhaustiveF (fib' n) = FibStrExpr.exhaustive
exhaustiveF (2^' n) = BinStrExpr.exhaustive
exhaustiveF (S₂' l r) = SetPartitionKExpr.exhaustive
exhaustiveF (CS₂' l r) = CSetPartitionKExpr.exhaustive

generate : (E : Expr) → List (lift E)
generate zero = L[]
generate (suc E) = nothing L∷ L.map just (generate E)
generate (E + E₁) = L.map inj₁ (generate E) L.++ L.map inj₂ (generate E₁)
generate (E * E₁) = L.concatMap (λ l → L.concatMap (λ r → (l , r) L∷ L[]) (generate E₁)) (generate E)
generate (∑ n f) = {!!}
generate (∏ n f) = {!!}
generate (fun f) = generateF f

exhaustive : (E : Expr) → (e : lift E) → e ∈ generate E
exhaustive zero ()
exhaustive (suc E) (just x) = there (∈map (exhaustive E x))
exhaustive (suc E) nothing = here Prefl
exhaustive (E + E₁) (inj₁ x) = ∈++ˡ (∈map (exhaustive E x))
exhaustive (E + E₁) (inj₂ y) = ∈++ʳ {lift (E + E₁)} {L.map inj₁ (generate E)} (∈map (exhaustive E₁ y))
exhaustive (E * E₁) (x , y) = ∈concatMap {lift E} {lift (E * E₁)} {x} {x , y} {generate E} {λ l → L.concatMap (λ r → (l , r) L∷ L[]) (generate E₁)} (exhaustive E x)
  (∈concatMap {lift E₁} {lift (E * E₁)} {y} {x , y} {generate E₁} {λ r → (x , r) L∷ L[]} (exhaustive E₁ y) (here Prefl))
exhaustive (∑ n f) = {!!}
exhaustive (∏ n f) = {!!}
exhaustive (fun f) = exhaustiveF f

equalF : (A : Fun) → (x y : liftF A) → Dec (x P≡ y)
equalF (fib' n) = FibStrExpr.equal
equalF (2^' n) = BinStrExpr.equal
equalF (S₂' l r) = SetPartitionKExpr.equal
equalF (CS₂' l r) = CSetPartitionKExpr.equal

equal : (A : Expr) → (x y : lift A) → Dec (x P≡ y)
equal zero () ()
equal (suc A) (just x) (just y) with equal A x y
equal (suc A) (just x) (just .x) | yes Prefl = yes Prefl
equal (suc A) (just x) (just y) | no ¬p = no (λ { Prefl → ¬p Prefl })
equal (suc A) (just x) nothing = no (λ ())
equal (suc A) nothing (just x) = no (λ ())
equal (suc A) nothing nothing = yes Prefl
equal (A₁ + A₂) (inj₁ x) (inj₁ y) with equal A₁ x y
equal (A₁ + A₂) (inj₁ x) (inj₁ y) | yes Prefl = yes Prefl
equal (A₁ + A₂) (inj₁ x) (inj₁ y) | no ¬p = no (λ { Prefl → (¬p Prefl) })
equal (A₁ + A₂) (inj₁ x) (inj₂ y) = no (λ ())
equal (A₁ + A₂) (inj₂ y) (inj₁ x) = no (λ ())
equal (A₁ + A₂) (inj₂ x) (inj₂ y) with equal A₂ x y
equal (A₁ + A₂) (inj₂ x) (inj₂ y) | yes Prefl = yes Prefl
equal (A₁ + A₂) (inj₂ x) (inj₂ y) | no ¬p = no (λ { Prefl → (¬p Prefl) })
equal (A₁ * A₂) (x₁ , x₂) (y₁ , y₂) with equal A₁ x₁ y₁ | equal A₂ x₂ y₂
equal (A₁ * A₂) (x₁ , x₂) (.x₁ , .x₂) | yes Prefl | (yes Prefl) = yes Prefl
equal (A₁ * A₂) (x₁ , x₂) (y₁ , y₂) | yes p | no ¬p = no (λ { Prefl → ¬p Prefl })
equal (A₁ * A₂) (x₁ , x₂) (y₁ , y₂) | no ¬p | yes p = no (λ { Prefl → ¬p Prefl })
equal (A₁ * A₂) (x₁ , x₂) (y₁ , y₂) | no ¬p | no ¬p₁ = no (λ { Prefl → ¬p Prefl })
equal (∑ n f) = {!!}
equal (∏ n f) = {!!}
equal (fun f) x y = equalF f x y

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

