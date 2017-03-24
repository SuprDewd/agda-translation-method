module Translate.Tools where

open import Function

open import Translate.Base
open import Translate.Types
open import Translate.Common
open import Translate.Bijection using (getTo)

open import Data.Product
open import Data.List.Any
open import Data.List.All
open Data.List.Any.Membership-≡

open import IO hiding (lift)
open import Data.List hiding (_++_; any; all)
open import Data.String as S hiding (show)
open import Data.Unit
import Agda.Builtin.IO as BIO
import Data.Colist as CL
open import Data.Nat.Show using () renaming (show to ℕshow)

private
  infixl 1 _>>'_
  _>>'_ : ∀ {a} → {A : Set a} → {B : Set a} (m₁ : (IO B)) (m₂ : (IO A)) → IO A
  m₁ >>' m₂ = (♯ m₁) >> (♯ m₂)

  seekAny : ∀ {A : Set} {P : A → Set} → (xs : List A) → Any P xs → Σ A (λ x → P x)
  seekAny L[] ()
  seekAny (x L∷ xs) (here px) = x , px
  seekAny (x L∷ xs) (there p) = seekAny xs p

-- Show an ≡ relation (starting with small values, and going up)

show≡ : ∀ {A B : Expr} → A ≡ B → IO ⊤
show≡ {A} {B} p = mapM′ (proj (getTo (toBijection p))) (CL.fromList (generate A)) >>' return tt
  where
    proj : (lift A → lift B) → lift A → IO ⊤
    proj f x =
      putStr (show A x) >>'
      putStr " -> " >>'
      putStrLn (show B (f x)) >>'
      return tt

-- Compare an ≡ relation to a given direct bijection (starting with small values, and going up), printing all counterexamples it finds

check≡ : ∀ {A B : Expr} → A ≡ B → (lift A → lift B) → IO ⊤
check≡ {A} {B} p to = mapM′ (check (getTo (toBijection p))) (CL.fromList (generate A)) >>' return tt
  where
    check : (lift A → lift B) → lift A → IO ⊤
    check f x =
      let y = f x
          y′ = to x
      in if (case equal B y y′ of (λ { (yes p₁) → true ; (no ¬p) → false })) then return tt
         else putStr (show A x) >>'
              putStr " -> " >>'
              putStr (show B y) >>'
              putStr " /= " >>'
              putStrLn (show B y′) >>'
              return tt

-- Creating a Bijection from a list of pairs

toBij : ∀ {A B : Expr} → List (lift A × lift B) → Maybe (lift A B≡ lift B)
toBij {A} {B} lst with all (λ x → any (λ { (x' , y) → equal A x x' }) lst) (generate A)
                     | all (λ y → any (λ { (x , y') → equal B y y' }) lst) (generate B)
toBij {A} {B} lst | _ | no _ = nothing
toBij {A} {B} lst | no _ | _ = nothing
toBij {A} {B} lst | yes p | yes q =
    case all (λ x → equal A (from (to x)) x) (generate A)
    of (λ { (no _) → nothing
          ; (yes fromTo) →
              case all (λ y → equal B (to (from y)) y) (generate B)
              of (λ { (no _) → nothing
                    ; (yes toFrom) → just (mkBij to
                                                 from
                                                 (λ y → lookup toFrom (exhaustive B y))
                                                 (λ x → lookup fromTo (exhaustive A x)))
                    })
          })
  where
    to : lift A → lift B
    to x with seekAny lst (lookup p (exhaustive A x))
    to x | (x' , y) , _ = y

    from : lift B → lift A
    from y with seekAny lst (lookup q (exhaustive B y))
    from y | (x , y') , _ = x

