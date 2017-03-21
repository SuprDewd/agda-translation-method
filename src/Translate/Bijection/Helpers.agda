------------------------------------------------------------------------
-- The Translate library
--
-- Various helper methods for bijections
------------------------------------------------------------------------
module Translate.Bijection.Helpers where

open import Function

open import Translate.Support
open import Translate.Bijection
open import Translate.Types

open import Data.Product
open import Data.List.Any
open import Data.List.All
open Data.List.Any.Membership-≡

-- Creating a Bijection from a list of pairs

private
  seekAny : ∀ {A : Set} {P : A → Set} → (xs : List A) → Any P xs → Σ A (λ x → P x)
  seekAny L[] ()
  seekAny (x L∷ xs) (here px) = x , px
  seekAny (x L∷ xs) (there p) = seekAny xs p

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
