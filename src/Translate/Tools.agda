module Translate.Tools where

open import Function

open import Translate.Base
open import Translate.Types
open import Translate.Support
open import Translate.Bijection using (getTo)

open import IO hiding (lift)
open import Data.List hiding (_++_)
open import Data.String as S hiding (show)
open import Data.Unit
import Agda.Builtin.IO as BIO
import Data.Colist as CL
open import Data.Nat.Show using () renaming (show to ℕshow)

private
  infixl 1 _>>'_
  _>>'_ : ∀ {a} → {A : Set a} → {B : Set a} (m₁ : (IO B)) (m₂ : (IO A)) → IO A
  m₁ >>' m₂ = (♯ m₁) >> (♯ m₂)

show≡ : ∀ {A B : Expr} → A ≡ B → IO ⊤
show≡ {A} {B} p = mapM′ (proj (getTo (toBijection p))) (CL.fromList (generate A)) >>' return tt
  where
    proj : (lift A → lift B) → lift A → IO ⊤
    proj f x =
      putStr (show A x) >>'
      putStr " -> " >>'
      putStrLn (show B (f x)) >>'
      return tt

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

