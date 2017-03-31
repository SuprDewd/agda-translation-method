module crash where

open import Data.Nat.Properties.Simple
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Data.Maybe
open import Data.Empty
open import IO
open import Data.Unit
open import Agda.Builtin.IO renaming (IO to BIO)
open import Data.String

data F : ℕ → Set where
  [] : F zero
  _∷1 : ∀ {n} → F n → F (suc n)
  _∷2 : ∀ {n} → F n → F (suc (suc n))

f : ∀ k → F (suc k) → F k ⊔ Maybe ⊥
f zero a = inj₂ nothing
f k (xs ∷1) = inj₂ nothing
-- to (suc k) xs = inj₂ nothing  -- This is fine
f (suc k) = λ xs → inj₂ nothing  -- This segfaults

myshow : F 1 ⊔ Maybe ⊥ → String
-- myshow (inj₁ b) = ""        -- This is fine
myshow (inj₁ (b ∷1)) = ""      -- This segfaults
myshow _ = ""

main : BIO ⊤
main = run (putStrLn (myshow (f 1 ([] ∷2))))

