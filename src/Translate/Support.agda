------------------------------------------------------------------------
-- The Translate library
--
-- Various support data types, mostly re-exported from the standard
-- library
------------------------------------------------------------------------

module Translate.Support where

open import Data.Maybe public
  using ( Maybe
        ; nothing
        ; just
        )

open import Data.Product public
  using ( _×_
        ; _,_
        ; proj₁
        ; proj₂
        )

open import Data.Sum public
  using ( _⊎_
        ; inj₁
        ; inj₂
        )

open import Translate.Bijection public
  using (mkBij)
  renaming ( _≡_ to _B≡_
           ; refl to Brefl
           ; sym to Bsym
           ; trans to Btrans
           )

open import Relation.Binary.PropositionalEquality public
  using ()
  renaming ( _≡_ to _P≡_
           ; refl to Prefl
           ; sym to Psym
           ; trans to Ptrans
           ; cong to Pcong
           )

open import Data.Vec public
  using ( Vec
        ; []
        )

open import Data.Fin public
  using (Fin)
  renaming ( zero to Fzero
           ; suc to Fsuc
           ; _+_ to _F+_
           )

open import Data.Nat public
  using (ℕ)
  renaming ( zero to ℕzero
           ; suc to ℕsuc
           ; _+_ to _ℕ+_
           ; _*_ to _ℕ*_
           ; _≟_ to _ℕ≟_
           )

open import Coinduction public
  using ( ♯_
        ; ♭
        )

