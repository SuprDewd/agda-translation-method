------------------------------------------------------------------------
-- The Translate library
--
-- Various properties of ≡
------------------------------------------------------------------------

module Translate.Properties where

open import Translate.Arithmetic
open import Translate.Base
open import Translate.Types
open import Relation.Binary
open import Algebra

≡-equivalence : IsEquivalence _≡_
≡-equivalence = record
  { refl = refl
  ; sym = sym
  ; trans = trans
  }

≡-setoid : Setoid _ _
≡-setoid = record
  { Carrier = Expr
  ; _≈_ = _≡_
  ; isEquivalence = ≡-equivalence
  }

≡-commutativeSemiring : CommutativeSemiring _ _
≡-commutativeSemiring = record
  { Carrier = Expr
  ; _≈_ = _≡_
  ; _+_ = _+_
  ; _*_ = _*_
  ; 0# = zero
  ; 1# = suc zero
  ; isCommutativeSemiring = record
    { +-isCommutativeMonoid = record
      { isSemigroup = record
        { isEquivalence = ≡-equivalence
        ; assoc = λ x y z → +-assoc {x} {y} {z}
        ; ∙-cong = +-cong
        }
      ; identityˡ = λ x → trans (+-comm {zero} {x}) (+-right-identity {x})
      ; comm = λ x y → +-comm {x} {y}
      }
    ; *-isCommutativeMonoid = record
      { isSemigroup = record
        { isEquivalence = ≡-equivalence
        ; assoc = λ x y z → *-assoc {x} {y} {z}
        ; ∙-cong = *-cong
        }
      ; identityˡ = λ x → trans (*-comm {suc zero} {x}) (*-right-identity {x})
      ; comm = λ x y → *-comm {x} {y}
      }
    ; distribʳ = λ x y z → distribʳ-*-+ {x} {y} {z}
    ; zeroˡ = λ x → trans (*-comm {zero} {x}) (*-right-zero {x})
    }
  }
