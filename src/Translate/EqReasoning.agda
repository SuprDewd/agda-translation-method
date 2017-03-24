------------------------------------------------------------------------
-- The Translate library
--
-- Nice reasoning environment for ≡
------------------------------------------------------------------------

module Translate.EqReasoning where
  open import Translate.Properties
  open import Relation.Binary.EqReasoning ≡-setoid public
    renaming ( _≈⟨_⟩_ to _≡⟨_⟩_
             ; _≡⟨_⟩_ to _P≡⟨_⟩_
             ; _≡⟨⟩_ to _P≡⟨⟩_
             )
