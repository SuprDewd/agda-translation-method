module cancel where

open import Function

open import Translate
open import Translate.Combinatorics
open import Translate.Support
open import Translate.Axioms
open import Translate.Bijection using (getTo; getFrom; getToFrom; getFromTo)
open import Translate.Tools
import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Relation.Binary.PropositionalEquality
  using (inspect; [_])
import Data.Nat.Properties.Simple as NPS

open import Data.Product

open import Relation.Nullary

import Level
open import Relation.Binary
import Data.List as L
open import Data.List.Any as Any using (here; there)
open import Data.Empty

-- open import Data.List.Any.Membership

ex-counted-tp : (A : Set) → List A → Set
ex-counted-tp A counted = ∀ x → x ∈ counted
  where
    open Any.Membership (record { Carrier = A ; _≈_ = _P≡_ ; isEquivalence = record { refl = Prefl ; sym = Psym ; trans = Ptrans } }) -- TODO: Is there a simpler way?

module InvolutionPrinciple
                           -- (AS : DecSetoid Level.zero Level.zero)
                           -- (BS : DecSetoid Level.zero Level.zero)
                           -- (CS : DecSetoid Level.zero Level.zero)
                           -- (DS : DecSetoid Level.zero Level.zero)
                           -- (counted : List (DecSetoid.Carrier AS))
                           -- (ex-counted : ex-counted-tp AS counted) -- (x : A) → x ∈ counted
                           -- (b₁ : ((DecSetoid.Carrier AS) ⊎ (DecSetoid.Carrier BS)) B≡ ((DecSetoid.Carrier CS) ⊎ (DecSetoid.Carrier DS)))
                           -- (b₂ : (DecSetoid.Carrier BS) B≡ (DecSetoid.Carrier DS))
                           where

  -- open DecSetoid AS using () renaming (Carrier to A)
  -- open DecSetoid BS using () renaming (Carrier to B)
  -- open DecSetoid CS using () renaming (Carrier to C)
  -- open DecSetoid DS using () renaming (Carrier to D)

  -- open import Data.List.Countdown

  private
    suc-inj : ∀ {a b} → ℕsuc a P≡ ℕsuc b → a P≡ b
    suc-inj Prefl = Prefl

    inj₁-inj : ∀ {l l2} {A : Set l} {B : Set l2} {a b : A} → inj₁ {l} {l2} {A} {B} a P≡ inj₁ b → a P≡ b
    inj₁-inj Prefl = Prefl

    inj₂-inj : ∀ {l l2} {A : Set l} {B : Set l2} {a b : B} → inj₂ {l} {l2} {A} {B} a P≡ inj₂ b → a P≡ b
    inj₂-inj Prefl = Prefl

    apply-with-proof : ∀ {l} {a b : Set l} → (f : a → b) → (x : a) → Σ b (λ y → f x P≡ y)
    apply-with-proof f x = f x , Prefl

  data [_∧_⊨_⇒_] {A B C D : Set} (b₁ : (A ⊎ B) B≡ (C ⊎ D)) (b₂ : B B≡ D) : (A ⊎ B) → C → Set where
    step : ∀ {p q r s} → (getTo b₁ p P≡ inj₂ q) → (getFrom b₂ q P≡ r) → [ b₁ ∧ b₂ ⊨ inj₂ r ⇒ s ] → [ b₁ ∧ b₂ ⊨ p ⇒ s ]
    done : ∀ {p q} → (getTo b₁ p P≡ inj₁ q) → [ b₁ ∧ b₂ ⊨ p ⇒ q ]

  reverse : ∀ {A B C D} (b₁ : (A ⊎ B) B≡ (C ⊎ D)) (b₂ : B B≡ D) x y → [ b₁ ∧ b₂ ⊨ inj₁ x ⇒ y ] → [ (Bsym b₁) ∧ (Bsym b₂) ⊨ inj₁ y ⇒ x ]
  reverse (mkBij to from toFrom fromTo) (mkBij to₁ from₁ toFrom₁ fromTo₁) x y (done p) = done (
      begin
        from (inj₁ y)
      ≡⟨ Pcong from (Psym p) ⟩
        from (to (inj₁ x))
      ≡⟨ fromTo (inj₁ x) ⟩
        inj₁ x
      ∎
    )
  reverse b₁@(mkBij to₁ from₁ toFrom₁ fromTo₁)
          b₂@(mkBij to₂ from₂ toFrom₂ fromTo₂)
          x y (step {dp} {dq} {dr} {ds} p₁ p₂ p) = rev dr dq p₂ p (done (begin
            from₁ (inj₂ dq)
          ≡⟨ Pcong from₁ (Psym p₁) ⟩
            from₁ (to₁ (inj₁ x))
          ≡⟨ fromTo₁ (inj₁ x) ⟩
            inj₁ x
          ∎))
    where

      rev : ∀ z₁ z₂ → from₂ z₂ P≡ z₁ → [ b₁ ∧ b₂ ⊨ inj₂ z₁ ⇒ y ] → [ (Bsym b₁) ∧ (Bsym b₂) ⊨ inj₂ z₂ ⇒ x ] → [ (Bsym b₁) ∧ (Bsym b₂) ⊨ inj₁ y ⇒ x ]
      rev z₁ z₂ zp (done p) q = step
        (begin
          from₁ (inj₁ y)
        ≡⟨ Pcong from₁ (Psym p) ⟩
          from₁ (to₁ (inj₂ z₁))
        ≡⟨ fromTo₁ (inj₂ z₁) ⟩
          inj₂ z₁
        ∎)
        (begin
          to₂ z₁
        ≡⟨ Pcong to₂ (Psym zp) ⟩
          to₂ (from₂ z₂)
        ≡⟨ toFrom₂ z₂ ⟩
          z₂
        ∎)
        q

      rev z₁ z₂ zp (step {dp} {dq} {dr} {ds} p₁ p₂ p) q = rev dr dq p₂ p (step
        (begin
          from₁ (inj₂ dq)
        ≡⟨ Pcong from₁ (Psym p₁) ⟩
          from₁ (to₁ (inj₂ z₁))
        ≡⟨ fromTo₁ (inj₂ z₁) ⟩
          inj₂ z₁
        ∎)
        (begin
          to₂ z₁
        ≡⟨ Pcong to₂ (Psym zp) ⟩
          to₂ (from₂ z₂)
        ≡⟨ toFrom₂ z₂ ⟩
          z₂
        ∎)
        q)

  bijective : ∀ {A B C D} (b₁ : (A ⊎ B) B≡ (C ⊎ D)) (b₂ : B B≡ D) x y z → [ b₁ ∧ b₂ ⊨ y ⇒ x ] → [ b₁ ∧ b₂ ⊨ y ⇒ z ] → x P≡ z
  bijective (mkBij to₁ from₁ toFrom₁ fromTo₁)
            (mkBij to₂ from₂ toFrom₂ fromTo₂)
            x y z (done p) (done q) =
    inj₁-inj (begin
        inj₁ x
      ≡⟨ Psym p ⟩
        to₁ y
      ≡⟨ q ⟩
        inj₁ z
      ∎)
  bijective b₁@(mkBij to₁ from₁ toFrom₁ fromTo₁)
            b₂@(mkBij to₂ from₂ toFrom₂ fromTo₂)
            x y z
            (step {pp} {pq} {pr} {ps} p₁ p₂ p)
            (step {qp} {qq} {qr} {qs} q₁ q₂ q) = bijective b₁ b₂ x (inj₂ qr) z (fix p) q
    where
      fix : [ b₁ ∧ b₂ ⊨ inj₂ pr ⇒ x ] → [ b₁ ∧ b₂ ⊨ inj₂ qr ⇒ x ]
      fix t rewrite (begin
          qr
        ≡⟨ Psym q₂ ⟩
          from₂ qq
        ≡⟨ Pcong from₂ (inj₂-inj (begin
                                  inj₂ qq
                                ≡⟨ Psym q₁ ⟩
                                  to₁ y
                                ≡⟨ p₁ ⟩
                                  inj₂ pq
                                ∎)) ⟩
          from₂ pq
        ≡⟨ p₂ ⟩
          pr
        ∎) = t

  bijective (mkBij to₁ from₁ toFrom₁ fromTo₁) (mkBij to₂ from₂ toFrom₂ fromTo₂) x y z (done p) (step {dp} {dq} {dr} {ds} q₁ q₂ q) with Ptrans (Psym p) q₁
  ... | ()
  bijective (mkBij to₁ from₁ toFrom₁ fromTo₁) (mkBij to₂ from₂ toFrom₂ fromTo₂) x y z (step p₁ p₂ p) (done q) with Ptrans (Psym p₁) q
  ... | ()

  module Run2 (A : Set)
              (B : Set) (_B≟_ : (x y : B) → Dec (x P≡ y))
              (C : Set)
              (D : Set) (_D≟_ : (x y : D) → Dec (x P≡ y))
              (counted : List D)
              (ex-counted : ex-counted-tp D counted) -- (x : D) → x ∈ counted
              (b₁ : (A ⊎ B) B≡ (C ⊎ D))
              (b₂ : B B≡ D)
              where

    -- open Setoid AS using () renaming (Carrier to A)
    -- open Setoid BS using () renaming (Carrier to B)
    -- open Setoid CS using () renaming (Carrier to C)
    -- open Setoid DS using () renaming (Carrier to D)

    -- private
    --   decEqA⊎B : (x : A ⊎ B) → (y : A ⊎ B) → Dec (x P≡ y)
    --   decEqA⊎B (inj₁ x) (inj₁ x₁) with x A≟ x₁
    --   decEqA⊎B (inj₁ x) (inj₁ .x) | yes Prefl = yes Prefl
    --   decEqA⊎B (inj₁ x) (inj₁ x₁) | no ¬p = no (λ x₂ → ¬p (inj₁-inj x₂))
    --   decEqA⊎B (inj₁ x) (inj₂ y) = no (λ())
    --   decEqA⊎B (inj₂ y) (inj₁ x) = no (λ())
    --   decEqA⊎B (inj₂ y) (inj₂ y₁) with y B≟ y₁
    --   decEqA⊎B (inj₂ y) (inj₂ .y) | yes Prefl = yes Prefl
    --   decEqA⊎B (inj₂ y) (inj₂ y₁) | no ¬p = no (λ x → ¬p (inj₂-inj x))

    open import Data.List.Countdown (record { Carrier = D
                                            ; _≈_ = _P≡_
                                            ; isDecEquivalence = record { isEquivalence = record { refl = Prefl
                                                                                                 ; sym = Psym
                                                                                                 ; trans = Ptrans
                                                                                                 }
                                                                        ; _≟_ = _D≟_
                                                                        }
                                            }) as CntD
    open Any.Membership (record { Carrier = D
                                ; _≈_ = _P≡_
                                ; isEquivalence = record { refl = Prefl ; sym = Psym ; trans = Ptrans }
                                }) using () renaming (_∈_ to _D∈_)
    open import Data.List.Countdown (record { Carrier = B
                                            ; _≈_ = _P≡_
                                            ; isDecEquivalence = record { isEquivalence = record { refl = Prefl
                                                                                                 ; sym = Psym
                                                                                                 ; trans = Ptrans
                                                                                                 }
                                                                        ; _≟_ = _B≟_
                                                                        }
                                            }) as CntB
    open Any.Membership (record { Carrier = B
                                ; _≈_ = _P≡_
                                ; isEquivalence = record { refl = Prefl ; sym = Psym ; trans = Ptrans }
                                }) using () renaming (_∈_ to _B∈_)

    lemmaB : ∀ x x' xs → ¬ x B∈ xs → x' B∈ xs → ¬ x P≡ x'
    lemmaB x x' (x₁ L∷ xs) x∉xs (here x'≡x₁) = λ x≡x' → x∉xs (here (Ptrans x≡x' x'≡x₁))
    lemmaB x x' (x₁ L∷ xs) x∉xs (there x'∈xs) = lemmaB x x' xs (λ p → x∉xs (there p)) x'∈xs

    lemmaD : ∀ x x' xs → ¬ x D∈ xs → x' D∈ xs → ¬ x P≡ x'
    lemmaD x x' (x₁ L∷ xs) x∉xs (here x'≡x₁) = λ x≡x' → x∉xs (here (Ptrans x≡x' x'≡x₁))
    lemmaD x x' (x₁ L∷ xs) x∉xs (there x'∈xs) = lemmaD x x' xs (λ p → x∉xs (there p)) x'∈xs

    y-contr : ∀ {w} {W : Set w}
            → ∀ x x' xs {y}
            → ¬ x B∈ xs
            → x' B∈ xs
            → getTo b₁ (inj₂ x) P≡ inj₂ y
            → getTo b₁ (inj₂ x') P≡ inj₂ y
            → W
    y-contr x x' xs x∉xs x'∈xs x↦y x'↦y =
      let x≠x' = lemmaB x x' xs x∉xs x'∈xs
          x≡x' = inj₂-inj (begin
                            inj₂ x
                          ≡⟨ Psym (getFromTo b₁ (inj₂ x)) ⟩
                            getFrom b₁ (getTo b₁ (inj₂ x))
                          ≡⟨ Pcong (getFrom b₁) (Ptrans x↦y (Psym x'↦y)) ⟩
                            getFrom b₁ (getTo b₁ (inj₂ x'))
                          ≡⟨ getFromTo b₁ (inj₂ x') ⟩
                            inj₂ x'
                          ∎)
      in ⊥-elim (x≠x' x≡x')

    x-contr : ∀ {x} {w} {W : Set w}
            → ∀ y y' ys
            → ¬ y D∈ ys
            → y' D∈ ys
            → getFrom b₂ y P≡ x
            → getFrom b₂ y' P≡ x
            → W
    x-contr {x} y y' ys y∉ys y'∈ys y↦x y'↦x =
      let y≠y' = lemmaD y y' ys y∉ys y'∈ys
          y≡y' = (begin
                  y
                 ≡⟨ Psym (getToFrom b₂ y) ⟩
                  getTo b₂ (getFrom b₂ y)
                 ≡⟨ Pcong (getTo b₂) y↦x ⟩
                  getTo b₂ x
                 ≡⟨ Pcong (getTo b₂) (Psym y'↦x) ⟩
                  getTo b₂ (getFrom b₂ y')
                 ≡⟨ getToFrom b₂ y' ⟩
                  y'
                 ∎)
      in ⊥-elim (y≠y' y≡y')

    run2 : ∀ {m n} → (xs : List B)
                   → (ys : List D)
                   → ((x' : B) → x' B∈ xs → Σ D (λ y' → getFrom b₂ y' P≡ x' × y' D∈ ys))
                   → ((y' : D) → y' D∈ ys → Σ B (λ x' → getTo b₁ (inj₂ x') P≡ (inj₂ y') × x' B∈ xs))
                   → xs CntB.⊕ m
                   → ys CntD.⊕ n
                   → (x : B)
                   → ¬ x B∈ xs
                   → Σ D (λ y' → getFrom b₂ y' P≡ x × y' D∈ ys)
                   → Σ C (λ y → [ b₁ ∧ b₂ ⊨ inj₂ x ⇒ y ])

    -- All D's seen
    run2 {m} {ℕzero} xs ys preB preD cntB cntD x x∉xs xPre with getTo b₁ (inj₂ x) | inspect (getTo b₁) (inj₂ x)
    run2 {m} {ℕzero} xs ys preB preD cntB cntD x x∉xs xPre | inj₁ y | [ x↦y ] = y , done x↦y
    run2 {m} {ℕzero} xs ys preB preD cntB cntD x x∉xs xPre | inj₂ y | [ x↦y ] with CntD.lookup! cntD y
    run2 {m} {ℕzero} xs ys preB preD cntB cntD x x∉xs xPre | inj₂ y | [ x↦y ] | y∈ys with preD y y∈ys
    run2 {m} {ℕzero} xs ys preB preD cntB cntD x x∉xs xPre | inj₂ y | [ x↦y ] | y∈ys | x' , x'↦y , x'∈xs = y-contr x x' xs x∉xs x'∈xs x↦y x'↦y

    -- All B's seen
    run2 {ℕzero} {ℕsuc n}  xs ys preB preD cntB cntD x x∉xs xPre with getTo b₁ (inj₂ x) | inspect (getTo b₁) (inj₂ x)
    run2 {ℕzero} {ℕsuc n} xs ys preB preD cntB cntD x x∉xs xPre | inj₁ y | [ x↦y ] = y , done x↦y
    run2 {ℕzero} {ℕsuc n} xs ys preB preD cntB cntD x x∉xs xPre | inj₂ y | [ x↦y ] with CntD.lookup cntD y
    run2 {ℕzero} {ℕsuc n} xs ys preB preD cntB cntD x x∉xs xPre | inj₂ y | [ x↦y ] | yes y∈ys with preD y y∈ys
    run2 {ℕzero} {ℕsuc n} xs ys preB preD cntB cntD x x∉xs xPre | inj₂ y | [ x↦y ] | yes y∈ys | x' , x'↦y , x'∈xs = y-contr x x' xs x∉xs x'∈xs x↦y x'↦y
    run2 {ℕzero} {ℕsuc n} xs ys preB preD cntB cntD x x∉xs xPre | inj₂ y | [ x↦y ] | no  y∉ys with getFrom b₂ y | inspect (getFrom b₂) y
    run2 {ℕzero} {ℕsuc n} xs ys preB preD cntB cntD x x∉xs xPre | inj₂ y | [ x↦y ] | no  y∉ys | x' | [ y↦x' ] with CntB.lookup! cntB x'
    run2 {ℕzero} {ℕsuc n} xs ys preB preD cntB cntD x x∉xs xPre | inj₂ y | [ x↦y ] | no  y∉ys | x' | [ y↦x' ] | x'∈xs with preB x' x'∈xs
    run2 {ℕzero} {ℕsuc n} xs ys preB preD cntB cntD x x∉xs xPre | inj₂ y | [ x↦y ] | no  y∉ys | x' | [ y↦x' ] | x'∈xs | y' , y'↦x' , y'∈ys = x-contr y y' ys y∉ys y'∈ys y↦x' y'↦x'

    -- At least one unseen B and D
    run2 {ℕsuc m} {ℕsuc n} xs ys preB preD cntB cntD x x∉xs xPre with getTo b₁ (inj₂ x) | inspect (getTo b₁) (inj₂ x)
    run2 {ℕsuc m} {ℕsuc n} xs ys preB preD cntB cntD x x∉xs xPre | inj₁ y | [ x↦y ] = y , done x↦y
    run2 {ℕsuc m} {ℕsuc n} xs ys preB preD cntB cntD x x∉xs xPre | inj₂ y | [ x↦y ] with CntD.lookup cntD y
    run2 {ℕsuc m} {ℕsuc n} xs ys preB preD cntB cntD x x∉xs xPre | inj₂ y | [ x↦y ] | yes y∈ys with preD y y∈ys
    run2 {ℕsuc m} {ℕsuc n} xs ys preB preD cntB cntD x x∉xs xPre | inj₂ y | [ x↦y ] | yes y∈ys | x' , x'↦y , x'∈xs = y-contr x x' xs x∉xs x'∈xs x↦y x'↦y
    run2 {ℕsuc m} {ℕsuc n} xs ys preB preD cntB cntD x x∉xs xPre | inj₂ y | [ x↦y ] | no  y∉ys with getFrom b₂ y | inspect (getFrom b₂) y
    run2 {ℕsuc m} {ℕsuc n} xs ys preB preD cntB cntD x x∉xs xPre | inj₂ y | [ x↦y ] | no  y∉ys | x' | [ y↦x' ] with CntB.lookup cntB x'
    run2 {ℕsuc m} {ℕsuc n} xs ys preB preD cntB cntD x x∉xs xPre | inj₂ y | [ x↦y ] | no  y∉ys | x' | [ y↦x' ] | yes x'∈xs with preB x' x'∈xs
    run2 {ℕsuc m} {ℕsuc n} xs ys preB preD cntB cntD x x∉xs xPre | inj₂ y | [ x↦y ] | no  y∉ys | x' | [ y↦x' ] | yes x'∈xs | y' , y'↦x' , y'∈ys = x-contr y y' ys y∉ys y'∈ys y↦x' y'↦x'
    run2 {ℕsuc m} {ℕsuc n} xs ys preB preD cntB cntD x x∉xs xPre | inj₂ y | [ x↦y ] | no  y∉ys | x' | [ y↦x' ] | no  x'∉xs
      with run2 (x L∷ xs)
                (y L∷ ys)
                (λ { .x (here Prefl) → case xPre of (λ { (y₁ , y₁↦x , y₁∈ys) → y₁ , y₁↦x , there y₁∈ys })
                   ; x₁ (there x₁∈xs) → case preB x₁ x₁∈xs of (λ { (y₁ , y₁↦x₁ , y₁∈ys) → y₁ , y₁↦x₁ , there y₁∈ys })
                   })
                (λ { .y (here Prefl) → x , x↦y , here Prefl
                   ; y₁ (there y₁∈ys) → case preD y₁ y₁∈ys of (λ { (x₁ , x₁↦y₁ , x₁∈xs) → x₁ , x₁↦y₁ , there x₁∈xs })
                   })
                (CntB.insert cntB x x∉xs)
                (CntD.insert cntD y y∉ys)
                x'
                (λ { (here x'≡x) → case xPre of (λ { (y₁ , y₁↦x , y₁∈ys)
                                                   → lemmaD y y₁ ys y∉ys y₁∈ys (begin
                                                                                  y
                                                                                ≡⟨ Psym (getToFrom b₂ y) ⟩
                                                                                  getTo b₂ (getFrom b₂ y)
                                                                                ≡⟨ Pcong (getTo b₂) y↦x' ⟩
                                                                                  getTo b₂ x'
                                                                                ≡⟨ Pcong (getTo b₂) x'≡x ⟩
                                                                                  getTo b₂ x
                                                                                ≡⟨ Pcong (getTo b₂) (Psym y₁↦x) ⟩
                                                                                  getTo b₂ (getFrom b₂ y₁)
                                                                                ≡⟨ getToFrom b₂ y₁ ⟩
                                                                                  y₁
                                                                                ∎) })
                   ; (there x'∈xs) → x'∉xs x'∈xs
                   })
                (y , (y↦x' , here Prefl))
    run2 {ℕsuc m} {ℕsuc n} xs ys preB preD cntB cntD x x∉xs xPre | inj₂ y | [ x↦y ] | no y∉ys | x' | [ y↦x' ] | (no x'∉xs) | z , zp = z , step x↦y y↦x' zp

  {-# NON_TERMINATING #-}
  run : ∀ {A B C D : Set} → (b₁ : (A ⊎ B) B≡ (C ⊎ D)) → (b₂ : B B≡ D) → (x : A ⊎ B) → Σ C (λ y → [ b₁ ∧ b₂ ⊨ x ⇒ y ])
  run b₁ b₂ x with apply-with-proof (getTo b₁) x
  run b₁ b₂ x | inj₁ y , yp = y , done yp
  run b₁ b₂ x | inj₂ y , yp with run b₁ b₂ (inj₂ (getFrom b₂ y))
  run b₁ b₂ x | inj₂ y , yp | (z , zp) = z , step yp Prefl zp

  +-inj₂ : ∀ {A B C D} → A ℕ+ B P≡ C ℕ+ D → A P≡ C → B P≡ D
  +-inj₂ {ℕzero} {B} {.0} {D} p Prefl = p
  +-inj₂ {ℕsuc A} {B} {.(ℕsuc A)} {D} p Prefl = +-inj₂ {A} {B} {A} {D} (suc-inj p) Prefl

  +-inj₁ : ∀ {A B C D} → A ℕ+ B P≡ C ℕ+ D → B P≡ D → A P≡ C
  +-inj₁ {A} {B} {C} {D} p q = +-inj₂ {B} {A} {D} {C} (begin
      B ℕ+ A
    ≡⟨ NPS.+-comm B A ⟩
      A ℕ+ B
    ≡⟨ p ⟩
      C ℕ+ D
    ≡⟨ NPS.+-comm C D ⟩
      D ℕ+ C
    ∎) q

  +-cancel : ∀ {A B C D} → A + B ≡ C + D → B ≡ D → A ≡ C
  +-cancel {A} {B} {C} {D} p q = axiom (+-inj₁ (toEquality p) (toEquality q)) (mkBij to from toFrom fromTo)
    where
      to : lift A → lift C
      to x with run (toBijection p) (toBijection q) (inj₁ x)
      to x | y , prf = y

      from : lift C → lift A
      from x with run (Bsym (toBijection p)) (Bsym (toBijection q)) (inj₁ x)
      from x | y , prf = y

      toFrom : ∀ y → to (from y) P≡ y
      toFrom x with run (Bsym (toBijection p)) (Bsym (toBijection q)) (inj₁ x)
      toFrom x | y , prf with run (toBijection p) (toBijection q) (inj₁ y)
      toFrom x | y , prf | z , prf2 = bijective (toBijection p) (toBijection q) z (inj₁ y) x prf2 (fix (reverse (Bsym (toBijection p)) (Bsym (toBijection q)) x y prf))
        where
          symsym : ∀ {A B} → (t : A B≡ B) → Bsym (Bsym t) P≡ t
          symsym (mkBij to₁ from₁ x₁ x₂) = Prefl

          fix : [ Bsym (Bsym (toBijection p)) ∧ Bsym (Bsym (toBijection q)) ⊨ inj₁ y ⇒ x ] → [ toBijection p ∧ toBijection q ⊨ inj₁ y ⇒ x ]
          fix t rewrite symsym (toBijection p) | symsym (toBijection q) = t

      fromTo : ∀ x → from (to x) P≡ x
      fromTo x with run (toBijection p) (toBijection q) (inj₁ x)
      fromTo x | y , prf with run (Bsym (toBijection p)) (Bsym (toBijection q)) (inj₁ y)
      fromTo x | y , prf | z , prf2 = let test = reverse (toBijection p) (toBijection q) x y prf in bijective (Bsym (toBijection p)) (Bsym (toBijection q)) z (inj₁ y) x prf2 test

