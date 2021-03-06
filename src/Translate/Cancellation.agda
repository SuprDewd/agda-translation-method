module Translate.Cancellation where

open import Function

open import Translate.Base
open import Translate.Types
open import Translate.Combinatorics
open import Translate.Common
open import Translate.Arithmetic
open import Translate.Bijection using (getTo; getFrom; getToFrom; getFromTo)
open import Translate.Tools
import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Relation.Binary.PropositionalEquality
  using (inspect; [_])
import Data.Nat.Properties.Simple as NPS

open import Relation.Nullary
open import Relation.Binary

open import Data.Product
open import Data.Empty
import Data.List as L
import Data.Vec as V
open import Data.List.Any
open Data.List.Any.Membership-≡
import Data.List.Countdown

private
  suc-inj : ∀ {a b} → ℕsuc a P≡ ℕsuc b → a P≡ b
  suc-inj Prefl = Prefl

  inj₁-inj : ∀ {l l2} {A : Set l} {B : Set l2} {a b : A} → inj₁ {l} {l2} {A} {B} a P≡ inj₁ b → a P≡ b
  inj₁-inj Prefl = Prefl

  inj₂-inj : ∀ {l l2} {A : Set l} {B : Set l2} {a b : B} → inj₂ {l} {l2} {A} {B} a P≡ inj₂ b → a P≡ b
  inj₂-inj Prefl = Prefl

  -- Represents a valid iteration sequence produced by the involution principle
  data [_∧_⊨_⇒_] {A B C D : Set} (f : (A ⊔ B) ≅ (C ⊔ D)) (g : B ≅ D) : A ⊔ B → C → Set where
    step : ∀ {p q r s} → (getTo f p P≡ inj₂ q) → (getFrom g q P≡ r) → [ f ∧ g ⊨ inj₂ r ⇒ s ] → [ f ∧ g ⊨ p ⇒ s ]
    done : ∀ {p q} → (getTo f p P≡ inj₁ q) → [ f ∧ g ⊨ p ⇒ q ]

  reverse : ∀ {A B C D} (f : (A ⊔ B) ≅ (C ⊔ D)) (g : B ≅ D) x y → [ f ∧ g ⊨ inj₁ x ⇒ y ] → [ (Bsym f) ∧ (Bsym g) ⊨ inj₁ y ⇒ x ]
  reverse (mkBij to from to-from from-to) (mkBij to₁ from₁ to-from₁ from-to₁) x y (done p) = done (
      begin
        from (inj₁ y)
      ≡⟨ Pcong from (Psym p) ⟩
        from (to (inj₁ x))
      ≡⟨ from-to (inj₁ x) ⟩
        inj₁ x
      ∎
    )
  reverse f@(mkBij to₁ from₁ to-from₁ from-to₁)
          g@(mkBij to₂ from₂ to-from₂ from-to₂)
          x y (step {dp} {dq} {dr} {ds} p₁ p₂ p) = rev dr dq p₂ p (done (begin
            from₁ (inj₂ dq)
          ≡⟨ Pcong from₁ (Psym p₁) ⟩
            from₁ (to₁ (inj₁ x))
          ≡⟨ from-to₁ (inj₁ x) ⟩
            inj₁ x
          ∎))
    where

      rev : ∀ z₁ z₂ → from₂ z₂ P≡ z₁ → [ f ∧ g ⊨ inj₂ z₁ ⇒ y ] → [ (Bsym f) ∧ (Bsym g) ⊨ inj₂ z₂ ⇒ x ] → [ (Bsym f) ∧ (Bsym g) ⊨ inj₁ y ⇒ x ]
      rev z₁ z₂ zp (done p) q = step
        (begin
          from₁ (inj₁ y)
        ≡⟨ Pcong from₁ (Psym p) ⟩
          from₁ (to₁ (inj₂ z₁))
        ≡⟨ from-to₁ (inj₂ z₁) ⟩
          inj₂ z₁
        ∎)
        (begin
          to₂ z₁
        ≡⟨ Pcong to₂ (Psym zp) ⟩
          to₂ (from₂ z₂)
        ≡⟨ to-from₂ z₂ ⟩
          z₂
        ∎)
        q

      rev z₁ z₂ zp (step {dp} {dq} {dr} {ds} p₁ p₂ p) q = rev dr dq p₂ p (step
        (begin
          from₁ (inj₂ dq)
        ≡⟨ Pcong from₁ (Psym p₁) ⟩
          from₁ (to₁ (inj₂ z₁))
        ≡⟨ from-to₁ (inj₂ z₁) ⟩
          inj₂ z₁
        ∎)
        (begin
          to₂ z₁
        ≡⟨ Pcong to₂ (Psym zp) ⟩
          to₂ (from₂ z₂)
        ≡⟨ to-from₂ z₂ ⟩
          z₂
        ∎)
        q)

  injective : ∀ {A B C D} (f : (A ⊔ B) ≅ (C ⊔ D)) (g : B ≅ D) x y z → [ f ∧ g ⊨ y ⇒ x ] → [ f ∧ g ⊨ y ⇒ z ] → x P≡ z
  injective (mkBij to₁ from₁ to-from₁ from-to₁)
            (mkBij to₂ from₂ to-from₂ from-to₂)
            x y z (done p) (done q) =
    inj₁-inj (begin
        inj₁ x
      ≡⟨ Psym p ⟩
        to₁ y
      ≡⟨ q ⟩
        inj₁ z
      ∎)
  injective f@(mkBij to₁ from₁ to-from₁ from-to₁)
            g@(mkBij to₂ from₂ to-from₂ from-to₂)
            x y z
            (step {pp} {pq} {pr} {ps} p₁ p₂ p)
            (step {qp} {qq} {qr} {qs} q₁ q₂ q) = injective f g x (inj₂ qr) z (fix p) q
    where
      fix : [ f ∧ g ⊨ inj₂ pr ⇒ x ] → [ f ∧ g ⊨ inj₂ qr ⇒ x ]
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

  injective (mkBij to₁ from₁ to-from₁ from-to₁) (mkBij to₂ from₂ to-from₂ from-to₂) x y z (done p) (step {dp} {dq} {dr} {ds} q₁ q₂ q) with Ptrans (Psym p) q₁
  ... | ()
  injective (mkBij to₁ from₁ to-from₁ from-to₁) (mkBij to₂ from₂ to-from₂ from-to₂) x y z (step p₁ p₂ p) (done q) with Ptrans (Psym p₁) q
  ... | ()

  module Run2 (A B C D : Expr)
              (A+≅C+D : A + B ≡ C + D)
              (≅D : B ≡ D)
              where

    f : lift (A + B) ≅ lift (C + D)
    f = bijection A+≅C+D

    g : lift B ≅ lift D
    g = bijection ≅D

    L : Expr
    L = A + B

    module CntD where
      open Data.List.Countdown (record { Carrier = lift D
                                        ; _≈_ = _P≡_
                                        ; isDecEquivalence = record { isEquivalence = record { refl = Prefl
                                                                                              ; sym = Psym
                                                                                              ; trans = Ptrans
                                                                                              }
                                                                    ; _≟_ = equal D -- _D≟_
                                                                    }
                                        }) public

    module CntL where
      open Data.List.Countdown (record { Carrier = lift L
                                        ; _≈_ = _P≡_
                                        ; isDecEquivalence = record { isEquivalence = record { refl = Prefl
                                                                                              ; sym = Psym
                                                                                              ; trans = Ptrans
                                                                                              }
                                                                    ; _≟_ = equal L -- _L≟_
                                                                    }
                                        }) public

    lemma : ∀ {A : Set} (x : A) x' xs → ¬ x ∈ xs → x' ∈ xs → ¬ x P≡ x'
    lemma x x' (x₁ L∷ xs) x∉xs (here x'≡x₁) = λ x≡x' → x∉xs (here (Ptrans x≡x' x'≡x₁))
    lemma x x' (x₁ L∷ xs) x∉xs (there x'∈xs) = lemma x x' xs (λ p → x∉xs (there p)) x'∈xs

    y-contr : ∀ {w} {W : Set w}
            → ∀ x x' xs {y}
            → ¬ x ∈ xs
            → x' ∈ xs
            → getTo f x P≡ inj₂ y
            → getTo f x' P≡ inj₂ y
            → W
    y-contr x x' xs x∉xs x'∈xs x↦y x'↦y =
      let x≠x' = lemma x x' xs x∉xs x'∈xs
          x≡x' = (begin
                    x
                  ≡⟨ Psym (getFromTo f x) ⟩
                    getFrom f (getTo f x)
                  ≡⟨ Pcong (getFrom f) (Ptrans x↦y (Psym x'↦y)) ⟩
                    getFrom f (getTo f x')
                  ≡⟨ getFromTo f x' ⟩
                    x'
                  ∎)
      in ⊥-elim (x≠x' x≡x')

    x-contr : ∀ {x} {w} {W : Set w}
            → ∀ y y' ys
            → ¬ y ∈ ys
            → y' ∈ ys
            → getFrom g y P≡ x
            → getFrom g y' P≡ x
            → W
    x-contr {x} y y' ys y∉ys y'∈ys y↦x y'↦x =
      let y≠y' = lemma y y' ys y∉ys y'∈ys
          y≡y' = (begin
                  y
                  ≡⟨ Psym (getToFrom g y) ⟩
                  getTo g (getFrom g y)
                  ≡⟨ Pcong (getTo g) y↦x ⟩
                  getTo g x
                  ≡⟨ Pcong (getTo g) (Psym y'↦x) ⟩
                  getTo g (getFrom g y')
                  ≡⟨ getToFrom g y' ⟩
                  y'
                  ∎)
      in ⊥-elim (y≠y' y≡y')

    run2 : ∀ {m n} → (xs : List (lift L))
                    → (ys : List (lift D))
                    → ((x : lift L) → x ∈ xs → (inj₂-p : ∃ (λ x' → x P≡ inj₂ x')) → Σ (lift D) (λ y → getFrom g y P≡ (proj₁ inj₂-p) × y ∈ ys))
                    → ((y' : lift D) → y' ∈ ys → Σ (lift L) (λ x' → getTo f x' P≡ (inj₂ y') × x' ∈ xs))
                    → xs CntL.⊕ m
                    → ys CntD.⊕ n
                    → (x : lift B)
                    → ¬ (inj₂ x) ∈ xs
                    → Σ (lift D) (λ y' → getFrom g y' P≡ x × y' ∈ ys)
                    → Σ (lift C) (λ y → [ f ∧ g ⊨ inj₂ x ⇒ y ])

    -- All D's seen
    run2 {m} {ℕzero} xs ys preL preD cntL cntD x x∉xs xPre with getTo f (inj₂ x) | inspect (getTo f) (inj₂ x)
    run2 {m} {ℕzero} xs ys preL preD cntL cntD x x∉xs xPre | inj₁ y | [ x↦y ] = y , done x↦y
    run2 {m} {ℕzero} xs ys preL preD cntL cntD x x∉xs xPre | inj₂ y | [ x↦y ] with CntD.lookup! cntD y
    run2 {m} {ℕzero} xs ys preL preD cntL cntD x x∉xs xPre | inj₂ y | [ x↦y ] | y∈ys with preD y y∈ys
    run2 {m} {ℕzero} xs ys preL preD cntL cntD x x∉xs xPre | inj₂ y | [ x↦y ] | y∈ys | x' , x'↦y , x'∈xs = y-contr (inj₂ x) x' xs x∉xs x'∈xs x↦y x'↦y

    -- All B's seen
    run2 {ℕzero} {ℕsuc n}  xs ys preL preD cntL cntD x x∉xs xPre with getTo f (inj₂ x) | inspect (getTo f) (inj₂ x)
    run2 {ℕzero} {ℕsuc n} xs ys preL preD cntL cntD x x∉xs xPre | inj₁ y | [ x↦y ] = y , done x↦y
    run2 {ℕzero} {ℕsuc n} xs ys preL preD cntL cntD x x∉xs xPre | inj₂ y | [ x↦y ] with CntD.lookup cntD y
    run2 {ℕzero} {ℕsuc n} xs ys preL preD cntL cntD x x∉xs xPre | inj₂ y | [ x↦y ] | yes y∈ys with preD y y∈ys
    run2 {ℕzero} {ℕsuc n} xs ys preL preD cntL cntD x x∉xs xPre | inj₂ y | [ x↦y ] | yes y∈ys | x' , x'↦y , x'∈xs = y-contr (inj₂ x) x' xs x∉xs x'∈xs x↦y x'↦y
    run2 {ℕzero} {ℕsuc n} xs ys preL preD cntL cntD x x∉xs xPre | inj₂ y | [ x↦y ] | no  y∉ys with getFrom g y | inspect (getFrom g) y
    run2 {ℕzero} {ℕsuc n} xs ys preL preD cntL cntD x x∉xs xPre | inj₂ y | [ x↦y ] | no  y∉ys | x' | [ y↦x' ] with CntL.lookup! cntL (inj₂ x')
    run2 {ℕzero} {ℕsuc n} xs ys preL preD cntL cntD x x∉xs xPre | inj₂ y | [ x↦y ] | no  y∉ys | x' | [ y↦x' ] | x'∈xs with preL (inj₂ x') x'∈xs (x' , Prefl)
    run2 {ℕzero} {ℕsuc n} xs ys preL preD cntL cntD x x∉xs xPre | inj₂ y | [ x↦y ] | no  y∉ys | x' | [ y↦x' ] | x'∈xs | y' , y'↦x' , y'∈ys = x-contr y y' ys y∉ys y'∈ys y↦x' y'↦x'

    -- At least one unseen B and D
    run2 {ℕsuc m} {ℕsuc n} xs ys preL preD cntL cntD x x∉xs xPre with getTo f (inj₂ x) | inspect (getTo f) (inj₂ x)
    run2 {ℕsuc m} {ℕsuc n} xs ys preL preD cntL cntD x x∉xs xPre | inj₁ y | [ x↦y ] = y , done x↦y
    run2 {ℕsuc m} {ℕsuc n} xs ys preL preD cntL cntD x x∉xs xPre | inj₂ y | [ x↦y ] with CntD.lookup cntD y
    run2 {ℕsuc m} {ℕsuc n} xs ys preL preD cntL cntD x x∉xs xPre | inj₂ y | [ x↦y ] | yes y∈ys with preD y y∈ys
    run2 {ℕsuc m} {ℕsuc n} xs ys preL preD cntL cntD x x∉xs xPre | inj₂ y | [ x↦y ] | yes y∈ys | x' , x'↦y , x'∈xs = y-contr (inj₂ x) x' xs x∉xs x'∈xs x↦y x'↦y
    run2 {ℕsuc m} {ℕsuc n} xs ys preL preD cntL cntD x x∉xs xPre | inj₂ y | [ x↦y ] | no  y∉ys with getFrom g y | inspect (getFrom g) y
    run2 {ℕsuc m} {ℕsuc n} xs ys preL preD cntL cntD x x∉xs xPre | inj₂ y | [ x↦y ] | no  y∉ys | x' | [ y↦x' ] with CntL.lookup cntL (inj₂ x')
    run2 {ℕsuc m} {ℕsuc n} xs ys preL preD cntL cntD x x∉xs xPre | inj₂ y | [ x↦y ] | no  y∉ys | x' | [ y↦x' ] | yes x'∈xs with preL (inj₂ x') x'∈xs (x' , Prefl)
    run2 {ℕsuc m} {ℕsuc n} xs ys preL preD cntL cntD x x∉xs xPre | inj₂ y | [ x↦y ] | no  y∉ys | x' | [ y↦x' ] | yes x'∈xs | y' , y'↦x' , y'∈ys = x-contr y y' ys y∉ys y'∈ys y↦x' y'↦x'
    run2 {ℕsuc m} {ℕsuc n} xs ys preL preD cntL cntD x x∉xs xPre | inj₂ y | [ x↦y ] | no  y∉ys | x' | [ y↦x' ] | no  x'∉xs
      with run2 (inj₂ x L∷ xs)
                (y L∷ ys)
                (λ { .(inj₂ x) (here Prefl) (x'' , Prefl) → case xPre of (λ { (y₁ , y₁↦x , y₁∈ys) → y₁ , y₁↦x , there y₁∈ys })
                    ; x₁ (there x₁∈xs) (x'' , Prefl) → case preL x₁ x₁∈xs (x'' , Prefl) of (λ { (y₁ , y₁↦x₁ , y₁∈ys) → y₁ , y₁↦x₁ , there y₁∈ys })
                    })
                (λ { .y (here Prefl) → inj₂ x , x↦y , here Prefl
                    ; y₁ (there y₁∈ys) → case preD y₁ y₁∈ys of (λ { (x₁ , x₁↦y₁ , x₁∈xs) → x₁ , x₁↦y₁ , there x₁∈xs })
                    })
                (CntL.insert cntL (inj₂ x) x∉xs)
                (CntD.insert cntD y y∉ys)
                x'
                (λ { (here x'≡x) → case xPre of (λ { (y₁ , y₁↦x , y₁∈ys) → lemma y y₁ ys y∉ys y₁∈ys (begin
                                                                                                      y
                                                                                                    ≡⟨ Psym (getToFrom g y) ⟩
                                                                                                      getTo g (getFrom g y)
                                                                                                    ≡⟨ Pcong (getTo g) y↦x' ⟩
                                                                                                      getTo g x'
                                                                                                    ≡⟨ Pcong (getTo g) (inj₂-inj x'≡x) ⟩
                                                                                                      getTo g x
                                                                                                    ≡⟨ Pcong (getTo g) (Psym y₁↦x) ⟩
                                                                                                      getTo g (getFrom g y₁)
                                                                                                    ≡⟨ getToFrom g y₁ ⟩
                                                                                                      y₁
                                                                                                    ∎) })
                    ; (there x'∈xs) → x'∉xs x'∈xs
                    })
                (y , (y↦x' , here Prefl))
    run2 {ℕsuc m} {ℕsuc n} xs ys preL preD cntL cntD x x∉xs xPre | inj₂ y | [ x↦y ] | no y∉ys | x' | [ y↦x' ] | (no x'∉xs) | z , zp = z , step x↦y y↦x' zp

    remove : ∀ {S : Set} {x} → (xs : List S) → (x ∈ xs) → List S
    remove (x L∷ xs) (here p) = xs
    remove (x L∷ xs) (there p) = x L∷ remove xs p

    bring-to-front : ∀ {S : Set} {x} → (xs : List S) → (x ∈ xs) → List S
    bring-to-front {S} {x} xs p = x L∷ remove xs p

    ∈tail : ∀ {S : Set} {x : S} {xs : List S} {y} → y ∈ (x L∷ xs) → ¬ y P≡ x → y ∈ xs
    ∈tail {S} {x} {xs} {y} (here p) q = ⊥-elim (q p)
    ∈tail (there p) q = p

    bring-to-front-exhaustive : ∀ {S : Set} {x} → (xs : List S) → (ex : (y : S) → y ∈ xs) → ((a b : S) → Dec (a P≡ b)) → ((y : S) → y ∈ bring-to-front xs (ex x))
    bring-to-front-exhaustive {S} {x} xs ex _≟_ y with y ≟ x
    bring-to-front-exhaustive {S} {x} xs ex _≟_ y | yes p = here p
    bring-to-front-exhaustive {S} {x} xs ex _≟_ y | no ¬p = there (getit xs (ex x) (ex y))
      where
        getit : ∀ (ps : List S) → (x∈ps : x ∈ ps) → y ∈ ps → y ∈ remove ps x∈ps
        getit (x₁ L∷ xs) (here px) (here px₁) = ⊥-elim (¬p (Ptrans px₁ (Psym px)))
        getit (x₁ L∷ xs) (here px) (there y∈xs) = y∈xs
        getit (x₁ L∷ xs) (there x∈xs) (here px) = here px
        getit (x₁ L∷ xs) (there x∈xs) (there y∈xs) = there (getit xs x∈xs y∈xs)

    nothing-in-empty : ∀ {A : Set} → (x : A) → (x ∈ L[] → ⊥)
    nothing-in-empty x ()

    explicit1 : ∀ {x} → (DecSetoid.setoid (record { Carrier = lift L
                                                  ; _≈_ = _P≡_
                                                  ; isDecEquivalence = record { isEquivalence = record { refl = λ {x} → Prefl
                                                                                                       ; sym = Psym
                                                                                                       ; trans = Ptrans
                                                                                                       }
                                                                              ; _≟_ = equal L
                                                                              }
                                                  })
                        Membership.∈ inj₁ x) L[] → ⊥
    explicit1 ()

    explicit2 : ∀ {y} → (DecSetoid.setoid (record { Carrier = lift D
                                                  ; _≈_ = _P≡_
                                                  ; isDecEquivalence = record { isEquivalence = record { refl = λ {y} → Prefl
                                                                                                       ; sym = Psym
                                                                                                       ; trans = Ptrans
                                                                                                       }
                                                                              ; _≟_ = equal D
                                                                              }
                                                  })
                        Membership.∈ y) L[] → ⊥
    explicit2 ()

    run : (x : lift A) → Σ (lift C) (λ y → [ f ∧ g ⊨ inj₁ x ⇒ y ])
    run x with getTo f (inj₁ x) | inspect (getTo f) (inj₁ x)
    run x | inj₁ y | [ x→y ] = y , (done x→y)
    run x | inj₂ y | [ x→y ] with getFrom g y | inspect (getFrom g) y
    run x | inj₂ y | [ x→y ] | x' | [ y→x' ]
        with run2 (inj₁ x L∷ L[]) (y L∷ L[])
                  (λ { .(inj₁ x) (here Prefl) (_ , ())
                    ; _ (there ()) _
                    })
                  (λ { y' (here Prefl) → inj₁ x , x→y , here Prefl
                    ; _ (there ())
                    })
                  (CntL.insert (CntL.emptyFromList (bring-to-front (generate (A + B)) (exhaustive (A + B) (inj₁ x))) (bring-to-front-exhaustive (generate (A + B)) (exhaustive (A + B)) (equal (A + B)))) (inj₁ x) explicit1)
                  (CntD.insert (CntD.emptyFromList (bring-to-front (generate D) (exhaustive D y)) (bring-to-front-exhaustive (generate D) (exhaustive D) (equal D))) y explicit2)
                  x' (λ { (here ()) ; (there ()) }) (y , y→x' , here Prefl)
    run x | inj₂ y | [ x→y ] | x' | [ y→x' ] | (y' , prf) = y' , step x→y y→x' prf

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
+-cancel {A} {B} {C} {D} p q = proof (+-inj₁ (equality p) (equality q)) (mkBij to from to-from from-to)
  where

    to : lift A → lift C
    to x with run x where open Run2 A B C D p q
    to x | y , prf = y

    from : lift C → lift A
    from y with run y where open Run2 C D A B (sym p) (sym q)
    from y | x , prf = x

    symFix : ∀ {A B C D : Expr} (p : (A + B) ≡ (C + D)) (q : B ≡ D) → ∀ x y → [ bijection (sym p) ∧ bijection (sym q) ⊨ inj₁ y ⇒ x ] → [ Bsym (bijection p) ∧ Bsym (bijection q) ⊨ inj₁ y ⇒ x ]
    symFix (proof x₁ x₂) (proof x₃ x₄) x y (step x₅ x₆ prf) = step x₅ x₆ prf
    symFix (proof x₁ x₂) q₁ x y (done x₃) = done x₃

    to-from : ∀ y → to (from y) P≡ y
    to-from y with run y where open Run2 C D A B (sym p) (sym q)
    to-from y | x , prf with run x where open Run2 A B C D p q
    to-from y | x , prf | z , prf2 = injective (bijection p) (bijection q) z (inj₁ x) y prf2 (fix (reverse (Bsym (bijection p)) (Bsym (bijection q)) y x (symFix p q x y prf)))
      where
        symsym : ∀ {A B} → (t : A ≅ B) → Bsym (Bsym t) P≡ t
        symsym (mkBij to₁ from₁ x₁ x₂) = Prefl

        fix : [ Bsym (Bsym (bijection p)) ∧ Bsym (Bsym (bijection q)) ⊨ inj₁ x ⇒ y ] → [ bijection p ∧ bijection q ⊨ inj₁ x ⇒ y ]
        fix t rewrite symsym (bijection p) | symsym (bijection q) = t

    from-to : ∀ x → from (to x) P≡ x
    from-to x with run x where open Run2 A B C D p q
    from-to x | y , prf with run y where open Run2 C D A B (sym p) (sym q)
    from-to x | y , prf | z , prf2 = injective (Bsym (bijection p)) (Bsym (bijection q)) z (inj₁ y) x (symFix p q z y prf2) (reverse (bijection p) (bijection q) x y prf)
