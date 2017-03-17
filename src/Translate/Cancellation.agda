module Translate.Cancellation where

open import Function

open import Translate.Base
open import Translate.Types
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

  module Run2 (A B C D : Expr)
              (A+B≡C+D : A + B ≡ C + D)
              (B≡D : B ≡ D)
              where

    b₁ : lift (A + B) B≡ lift (C + D)
    b₁ = toBijection A+B≡C+D

    b₂ : lift B B≡ lift D
    b₂ = toBijection B≡D

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
            → getTo b₁ x P≡ inj₂ y
            → getTo b₁ x' P≡ inj₂ y
            → W
    y-contr x x' xs x∉xs x'∈xs x↦y x'↦y =
      let x≠x' = lemma x x' xs x∉xs x'∈xs
          x≡x' = (begin
                    x
                  ≡⟨ Psym (getFromTo b₁ x) ⟩
                    getFrom b₁ (getTo b₁ x)
                  ≡⟨ Pcong (getFrom b₁) (Ptrans x↦y (Psym x'↦y)) ⟩
                    getFrom b₁ (getTo b₁ x')
                  ≡⟨ getFromTo b₁ x' ⟩
                    x'
                  ∎)
      in ⊥-elim (x≠x' x≡x')

    x-contr : ∀ {x} {w} {W : Set w}
            → ∀ y y' ys
            → ¬ y ∈ ys
            → y' ∈ ys
            → getFrom b₂ y P≡ x
            → getFrom b₂ y' P≡ x
            → W
    x-contr {x} y y' ys y∉ys y'∈ys y↦x y'↦x =
      let y≠y' = lemma y y' ys y∉ys y'∈ys
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

    run2 : ∀ {m n} → (xs : List (lift L))
                    → (ys : List (lift D))
                    → ((x : lift L) → x ∈ xs → (inj₂-p : ∃ (λ x' → x P≡ inj₂ x')) → Σ (lift D) (λ y → getFrom b₂ y P≡ (proj₁ inj₂-p) × y ∈ ys))
                    → ((y' : lift D) → y' ∈ ys → Σ (lift L) (λ x' → getTo b₁ x' P≡ (inj₂ y') × x' ∈ xs))
                    → xs CntL.⊕ m
                    → ys CntD.⊕ n
                    → (x : lift B)
                    → ¬ (inj₂ x) ∈ xs
                    → Σ (lift D) (λ y' → getFrom b₂ y' P≡ x × y' ∈ ys)
                    → Σ (lift C) (λ y → [ b₁ ∧ b₂ ⊨ inj₂ x ⇒ y ])

    -- All D's seen
    run2 {m} {ℕzero} xs ys preL preD cntL cntD x x∉xs xPre with getTo b₁ (inj₂ x) | inspect (getTo b₁) (inj₂ x)
    run2 {m} {ℕzero} xs ys preL preD cntL cntD x x∉xs xPre | inj₁ y | [ x↦y ] = y , done x↦y
    run2 {m} {ℕzero} xs ys preL preD cntL cntD x x∉xs xPre | inj₂ y | [ x↦y ] with CntD.lookup! cntD y
    run2 {m} {ℕzero} xs ys preL preD cntL cntD x x∉xs xPre | inj₂ y | [ x↦y ] | y∈ys with preD y y∈ys
    run2 {m} {ℕzero} xs ys preL preD cntL cntD x x∉xs xPre | inj₂ y | [ x↦y ] | y∈ys | x' , x'↦y , x'∈xs = y-contr (inj₂ x) x' xs x∉xs x'∈xs x↦y x'↦y

    -- All B's seen
    run2 {ℕzero} {ℕsuc n}  xs ys preL preD cntL cntD x x∉xs xPre with getTo b₁ (inj₂ x) | inspect (getTo b₁) (inj₂ x)
    run2 {ℕzero} {ℕsuc n} xs ys preL preD cntL cntD x x∉xs xPre | inj₁ y | [ x↦y ] = y , done x↦y
    run2 {ℕzero} {ℕsuc n} xs ys preL preD cntL cntD x x∉xs xPre | inj₂ y | [ x↦y ] with CntD.lookup cntD y
    run2 {ℕzero} {ℕsuc n} xs ys preL preD cntL cntD x x∉xs xPre | inj₂ y | [ x↦y ] | yes y∈ys with preD y y∈ys
    run2 {ℕzero} {ℕsuc n} xs ys preL preD cntL cntD x x∉xs xPre | inj₂ y | [ x↦y ] | yes y∈ys | x' , x'↦y , x'∈xs = y-contr (inj₂ x) x' xs x∉xs x'∈xs x↦y x'↦y
    run2 {ℕzero} {ℕsuc n} xs ys preL preD cntL cntD x x∉xs xPre | inj₂ y | [ x↦y ] | no  y∉ys with getFrom b₂ y | inspect (getFrom b₂) y
    run2 {ℕzero} {ℕsuc n} xs ys preL preD cntL cntD x x∉xs xPre | inj₂ y | [ x↦y ] | no  y∉ys | x' | [ y↦x' ] with CntL.lookup! cntL (inj₂ x')
    run2 {ℕzero} {ℕsuc n} xs ys preL preD cntL cntD x x∉xs xPre | inj₂ y | [ x↦y ] | no  y∉ys | x' | [ y↦x' ] | x'∈xs with preL (inj₂ x') x'∈xs (x' , Prefl)
    run2 {ℕzero} {ℕsuc n} xs ys preL preD cntL cntD x x∉xs xPre | inj₂ y | [ x↦y ] | no  y∉ys | x' | [ y↦x' ] | x'∈xs | y' , y'↦x' , y'∈ys = x-contr y y' ys y∉ys y'∈ys y↦x' y'↦x'

    -- At least one unseen B and D
    run2 {ℕsuc m} {ℕsuc n} xs ys preL preD cntL cntD x x∉xs xPre with getTo b₁ (inj₂ x) | inspect (getTo b₁) (inj₂ x)
    run2 {ℕsuc m} {ℕsuc n} xs ys preL preD cntL cntD x x∉xs xPre | inj₁ y | [ x↦y ] = y , done x↦y
    run2 {ℕsuc m} {ℕsuc n} xs ys preL preD cntL cntD x x∉xs xPre | inj₂ y | [ x↦y ] with CntD.lookup cntD y
    run2 {ℕsuc m} {ℕsuc n} xs ys preL preD cntL cntD x x∉xs xPre | inj₂ y | [ x↦y ] | yes y∈ys with preD y y∈ys
    run2 {ℕsuc m} {ℕsuc n} xs ys preL preD cntL cntD x x∉xs xPre | inj₂ y | [ x↦y ] | yes y∈ys | x' , x'↦y , x'∈xs = y-contr (inj₂ x) x' xs x∉xs x'∈xs x↦y x'↦y
    run2 {ℕsuc m} {ℕsuc n} xs ys preL preD cntL cntD x x∉xs xPre | inj₂ y | [ x↦y ] | no  y∉ys with getFrom b₂ y | inspect (getFrom b₂) y
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
                                                                                                    ≡⟨ Psym (getToFrom b₂ y) ⟩
                                                                                                      getTo b₂ (getFrom b₂ y)
                                                                                                    ≡⟨ Pcong (getTo b₂) y↦x' ⟩
                                                                                                      getTo b₂ x'
                                                                                                    ≡⟨ Pcong (getTo b₂) (inj₂-inj x'≡x) ⟩
                                                                                                      getTo b₂ x
                                                                                                    ≡⟨ Pcong (getTo b₂) (Psym y₁↦x) ⟩
                                                                                                      getTo b₂ (getFrom b₂ y₁)
                                                                                                    ≡⟨ getToFrom b₂ y₁ ⟩
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

    run : (x : lift A) → Σ (lift C) (λ y → [ b₁ ∧ b₂ ⊨ inj₁ x ⇒ y ])
    run x with getTo b₁ (inj₁ x) | inspect (getTo b₁) (inj₁ x)
    run x | inj₁ y | [ x→y ] = y , (done x→y)
    run x | inj₂ y | [ x→y ] with getFrom b₂ y | inspect (getFrom b₂) y
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
+-cancel {A} {B} {C} {D} p q = axiom (+-inj₁ (toEquality p) (toEquality q)) (mkBij to from toFrom fromTo)
  where

    to : lift A → lift C
    to x with run x where open Run2 A B C D p q
    to x | y , prf = y

    from : lift C → lift A
    from y with run y where open Run2 C D A B (sym p) (sym q)
    from y | x , prf = x

    toFrom : ∀ y → to (from y) P≡ y
    toFrom y with run y where open Run2 C D A B (sym p) (sym q)
    toFrom y | x , prf with run x where open Run2 A B C D p q
    toFrom y | x , prf | z , prf2 = bijective (toBijection p) (toBijection q) z (inj₁ x) y prf2 (fix (reverse (Bsym (toBijection p)) (Bsym (toBijection q)) y x prf))
      where
        symsym : ∀ {A B} → (t : A B≡ B) → Bsym (Bsym t) P≡ t
        symsym (mkBij to₁ from₁ x₁ x₂) = Prefl

        fix : [ Bsym (Bsym (toBijection p)) ∧ Bsym (Bsym (toBijection q)) ⊨ inj₁ x ⇒ y ] → [ toBijection p ∧ toBijection q ⊨ inj₁ x ⇒ y ]
        fix t rewrite symsym (toBijection p) | symsym (toBijection q) = t

    fromTo : ∀ x → from (to x) P≡ x
    fromTo x with run x where open Run2 A B C D p q
    fromTo x | y , prf with run y where open Run2 C D A B (sym p) (sym q)
    fromTo x | y , prf | z , prf2 = bijective (Bsym (toBijection p)) (Bsym (toBijection q)) z (inj₁ y) x prf2 (reverse (toBijection p) (toBijection q) x y prf)