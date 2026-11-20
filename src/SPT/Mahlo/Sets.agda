{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Sets where

-- The parent of sets of level ℓ. Its codes are small sets: a type of
-- level ℓ with a proof that it is a set (`Small-Set`), decoded by their
-- points; `Operator ℓ` is the type of operators on its families. Under
-- extensionality for the dependent functions of level ℓ the ordinary type
-- formers keep sets (lifts, sums, products, trees over a set of labels,
-- identity types), so they are its formers (`set-formers`), each decoding
-- to the type former by refl (`set-laws`). Being a set is then a
-- proposition, so two small sets are identified exactly when their points
-- are (`small-sets-are-identified-by-their-points`), and under univalence
-- exactly when their points are equivalent (`small-set-identifications`).
-- No reflector is assumed here.

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.Hedberg using
  (decidable-equality-gives-set; ℕ-is-set)
open import SPT.Foundation.Isomorphisms using (_≅_; ≅-trans)
open import SPT.Foundation.Propositions using
  (is-set; propositions-are-sets)
open import SPT.Foundation.Sets using
  ( being-a-set-is-a-proposition; products-of-sets-are-sets
  ; sums-of-sets-are-sets; lifts-of-sets-are-sets )
open import SPT.Foundation.Univalence using
  (Equivalence; is-univalent; idtoeq; equivalence-to-isomorphism)
open import SPT.Foundation.Tree.W using (W)
open import SPT.Mahlo.Decoding using (DecodingLaws)
open import SPT.Foundation.Tree.W.Sets using (trees-over-a-set-are-sets)
import SPT.Mahlo.Specification as Specification

------------------------------------------------------------------------
-- Small sets

record Small-Set (ℓ : Level) : Set (lsuc ℓ) where
  constructor small-set
  field
    points : Set ℓ
    points-form-a-set : is-set points

open Small-Set public

Operator : (ℓ : Level) → Set (lsuc ℓ)
Operator ℓ = Specification.Operator {C = Small-Set ℓ} points

------------------------------------------------------------------------
-- The formers

module _ {ℓ : Level}
  (extensionality : (X : Set ℓ) (Y : X → Set ℓ) → FunExt X Y) where

  set-formers : Specification.Formers (Small-Set ℓ) points
  set-formers = record
    { empty =
        small-set (Lift ℓ 𝟘) (propositions-are-sets (λ x y → 𝟘-elim (lower x)))
    ; unit = small-set (Lift ℓ 𝟙) (propositions-are-sets (λ x y → refl))
    ; two =
        small-set (Lift ℓ 𝟚)
          (lifts-of-sets-are-sets ℓ
            (decidable-equality-gives-set 𝟚-has-decidable-equality))
    ; natural = small-set (Lift ℓ ℕ) (lifts-of-sets-are-sets ℓ ℕ-is-set)
    ; product = λ (a , b) →
        small-set ((x : points a) → points (b x))
          (products-of-sets-are-sets extensionality (points a)
            (λ x → points (b x)) (λ x → points-form-a-set (b x)))
    ; sum = λ (a , b) →
        small-set (Σ (points a) (λ x → points (b x)))
          (sums-of-sets-are-sets (points-form-a-set a)
            (λ x → points-form-a-set (b x)))
    ; tree = λ (a , b) →
        small-set (W (points a) (λ x → points (b x)))
          (trees-over-a-set-are-sets
            (λ x → extensionality (points (b x))
              (λ y → W (points a) (λ z → points (b z))))
            (λ x f g → extensionality (points (b x)) (λ y → f y ＝ g y))
            (points-form-a-set a))
    ; identity = λ a x y →
        small-set (x ＝ y) (propositions-are-sets (points-form-a-set a x y))
    }

  set-laws : DecodingLaws set-formers
  set-laws = record
    { empty-β = refl
    ; unit-β = refl
    ; two-β = refl
    ; natural-β = refl
    ; product-β = λ a b → refl
    ; sum-β = λ a b → refl
    ; tree-β = λ a b → refl
    ; identity-β = λ a x y → refl
    }

  ----------------------------------------------------------------------
  -- Identifications of small sets

  -- Points identified give small sets identified, the proofs being
  -- identified because being a set is a proposition.
  small-set-identification : (c c′ : Small-Set ℓ) →
    points c ＝ points c′ → c ＝ c′
  small-set-identification (small-set X s) (small-set .X s′) refl =
    ap (small-set X) (being-a-set-is-a-proposition extensionality X s s′)

  -- Along an identification of proofs the points stay put.
  points-along-proofs : (X : Set ℓ) {s s′ : is-set X} (q : s ＝ s′) →
    ap points (ap (small-set X) q) ＝ refl
  points-along-proofs X refl = refl

  points-of-small-set-identification : (c c′ : Small-Set ℓ)
    (p : points c ＝ points c′) →
    ap points (small-set-identification c c′ p) ＝ p
  points-of-small-set-identification (small-set X s) (small-set .X s′)
    refl =
    points-along-proofs X (being-a-set-is-a-proposition extensionality X s s′)

  -- The identification made from the points of e is e, since any loop of
  -- proofs is refl.
  small-set-identification-of-points : (c c′ : Small-Set ℓ) (e : c ＝ c′) →
    small-set-identification c c′ (ap points e) ＝ e
  small-set-identification-of-points (small-set X s) .(small-set X s) refl =
    ap (ap (small-set X))
      (propositions-are-sets (being-a-set-is-a-proposition extensionality X)
        s s (being-a-set-is-a-proposition extensionality X s s) refl)

  small-sets-are-identified-by-their-points : (c c′ : Small-Set ℓ) →
    (c ＝ c′) ≅ (points c ＝ points c′)
  small-sets-are-identified-by-their-points c c′ = record
    { forward = ap points
    ; backward = small-set-identification c c′
    ; backward-forward = small-set-identification-of-points c c′
    ; forward-backward = points-of-small-set-identification c c′
    }

  -- Under univalence, identifications of small sets are equivalences of
  -- their points.
  small-set-identifications : is-univalent ℓ → (c c′ : Small-Set ℓ) →
    (c ＝ c′) ≅ Equivalence (points c) (points c′)
  small-set-identifications univalence c c′ =
    ≅-trans (small-sets-are-identified-by-their-points c c′)
      (equivalence-to-isomorphism
        (idtoeq (points c) (points c′) , univalence (points c) (points c′)))
