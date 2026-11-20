{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.DS.Univalent.Gluing where

-- Names for the members of a family over a named cover. Let T : A → Set ℓ
-- be a family of codes. A named cover of a family B over the decoding of
-- a code a is a code of a covering domain, an owner map from its decoding
-- onto that of a, and a name, up to isomorphism, of the member of B at
-- each owner (`Named-Cover`). At a point w of the fiber of the owner map
-- at x, B x is the decoding of the name at w, through the name's
-- isomorphism and the transport along w's identification (`named-at`).
--
-- Every member of B is the limit of the maps out of the iterated joins of
-- its fiber (Foundation.Joins, `members-are-join-limits`). Given formers
-- on the family with their decoding laws (Mahlo.Decoding), that limit is
-- named up to isomorphism through Univalent.Names:
--
-- * the fiber is a sum of identity types (`fiber-has-a-name`);
-- * maps from it into B x are a product whose factor at w is named by the
--   name at w (`maps-have-names`);
-- * each stage is a sum of such maps, the stage below and a product of
--   identity types of the stage below (`join-maps-have-names`, by
--   recursion on the stage);
-- * the limit is a sum of a product over the lifted natural numbers and a
--   product of identity types (`sequences-have-names`,
--   `limit-has-a-name`).
--
-- So every member of B has a name up to isomorphism, as a function of the
-- point of the arity (`named-covers-name-their-members`):
--
--   Named-Cover a B  →  Π (x : T a). Isomorphic-Name (B x),
--
-- with extensionality for the dependent functions of level ℓ alone: no
-- set hypothesis, descent datum or coherence above identity types. No
-- choice is made, since the names are the codes of the limits, and no
-- univalence is used. The child of a closure, with `child-formers` and
-- `child-decoding` of Mahlo.Decoding, is such a family.

open import SPT.Base
open import SPT.Foundation.Covers using (Cover)
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.Fibers using (fiber)
open import SPT.Foundation.Isomorphisms using
  (_≅_; ≅-refl; ≅-trans; ≅-sym; transport-is-isomorphism)
open import SPT.Foundation.Joins using
  ( join-maps; constant-map; restriction; Join-Limit; constant-family
  ; members-are-join-limits )
open import SPT.Foundation.Limits.Sequential using (limits-are-sums)
open import SPT.Foundation.Univalence using (equivalence-to-isomorphism)
open import SPT.Mahlo.Decoding using (DecodingLaws)
open import SPT.Mahlo.Specification using (Formers)
open import SPT.Mahlo.DS.Univalent.Names using
  ( Isomorphic-Name; sums-have-isomorphic-names
  ; products-have-isomorphic-names; identity-types-have-isomorphic-names )

------------------------------------------------------------------------
-- Named covers

module _ {κ ℓ : Level} {A : Set κ} (T : A → Set ℓ) where

  -- Mathematical shape: a code of a covering domain, an owner map onto the
  -- arity, and names of the members of B at the owners.
  record Named-Cover (a : A) (B : T a → Set ℓ) : Set (κ ⊔ lsuc ℓ) where
    field
      domain : A
      owner : T domain → T a
      names : T domain → A
      named : (e : T domain) → T (names e) ≅ B (owner e)
      covers : Cover ℓ owner

------------------------------------------------------------------------
-- Sequences of named types

-- Functions on the lifted natural numbers are sequences.
sequences-over-lifted-naturals : {ℓ : Level} (P : ℕ → Set ℓ) →
  ((i : Lift ℓ ℕ) → P (lower i)) ≅ ((n : ℕ) → P n)
sequences-over-lifted-naturals P = record
  { forward = λ g n → g (lift n)
  ; backward = λ f i → f (lower i)
  ; backward-forward = λ g → refl
  ; forward-backward = λ f → refl
  }

module _ {κ ℓ : Level} {A : Set κ} {T : A → Set ℓ}
  (Q : Formers A T) (laws : DecodingLaws Q)
  (functions : (X : Set ℓ) (Z : X → Set ℓ) → FunExt X Z) where

  -- A sequence of named types: a product over the lifted natural numbers.
  sequences-have-names : (P : ℕ → Set ℓ) →
    ((n : ℕ) → Isomorphic-Name T (P n)) →
    Isomorphic-Name T ((n : ℕ) → P n)
  sequences-have-names P named-stages =
    let product = products-have-isomorphic-names Q laws functions
                    (Lift ℓ ℕ) (λ i → P (lower i))
                    ( Formers.natural Q
                    , transport-is-isomorphism id
                        (DecodingLaws.natural-β laws))
                    (λ i → named-stages (lower i))
    in pr₁ product , ≅-trans (pr₂ product) (sequences-over-lifted-naturals P)

------------------------------------------------------------------------
-- The members of a named cover are named

module _ {κ ℓ : Level} {A : Set κ} {T : A → Set ℓ} {a : A}
  {B : T a → Set ℓ} (N : Named-Cover T a B) where

  open Named-Cover N

  -- At a point of the fiber, B x is the decoding of the name there.
  named-at : (x : T a) (w : fiber owner x) → T (names (pr₁ w)) ≅ B x
  named-at x w =
    ≅-trans (named (pr₁ w)) (transport-is-isomorphism B (pr₂ w))

  -- The fiber of the owner map at x: a sum over the domain of identity
  -- types of the arity.
  fiber-has-a-name : (Q : Formers A T) → DecodingLaws Q → (x : T a) →
    Isomorphic-Name T (fiber owner x)
  fiber-has-a-name Q laws x =
    sums-have-isomorphic-names Q laws (T domain) (λ e → owner e ＝ x)
      (domain , ≅-refl)
      (λ e → identity-types-have-isomorphic-names Q laws (T a)
        (a , ≅-refl) (owner e) x)

  module _ (Q : Formers A T) (laws : DecodingLaws Q)
    (functions : (X : Set ℓ) (Z : X → Set ℓ) → FunExt X Z) where

    -- Maps from the fiber into B x: the factor at w named by the name at w.
    maps-have-names : (x : T a) →
      Isomorphic-Name T (fiber owner x → B x)
    maps-have-names x =
      products-have-isomorphic-names Q laws functions (fiber owner x)
        (λ w → B x) (fiber-has-a-name Q laws x)
        (λ w → names (pr₁ w) , named-at x w)

    join-maps-have-names : (x : T a) (n : ℕ) →
      Isomorphic-Name T (join-maps (fiber owner x) (B x) n)
    join-maps-have-names x zero = maps-have-names x
    join-maps-have-names x (suc n) =
      sums-have-isomorphic-names Q laws (fiber owner x → B x)
        (λ f →
          Σ (join-maps (fiber owner x) (B x) n) (λ g →
            (w : fiber owner x) →
              constant-map (fiber owner x) (B x) n (f w) ＝ g))
        (maps-have-names x)
        (λ f →
          sums-have-isomorphic-names Q laws
            (join-maps (fiber owner x) (B x) n)
            (λ g → (w : fiber owner x) →
              constant-map (fiber owner x) (B x) n (f w) ＝ g)
            (join-maps-have-names x n)
            (λ g →
              products-have-isomorphic-names Q laws functions
                (fiber owner x)
                (λ w → constant-map (fiber owner x) (B x) n (f w) ＝ g)
                (fiber-has-a-name Q laws x)
                (λ w →
                  identity-types-have-isomorphic-names Q laws
                    (join-maps (fiber owner x) (B x) n)
                    (join-maps-have-names x n)
                    (constant-map (fiber owner x) (B x) n (f w)) g)))

    -- The limit: its stage families and their witnesses, read as a sum.
    limit-has-a-name : (x : T a) →
      Isomorphic-Name T (Join-Limit (fiber owner x) (B x))
    limit-has-a-name x =
      let sum = sums-have-isomorphic-names Q laws
                  ((n : ℕ) → join-maps (fiber owner x) (B x) n)
                  (λ m → (n : ℕ) →
                    restriction (fiber owner x) (B x) n (m (suc n)) ＝ m n)
                  (sequences-have-names Q laws functions
                    (join-maps (fiber owner x) (B x))
                    (join-maps-have-names x))
                  (λ m → sequences-have-names Q laws functions
                    (λ n →
                      restriction (fiber owner x) (B x) n (m (suc n))
                        ＝ m n)
                    (λ n → identity-types-have-isomorphic-names Q laws
                      (join-maps (fiber owner x) (B x) n)
                      (join-maps-have-names x n)
                      (restriction (fiber owner x) (B x) n (m (suc n)))
                      (m n)))
      in pr₁ sum ,
         ≅-trans (pr₂ sum)
           (≅-sym
             (limits-are-sums (λ n higher lower →
               restriction (fiber owner x) (B x) n higher ＝ lower)))

    -- So every member of B is named up to isomorphism.
    named-covers-name-their-members : (x : T a) → Isomorphic-Name T (B x)
    named-covers-name-their-members x =
      pr₁ (limit-has-a-name x) ,
      ≅-trans (pr₂ (limit-has-a-name x))
        (≅-sym
          (equivalence-to-isomorphism
            ( constant-family (fiber owner x) (B x)
            , members-are-join-limits functions covers B x)))
