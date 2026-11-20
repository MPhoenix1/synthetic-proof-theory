{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.DS.Univalent.Names where

-- Names in a family of codes whose formers decode as the type formers.
-- For a family T : A → Set ℓ, a name of a type X up to isomorphism is a
-- code whose decoding is isomorphic to X (`Isomorphic-Name`), and a name of
-- X as a decoding is a code whose decoding is identified with X
-- (`Decoded-Name`); the latter give the former
-- (`decoded-names-are-isomorphic-names`). Given formers on the family with
-- their decoding laws (Mahlo.Decoding), both are closed under the formers
-- over named data:
--
-- * a type with a name up to isomorphism, with a family named pointwise,
--   has its sum named, and under extensionality its product; so has every
--   identity type of it (`sums-have-isomorphic-names`,
--   `products-have-isomorphic-names`,
--   `identity-types-have-isomorphic-names`), the former at the codes read
--   along the isomorphism of the base (`Σ-bicong`, `Π-bicong`,
--   `ap-is-isomorphism` of Foundation.HalfAdjoint);
-- * under extensionality for families of types, the same holds of names as
--   decodings (`sums-of-decoded-names`, `products-of-decoded-names`,
--   `identity-types-of-decoded-names`):
--
--     Decoded-Name X  →  Π x. Decoded-Name (Y x)  →  Decoded-Name (Σ X Y).
--
-- The child of a closure is such a family: its codes are the closure's
-- carrier, its formers and laws `child-formers` and `child-decoding` of
-- Mahlo.Decoding. No univalence is used.

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.HalfAdjoint using
  (ap-is-isomorphism; Σ-bicong; Π-bicong)
open import SPT.Foundation.Isomorphisms using
  (_≅_; forward; backward; ≅-trans; ≅-sym; transport-is-isomorphism)
open import SPT.Mahlo.Decoding using (DecodingLaws)
open import SPT.Mahlo.Specification using (Formers)

------------------------------------------------------------------------
-- Names of a family

module _ {κ ℓ : Level} {A : Set κ} (T : A → Set ℓ) where

  -- Mathematical shape: Σ (k : A). T k ≅ X.
  Isomorphic-Name : Set ℓ → Set (κ ⊔ ℓ)
  Isomorphic-Name X = Σ A (λ k → T k ≅ X)

  -- Mathematical shape: Σ (k : A). T k ＝ X.
  Decoded-Name : Set ℓ → Set (κ ⊔ lsuc ℓ)
  Decoded-Name X = Σ A (λ k → T k ＝ X)

  decoded-names-are-isomorphic-names : (X : Set ℓ) → Decoded-Name X →
    Isomorphic-Name X
  decoded-names-are-isomorphic-names X (k , e) =
    k , transport-is-isomorphism id e

------------------------------------------------------------------------
-- Closure under the formers

module _ {κ ℓ : Level} {A : Set κ} {T : A → Set ℓ}
  (F : Formers A T) (laws : DecodingLaws F) where

  ----------------------------------------------------------------------
  -- Names up to isomorphism

  -- The sum at the codes of the family along E.
  sums-have-isomorphic-names : (X : Set ℓ) (Y : X → Set ℓ) →
    Isomorphic-Name T X → ((x : X) → Isomorphic-Name T (Y x)) →
    Isomorphic-Name T (Σ X Y)
  sums-have-isomorphic-names X Y (k , E) n =
    Formers.sum F (k , λ u → pr₁ (n (forward E u))) ,
    ≅-trans
      ( transport-is-isomorphism id
          (DecodingLaws.sum-β laws k (λ u → pr₁ (n (forward E u)))))
      ( Σ-bicong (λ u → T (pr₁ (n (forward E u)))) Y E
          (λ u → pr₂ (n (forward E u))))

  -- The product at the codes of the family along E.
  products-have-isomorphic-names :
    ((U : Set ℓ) (V : U → Set ℓ) → FunExt U V) →
    (X : Set ℓ) (Y : X → Set ℓ) →
    Isomorphic-Name T X → ((x : X) → Isomorphic-Name T (Y x)) →
    Isomorphic-Name T ((x : X) → Y x)
  products-have-isomorphic-names extensionality X Y (k , E) n =
    Formers.product F (k , λ u → pr₁ (n (forward E u))) ,
    ≅-trans
      ( transport-is-isomorphism id
          (DecodingLaws.product-β laws k (λ u → pr₁ (n (forward E u)))))
      ( Π-bicong (λ u → T (pr₁ (n (forward E u)))) Y
          (extensionality (T k) (λ u → T (pr₁ (n (forward E u)))))
          (extensionality X Y) E (λ u → pr₂ (n (forward E u))))

  -- The identity type at the backward images, read along the action of E
  -- on identifications.
  identity-types-have-isomorphic-names : (X : Set ℓ) →
    Isomorphic-Name T X → (x y : X) → Isomorphic-Name T (x ＝ y)
  identity-types-have-isomorphic-names X (k , E) x y =
    Formers.identity F k (backward E x) (backward E y) ,
    ≅-trans
      ( transport-is-isomorphism id
          (DecodingLaws.identity-β laws k (backward E x) (backward E y)))
      ( ≅-sym (ap-is-isomorphism (≅-sym E) x y))

  ----------------------------------------------------------------------
  -- Names as decodings

  -- The sum at the codes, its decoding law followed by the identification
  -- of the families of decodings.
  sums-of-decoded-names : ((U : Set ℓ) → FunExt U (λ _ → Set ℓ)) →
    (X : Set ℓ) (Y : X → Set ℓ) → Decoded-Name T X →
    ((x : X) → Decoded-Name T (Y x)) → Decoded-Name T (Σ X Y)
  sums-of-decoded-names families X Y (k , refl) n =
    Formers.sum F (k , λ u → pr₁ (n u)) ,
    DecodingLaws.sum-β laws k (λ u → pr₁ (n u))
      ∙ ap (Σ (T k))
          (families (T k) (λ u → T (pr₁ (n u))) Y (λ u → pr₂ (n u)))

  products-of-decoded-names : ((U : Set ℓ) → FunExt U (λ _ → Set ℓ)) →
    (X : Set ℓ) (Y : X → Set ℓ) → Decoded-Name T X →
    ((x : X) → Decoded-Name T (Y x)) → Decoded-Name T ((x : X) → Y x)
  products-of-decoded-names families X Y (k , refl) n =
    Formers.product F (k , λ u → pr₁ (n u)) ,
    DecodingLaws.product-β laws k (λ u → pr₁ (n u))
      ∙ ap (λ V → (u : T k) → V u)
          (families (T k) (λ u → T (pr₁ (n u))) Y (λ u → pr₂ (n u)))

  identity-types-of-decoded-names : (X : Set ℓ) → Decoded-Name T X →
    (x y : X) → Decoded-Name T (x ＝ y)
  identity-types-of-decoded-names X (k , refl) x y =
    Formers.identity F k x y , DecodingLaws.identity-β laws k x y
