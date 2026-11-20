{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.DS.Univalent.Collection where

-- Covered Strong Collection in a child names its families. In a closure
-- of the ambient family, take as witnesses over the points of a code a the
-- names up to isomorphism of the members of a family B, with no further
-- evidence. A refinement of these witnesses is a named cover of B
-- (`refinements-are-named-covers`), and covered names of the members make
-- the witnesses total (`names-are-total`). A refinement names the family,
-- by the limits over it in the closure's child, whose formers and laws are
-- `child-formers` and `child-decoding` of Mahlo.Decoding
-- (`refinements-name-families`, Univalent.Gluing), with no set
-- hypothesis. So, in a child with covered Strong Collection
-- (`Covered-Collection` of Universes.ChildCollection), a family whose
-- members are each covered by names is covered by one naming function
-- (`families-are-named`):
--
--   (Π x. Covered ℓ (Isomorphic-Name (B x)))  →
--     Covered ℓ (Π x. Isomorphic-Name (B x)).
--
-- Hence the sum and the product of such a family are covered by names
-- (`sums-of-families-are-named`, `products-of-families-are-named`),
-- through Univalent.Names.

open import SPT.Base
open import SPT.Foundation.Covers using (Covered; map-covered)
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.Isomorphisms using (≅-refl)
import SPT.Mahlo.Ambient as Ambient
open import SPT.Mahlo.Decoding using (child-formers; child-decoding)
import SPT.Mahlo.Specification as Specification
open import SPT.Universes.ChildCollection using
  (Total; Refinement; Covered-Collection)
open import SPT.Mahlo.DS.Univalent.Names using
  ( Isomorphic-Name; sums-have-isomorphic-names
  ; products-have-isomorphic-names )
open import SPT.Mahlo.DS.Univalent.Gluing using
  (Named-Cover; named-covers-name-their-members)

------------------------------------------------------------------------
-- Names as witnesses

module _ {ℓ : Level} {Ψ : Ambient.Operator ℓ} {A : Set ℓ}
  (L : Specification.Closure (Ambient.formers ℓ) Ψ A) where

  open Specification.Closure L using (interpret)

  -- The collected code is the domain; owners and names are read off the
  -- occurrences.
  refinements-are-named-covers : (a : A)
    (B : Specification.Decode (λ X → X) interpret a → Set ℓ) →
    Refinement L a
      (λ x → Isomorphic-Name (Specification.Decode (λ X → X) interpret) (B x))
      (λ x n → Lift ℓ 𝟙) →
    Named-Cover (Specification.Decode (λ X → X) interpret) a B
  refinements-are-named-covers a B r = record
    { domain = Refinement.collected r
    ; owner = λ e → pr₁ (Refinement.occurrence r e)
    ; names = λ e → pr₁ (pr₁ (pr₂ (Refinement.occurrence r e)))
    ; named = λ e → pr₂ (pr₁ (pr₂ (Refinement.occurrence r e)))
    ; covers = Refinement.covered r
    }

  -- Covered names of every member cover every owner by evidence.
  names-are-total : (a : A)
    (B : Specification.Decode (λ X → X) interpret a → Set ℓ) →
    ((x : Specification.Decode (λ X → X) interpret a) →
      Covered ℓ
        (Isomorphic-Name (Specification.Decode (λ X → X) interpret) (B x))) →
    Total L a
      (λ x → Isomorphic-Name (Specification.Decode (λ X → X) interpret) (B x))
      (λ x n → Lift ℓ 𝟙)
  names-are-total a B named x =
    map-covered (λ n → (x , n , lift ⋆) , refl) (named x)

  ----------------------------------------------------------------------
  -- Collection names families

  -- A refinement of the names of its members names a family.
  refinements-name-families :
    ((X : Set ℓ) (Y : X → Set ℓ) → FunExt X Y) → (a : A)
    (B : Specification.Decode (λ X → X) interpret a → Set ℓ) →
    Refinement L a
      (λ x → Isomorphic-Name (Specification.Decode (λ X → X) interpret) (B x))
      (λ x n → Lift ℓ 𝟙) →
    (x : Specification.Decode (λ X → X) interpret a) →
    Isomorphic-Name (Specification.Decode (λ X → X) interpret) (B x)
  refinements-name-families extensionality a B r =
    named-covers-name-their-members (refinements-are-named-covers a B r)
      (child-formers L) (child-decoding (Ambient.laws ℓ) L) extensionality

  families-are-named : ((X : Set ℓ) (Y : X → Set ℓ) → FunExt X Y) →
    Covered-Collection L → (a : A)
    (B : Specification.Decode (λ X → X) interpret a → Set ℓ) →
    ((x : Specification.Decode (λ X → X) interpret a) →
      Covered ℓ
        (Isomorphic-Name (Specification.Decode (λ X → X) interpret) (B x))) →
    Covered ℓ
      ((x : Specification.Decode (λ X → X) interpret a) →
        Isomorphic-Name (Specification.Decode (λ X → X) interpret) (B x))
  families-are-named extensionality collection a B named =
    map-covered (refinements-name-families extensionality a B)
      ( collection a
          (λ x → Isomorphic-Name (Specification.Decode (λ X → X) interpret)
            (B x))
          (λ x n → Lift ℓ 𝟙)
          (names-are-total a B named))

  -- The sum of such a family is covered by names.
  sums-of-families-are-named :
    ((X : Set ℓ) (Y : X → Set ℓ) → FunExt X Y) →
    Covered-Collection L → (a : A)
    (B : Specification.Decode (λ X → X) interpret a → Set ℓ) →
    ((x : Specification.Decode (λ X → X) interpret a) →
      Covered ℓ
        (Isomorphic-Name (Specification.Decode (λ X → X) interpret) (B x))) →
    Covered ℓ
      (Isomorphic-Name (Specification.Decode (λ X → X) interpret)
        (Σ (Specification.Decode (λ X → X) interpret a) B))
  sums-of-families-are-named extensionality collection a B named =
    map-covered
      (sums-have-isomorphic-names (child-formers L)
        (child-decoding (Ambient.laws ℓ) L)
        (Specification.Decode (λ X → X) interpret a) B (a , ≅-refl))
      (families-are-named extensionality collection a B named)

  -- So is its product.
  products-of-families-are-named :
    ((X : Set ℓ) (Y : X → Set ℓ) → FunExt X Y) →
    Covered-Collection L → (a : A)
    (B : Specification.Decode (λ X → X) interpret a → Set ℓ) →
    ((x : Specification.Decode (λ X → X) interpret a) →
      Covered ℓ
        (Isomorphic-Name (Specification.Decode (λ X → X) interpret) (B x))) →
    Covered ℓ
      (Isomorphic-Name (Specification.Decode (λ X → X) interpret)
        ((x : Specification.Decode (λ X → X) interpret a) → B x))
  products-of-families-are-named extensionality collection a B named =
    map-covered
      (products-have-isomorphic-names (child-formers L)
        (child-decoding (Ambient.laws ℓ) L) extensionality
        (Specification.Decode (λ X → X) interpret a) B (a , ≅-refl))
      (families-are-named extensionality collection a B named)
