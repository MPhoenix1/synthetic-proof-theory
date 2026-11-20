{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.DS.Univalent.Covering where

-- Closures that collect names, from weakly initial covers, over a
-- univalent parent (Univalent.Completion). A closure collects names when
-- every family of codes over a code whose members are covered by names is
-- covered by a named cover: choice relative to the closure. Weakly initial
-- covers of every arity with named domains give it: along a projection the
-- names of the members have a section, and the projection's named domain
-- is the cover (`named-cover`, `covered-closures-collect-names`).
--
-- Covering operators of a parent are weakly initial covers of the decoding
-- of every code, with, for every operator Ψ, an operator whose closures
-- name the index and the members of Ψ's family and the domains of the
-- covers of every arity (`Covering-Operators`): Ψ joined with the operator
-- returning the covers (Univalent.Sets, Univalent.Types). A closure of the
-- joined operator is a closure of Ψ on the same codes (`restricted`, through
-- Cedents' `coded`), and it collects names. So:
--
--   plain rule  →  Covering-Operators P  →
--     Σ (R : Π Ψ. Small-Closure Ψ). Π Ψ. Collects-Names (R Ψ)
--
-- (`collection-from-covers`), and with completions closures with unique
-- names for every operator (`unique-names-from-covers`), with no excluded
-- middle and no choice.
--
-- Conversely, a closure that collects names refines every cover of the
-- decoding of a code whose fibers are codes covered by names, by a cover
-- named in the closure (`Named-Refinement`, `summed-refinement`,
-- `collection-refines-covers`). So collecting names is weakly initial
-- covers relative to the closure: it follows from refinements of all
-- covers by small types and gives refinements of the covers with named
-- fibers.

open import SPT.Base
open import SPT.Foundation.Covers using
  ( Covered; Cover; map-covered; composite-of-covers-is-cover
  ; cover-respects-homotopy )
open import SPT.Foundation.Covers.WeaklyInitial using
  ( Weakly-Initial-Covers; isomorphisms-are-covers
  ; first-projections-cover )
open import SPT.Foundation.Fibers using (fiber)
open import SPT.Foundation.Isomorphisms using
  (_≅_; forward; backward; ≅-trans; ≅-sym; transport-is-isomorphism)
open import SPT.Mahlo.Decoding using (DecodingLaws)
import SPT.Mahlo.Specification as Specification
open import SPT.Mahlo.DS.Cedents using (coded; coded-β)
open import SPT.Mahlo.DS.Univalent.Names using (Isomorphic-Name)
open import SPT.Mahlo.DS.Univalent.Gluing using (Named-Cover)
open import SPT.Mahlo.DS.Univalent.Completion using
  ( Univalent-Parent; Small-Closure; Has-Unique-Names; Collects-Names
  ; Completions; unique-names-from-collection )

------------------------------------------------------------------------
-- Weakly initial covers with named domains collect names

-- Along a projection the names of the members have a section. The named
-- domain, read through its isomorphism with the projection's domain, is
-- the cover, and the section gives the names.

module _ {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} (P : Univalent-Parent D)
  {Ψ : Specification.Operator D} {K : Set ℓ}
  (L : Specification.Closure (Univalent-Parent.formers P) Ψ K)
  (W : (a : K) →
    Weakly-Initial-Covers
      (Specification.Decode D (Specification.Closure.interpret L) a))
  (domains-named : (a : K) (i : Weakly-Initial-Covers.index (W a)) →
    Isomorphic-Name
      (Specification.Decode D (Specification.Closure.interpret L))
      (Weakly-Initial-Covers.domain (W a) i))
  where

  open Specification.Closure L using (interpret)

  named-cover : (a : K) (B : Specification.Decode D interpret a → C)
    (s : Σ (Weakly-Initial-Covers.index (W a)) (λ i →
      (z : Weakly-Initial-Covers.domain (W a) i) →
        Isomorphic-Name (Specification.Decode D interpret)
          (D (B (Weakly-Initial-Covers.projection (W a) i z))))) →
    Named-Cover (Specification.Decode D interpret) a (λ x → D (B x))
  named-cover a B s = record
    { domain = pr₁ (domains-named a (pr₁ s))
    ; owner =
        Weakly-Initial-Covers.projection (W a) (pr₁ s)
        ∘ forward (pr₂ (domains-named a (pr₁ s)))
    ; names = λ z → pr₁ (pr₂ s (forward (pr₂ (domains-named a (pr₁ s))) z))
    ; named = λ z → pr₂ (pr₂ s (forward (pr₂ (domains-named a (pr₁ s))) z))
    ; covers =
        composite-of-covers-is-cover
          (isomorphisms-are-covers (pr₂ (domains-named a (pr₁ s))))
          (Weakly-Initial-Covers.projections-cover (W a) (pr₁ s))
    }

  covered-closures-collect-names : Collects-Names P L
  covered-closures-collect-names a B merely =
    map-covered (named-cover a B)
      (Weakly-Initial-Covers.sections (W a)
        (λ x → Isomorphic-Name (Specification.Decode D interpret) (D (B x)))
        merely)

------------------------------------------------------------------------
-- Covering operators

-- Mathematical shape: weakly initial covers of every decoding, and for
-- every operator Ψ an operator whose closures name Ψ's index and members
-- and the domains of the covers of every arity.
record Covering-Operators {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ}
  (P : Univalent-Parent D) : Set (κ ⊔ lsuc ℓ) where
  field
    covers : (c : C) → Weakly-Initial-Covers (D c)
    joined : Specification.Operator D → Specification.Operator D
    index-is-named : (Ψ : Specification.Operator D) {K : Set ℓ}
      (L : Specification.Closure (Univalent-Parent.formers P) (joined Ψ) K)
      (F : Specification.Family
        (Specification.Decode D (Specification.Closure.interpret L))) →
      Specification.Name (Specification.Closure.interpret L)
        (pr₁ (Ψ (Specification.map D (Specification.Closure.interpret L) F)))
    members-are-named : (Ψ : Specification.Operator D) {K : Set ℓ}
      (L : Specification.Closure (Univalent-Parent.formers P) (joined Ψ) K)
      (F : Specification.Family
        (Specification.Decode D (Specification.Closure.interpret L)))
      (y : D (pr₁ (Ψ
        (Specification.map D (Specification.Closure.interpret L) F)))) →
      Specification.Name (Specification.Closure.interpret L)
        (pr₂ (Ψ (Specification.map D (Specification.Closure.interpret L) F))
          y)
    domains-are-named : (Ψ : Specification.Operator D) {K : Set ℓ}
      (L : Specification.Closure (Univalent-Parent.formers P) (joined Ψ) K)
      (a : K)
      (i : Weakly-Initial-Covers.index
        (covers (Specification.Closure.interpret L a))) →
      Isomorphic-Name
        (Specification.Decode D (Specification.Closure.interpret L))
        (Weakly-Initial-Covers.domain
          (covers (Specification.Closure.interpret L a)) i)

-- A closure of the joined operator is a closure of Ψ on the same codes.

module _ {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} (P : Univalent-Parent D)
  (S : Covering-Operators P) (Ψ : Specification.Operator D) {K : Set ℓ}
  (L : Specification.Closure (Univalent-Parent.formers P)
    (Covering-Operators.joined S Ψ) K)
  where

  open Specification.Closure L using (interpret)

  restricted : Specification.Closure (Univalent-Parent.formers P) Ψ K
  restricted = record
    { interpret = interpret
    ; empty = Specification.Closure.empty L
    ; unit = Specification.Closure.unit L
    ; two = Specification.Closure.two L
    ; natural = Specification.Closure.natural L
    ; product = Specification.Closure.product L
    ; sum = Specification.Closure.sum L
    ; tree = Specification.Closure.tree L
    ; identity = Specification.Closure.identity L
    ; inner = λ F →
        coded (Univalent-Parent.code-families P) L
          (pr₁ (Ψ (Specification.map D interpret F)))
          (pr₂ (Ψ (Specification.map D interpret F)))
          (Covering-Operators.index-is-named S Ψ L F)
          (Covering-Operators.members-are-named S Ψ L F)
    ; inner-β = λ F →
        coded-β (Univalent-Parent.code-families P) L
          (pr₁ (Ψ (Specification.map D interpret F)))
          (pr₂ (Ψ (Specification.map D interpret F)))
          (Covering-Operators.index-is-named S Ψ L F)
          (Covering-Operators.members-are-named S Ψ L F)
    }

------------------------------------------------------------------------
-- Collection and unique names from covering operators

module _ {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} (P : Univalent-Parent D)
  (S : Covering-Operators P) where

  -- Reflect each operator joined with the covers.
  collection-from-covers :
    (R : (Ψ : Specification.Operator D) → Small-Closure P Ψ) →
    Σ ((Ψ : Specification.Operator D) → Small-Closure P Ψ)
      (λ R′ → (Ψ : Specification.Operator D) →
        Collects-Names P (pr₂ (R′ Ψ)))
  collection-from-covers R =
    (λ Ψ →
      pr₁ (R (Covering-Operators.joined S Ψ)) ,
      restricted P S Ψ (pr₂ (R (Covering-Operators.joined S Ψ)))) ,
    (λ Ψ →
      let L = pr₂ (R (Covering-Operators.joined S Ψ))
      in covered-closures-collect-names P (restricted P S Ψ L)
           (λ a →
             Covering-Operators.covers S (Specification.Closure.interpret L a))
           (Covering-Operators.domains-are-named S Ψ L))

  -- With completions, closures with unique names (Univalent.Completion).
  unique-names-from-covers : Completions ℓ C →
    (R : (Ψ : Specification.Operator D) → Small-Closure P Ψ) →
    (Ψ : Specification.Operator D) →
    Σ (Small-Closure P Ψ) (λ L → Has-Unique-Names P (pr₂ L))
  unique-names-from-covers completions R =
    unique-names-from-collection P completions
      (pr₁ (collection-from-covers R)) (pr₂ (collection-from-covers R))

------------------------------------------------------------------------
-- Collection refines covers with covered named fibers

-- A cover of the decoding of a code, whose fibers are codes each covered
-- by names, has a named cover of its fibers when the closure collects
-- names. Summed in the closure, its names form a named domain that maps
-- into the cover's domain over the arity, and that map is a cover.

module _ {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} (P : Univalent-Parent D)
  {Ψ : Specification.Operator D} {K : Set ℓ}
  (L : Specification.Closure (Univalent-Parent.formers P) Ψ K)
  where

  open Specification.Closure L using (interpret)

  -- Mathematical shape: a code d with r : D d → E and q ∘ r a cover.
  record Named-Refinement (a : K) {E : Set ℓ}
    (q : E → Specification.Decode D interpret a) : Set (κ ⊔ lsuc ℓ) where
    field
      domain : K
      refining : Specification.Decode D interpret domain → E
      refines : Cover ℓ (q ∘ refining)

  summed-refinement : (a : K) {E : Set ℓ}
    (q : E → Specification.Decode D interpret a) → Cover ℓ q →
    (F : Specification.Decode D interpret a → C) →
    ((x : Specification.Decode D interpret a) → D (F x) ≅ fiber q x) →
    Named-Cover (Specification.Decode D interpret) a (λ x → D (F x)) →
    Named-Refinement a q
  summed-refinement a q cover F fibers N =
    let ι = ≅-trans
              (transport-is-isomorphism id
                (ap D
                  (pr₂
                    (Specification.Closure.sum L
                      (Named-Cover.domain N , Named-Cover.names N)))))
              (transport-is-isomorphism id
                (DecodingLaws.sum-β (Univalent-Parent.laws P)
                  (interpret (Named-Cover.domain N))
                  (λ e → interpret (Named-Cover.names N e))))
    in record
      { domain =
          pr₁
            (Specification.Closure.sum L
              (Named-Cover.domain N , Named-Cover.names N))
      ; refining = λ w →
          pr₁
            (forward (fibers (Named-Cover.owner N (pr₁ (forward ι w))))
              (forward (Named-Cover.named N (pr₁ (forward ι w)))
                (pr₂ (forward ι w))))
      ; refines =
          cover-respects-homotopy
            (λ w →
              pr₂
                (forward (fibers (Named-Cover.owner N (pr₁ (forward ι w))))
                  (forward (Named-Cover.named N (pr₁ (forward ι w)))
                    (pr₂ (forward ι w))))
              ⁻¹)
            (composite-of-covers-is-cover (isomorphisms-are-covers ι)
              (composite-of-covers-is-cover
                (first-projections-cover
                  (λ e → D (interpret (Named-Cover.names N e)))
                  (λ e →
                    map-covered
                      (λ p →
                        backward (Named-Cover.named N e)
                          (backward (fibers (Named-Cover.owner N e)) p))
                      (cover (Named-Cover.owner N e))))
                (Named-Cover.covers N)))
      }

  collection-refines-covers : Collects-Names P L → (a : K) {E : Set ℓ}
    (q : E → Specification.Decode D interpret a) → Cover ℓ q →
    (F : Specification.Decode D interpret a → C) →
    ((x : Specification.Decode D interpret a) → D (F x) ≅ fiber q x) →
    ((x : Specification.Decode D interpret a) →
      Covered ℓ
        (Isomorphic-Name (Specification.Decode D interpret) (fiber q x))) →
    Covered ℓ (Named-Refinement a q)
  collection-refines-covers collection a q cover F fibers merely =
    map-covered (summed-refinement a q cover F fibers)
      (collection a F
        (λ x → map-covered
          (λ n → pr₁ n , ≅-trans (pr₂ n) (≅-sym (fibers x)))
          (merely x)))
