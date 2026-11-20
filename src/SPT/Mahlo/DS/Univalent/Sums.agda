{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.DS.Univalent.Sums where

-- Collection from sums in the completion. Over the ambient parent, under
-- univalence and extensionality (Univalent.Types' `Type-Hypotheses`), let L
-- be a closure of an operator on a small type and Cm a completion of its
-- decoding (Univalent.Completion). The completion names its sums when it
-- names the sum of each of its families (`Completed-Sums`), the sum field
-- of a closure on it. Then L collects names, over the arity itself
-- (`collection-from-completed-sums`). For a family B over a code a whose
-- members are merely named in L, each member is named in the completion
-- (`completion-name`), so the completion names Σ x. B x (`summed`). That
-- name is merely the image of a code σ of L, and the fibers of the first
-- projection are codes of L by its sum and identity formers, one at each
-- point of a, with no choice (`fiber-code`, `fibers`):
--
--   Σ (w : σ). pr₁ w ＝ x   ≅   B x   (`sum-fiber`).
--
-- Conversely, collection gives the closure with unique names on the
-- completion (Univalent.Completion's `completed-closure`), whose sums are
-- named (`sums-from-collection`). So
--
--   Collects-Names L   ⇔   Completed-Sums Cm.

open import SPT.Base
open import SPT.Foundation.Covers using
  (Covered; map-covered; identity-is-cover)
open import SPT.Foundation.Fibers using (fiber)
open import SPT.Foundation.Fibers.Projection using
  (projection-fiber-isomorphism)
open import SPT.Foundation.Isomorphisms using
  (_≅_; backward; ≅-sym; ≅-trans; transport-is-isomorphism)
open import SPT.Foundation.Univalence using (isomorphism-to-equivalence)
import SPT.Mahlo.Ambient as Ambient
open import SPT.Mahlo.DS.Realization.Family using (cast)
import SPT.Mahlo.Specification as Specification
open import SPT.Mahlo.DS.Univalent.Completion using
  ( Completion; Collects-Names; names-in-the-completion
  ; completed-closure )
open import SPT.Mahlo.DS.Univalent.Gluing using (Named-Cover)
open import SPT.Mahlo.DS.Univalent.Names using (Isomorphic-Name)
open import SPT.Mahlo.DS.Univalent.Types using
  (Type-Hypotheses; type-parent; type-identifications)
open import SPT.Mahlo.Heights.Stages using (family)

------------------------------------------------------------------------
-- Fibers of a sum

-- Mathematical shape: T ＝ Σ A B ⊢ Σ (w : T). pr₁ w ＝ a ≅ B a.
sum-fiber : {ℓ : Level} {A : Set ℓ} (B : A → Set ℓ) {T : Set ℓ}
  (e : T ＝ Σ A B) (a : A) → Σ T (λ w → pr₁ (cast e w) ＝ a) ≅ B a
sum-fiber B refl a = ≅-sym (projection-fiber-isomorphism B a)

------------------------------------------------------------------------
-- Sums in a completion

module _ {ℓ : Level} {K : Set ℓ} {S : K → Set ℓ} (Cm : Completion S) where

  -- The completion names the sum of each of its families.
  Completed-Sums : Set (lsuc ℓ)
  Completed-Sums =
    (F :
      Specification.Family
        (Specification.Decode (λ (A : Set ℓ) → A) (Completion.decode Cm)))
    → Specification.Name (Completion.decode Cm)
        (Specification.Formers.sum (Ambient.formers ℓ)
          (Specification.map (λ (A : Set ℓ) → A) (Completion.decode Cm) F))

------------------------------------------------------------------------
-- Collection from sums in the completion, and back

module _ {ℓ : Level} (H : Type-Hypotheses ℓ) {Ψ : Ambient.Operator ℓ}
  {K : Set ℓ} (L : Specification.Closure (Ambient.formers ℓ) Ψ K)
  where

  open Specification.Closure L using (interpret; sum; identity)

  module _ (Cm : Completion interpret) where

    -- A type covered by names of L up to isomorphism is named in the
    -- completion.
    completion-name : (B : Set ℓ) →
      Covered ℓ
        (Isomorphic-Name
          (Specification.Decode (λ (A : Set ℓ) → A) interpret) B) →
      Specification.Name (Completion.decode Cm) B
    completion-name B named =
      names-in-the-completion (type-parent H) Cm B
        (map-covered
          (λ n →
            pr₁ n ,
            backward
              (type-identifications (Type-Hypotheses.univalence H)
                (interpret (pr₁ n)) B)
              (isomorphism-to-equivalence (pr₂ n)))
          named)

    module _ (a : K) (B : interpret a → Set ℓ)
      (merely : (x : interpret a) →
        Covered ℓ
          (Isomorphic-Name
            (Specification.Decode (λ (A : Set ℓ) → A) interpret) (B x)))
      where

      -- The family of the completion over the image of a that names each
      -- member.
      completed-family :
        Specification.Family
          (Specification.Decode (λ (A : Set ℓ) → A) (Completion.decode Cm))
      completed-family =
        Completion.include Cm a ,
        (λ y →
          pr₁
            (completion-name (B (cast (Completion.include-decodes Cm a) y))
              (merely (cast (Completion.include-decodes Cm a) y))))

      -- It decodes to the family B.
      completed-family-β :
        Specification.map (λ (A : Set ℓ) → A) (Completion.decode Cm)
          completed-family
          ＝ (interpret a , B)
      completed-family-β =
        family (Type-Hypotheses.families H) (Completion.include-decodes Cm a)
          (λ y →
            pr₂
              (completion-name (B (cast (Completion.include-decodes Cm a) y))
                (merely (cast (Completion.include-decodes Cm a) y))))

      module _ (sums : Completed-Sums Cm) where

        -- The completion's name of Σ x. B x.
        summed :
          Specification.Name (Completion.decode Cm) (Σ (interpret a) B)
        summed =
          pr₁ (sums completed-family) ,
          (pr₂ (sums completed-family)
            ∙ ap (Specification.Formers.sum (Ambient.formers ℓ))
                completed-family-β)

        module _ (w : fiber (Completion.include Cm) (pr₁ summed)) where

          -- The code of L under the name of the sum decodes to the sum.
          summed-β : interpret (pr₁ w) ＝ Σ (interpret a) B
          summed-β =
            Completion.include-decodes Cm (pr₁ w) ⁻¹
            ∙ (ap (Completion.decode Cm) (pr₂ w) ∙ pr₂ summed)

          -- The fiber of the first projection over x, a code of L.
          fiber-code : interpret a → K
          fiber-code x =
            pr₁
              (sum
                (pr₁ w ,
                  (λ v → pr₁ (identity a (pr₁ (cast summed-β v)) x))))

          fiber-code-β : (x : interpret a) →
            interpret (fiber-code x)
              ＝ Σ (interpret (pr₁ w)) (λ v → pr₁ (cast summed-β v) ＝ x)
          fiber-code-β x =
            pr₂
              (sum
                (pr₁ w ,
                  (λ v → pr₁ (identity a (pr₁ (cast summed-β v)) x))))
            ∙ ap (Σ (interpret (pr₁ w)))
                (Type-Hypotheses.families H (interpret (pr₁ w))
                  (λ v →
                    interpret (pr₁ (identity a (pr₁ (cast summed-β v)) x)))
                  (λ v → pr₁ (cast summed-β v) ＝ x)
                  (λ v → pr₂ (identity a (pr₁ (cast summed-β v)) x)))

          -- Every member is named in L, over the arity itself.
          fibers :
            Named-Cover (Specification.Decode (λ (A : Set ℓ) → A) interpret)
              a B
          fibers = record
            { domain = a
            ; owner = id
            ; names = fiber-code
            ; named = λ x →
                ≅-trans (transport-is-isomorphism id (fiber-code-β x))
                  (sum-fiber B summed-β x)
            ; covers = identity-is-cover
            }

    -- Sums in the completion give collection, over the arity itself.
    collection-from-completed-sums :
      Completed-Sums Cm → Collects-Names (type-parent H) L
    collection-from-completed-sums sums a B merely =
      map-covered (fibers a B merely sums)
        (Completion.include-covers Cm (pr₁ (summed a B merely sums)))

    -- Collection gives the closure on the completion, which names sums.
    sums-from-collection :
      Collects-Names (type-parent H) L → Completed-Sums Cm
    sums-from-collection collection =
      Specification.Closure.sum
        (completed-closure (type-parent H) L collection Cm)
