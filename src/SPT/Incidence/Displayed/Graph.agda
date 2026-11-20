{-# OPTIONS --safe --without-K #-}

module SPT.Incidence.Displayed.Graph where

-- The graph of a map `output : I → D`, decorated by a family `C` over `D`,
-- against the pullback of `C` along `output`:
--
--   Graph-Occurrence C output = Σ (d : D). Σ (i : I). (output i ＝ d) × C d,
--   Total (pullback-space C output) = Σ (i : I). C (output i).
--
-- An occurrence keeps its output, its index, their identification and its
-- cell. Path induction recovers the complete occurrence from its index and
-- cell (`recover-occurrence`), so occurrences and the pullback total are
-- isomorphic (`graph-occurrence-isomorphism`). A map out of occurrences
-- factors through the pullback by `observe-through` of
-- SPT.Foundation.Isomorphisms.Conjugation at this isomorphism.
--
-- A family Q over occurrences moves to the pullback: its dependent pairs
-- exactly (`graph-family-total-isomorphism`), its sections pointwise in both
-- directions (`descend-sections`, `ascend-sections`), and as an isomorphism
-- of the two section types under extensionality for both, passed explicitly
-- (`graph-family-sections-isomorphism`).

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.Isomorphisms using
  (_≅_; forward; backward; backward-forward; forward-backward)
open import SPT.Foundation.Spaces using (DΣ; Base; Fiber; Total)

------------------------------------------------------------------------
-- Occurrences of the graph and the pullback

module _ {ℓi ℓc ℓd : Level} {I : Set ℓi} {D : Set ℓd} (C : D → Set ℓc)
  (output : I → D) where

  Graph-Fiber : D → Set (ℓi ⊔ ℓc ⊔ ℓd)
  Graph-Fiber d = Σ I (λ i → (output i ＝ d) × C d)

  Graph-Occurrence : Set (ℓi ⊔ ℓc ⊔ ℓd)
  Graph-Occurrence = Σ D Graph-Fiber

  pullback-space : DΣ ℓi ℓc
  pullback-space = record
    { Base = I
    ; Fiber = λ i → C (output i)
    }

  occurrence-index : Graph-Occurrence → I
  occurrence-index (d , i , p , c) = i

  occurrence-cell : (p : Graph-Occurrence) → C (output (occurrence-index p))
  occurrence-cell (d , i , p , c) = transport C (p ⁻¹) c

  restore-occurrence : (i : I) → C (output i) → Graph-Occurrence
  restore-occurrence i c = output i , i , refl , c

  recover-occurrence : (p : Graph-Occurrence) →
    restore-occurrence (occurrence-index p) (occurrence-cell p) ＝ p
  recover-occurrence (d , i , refl , c) = refl

  retain-occurrence : Graph-Occurrence → Total pullback-space
  retain-occurrence p = occurrence-index p , occurrence-cell p

  return-occurrence : Total pullback-space → Graph-Occurrence
  return-occurrence (i , c) = restore-occurrence i c

  retain-return-occurrence : (x : Total pullback-space) →
    retain-occurrence (return-occurrence x) ＝ x
  retain-return-occurrence (i , c) = refl

  -- The index, the complete output, their identification and the cell move
  -- together by path induction; neither inverse discards any of them.

  graph-occurrence-isomorphism : Graph-Occurrence ≅ Total pullback-space
  graph-occurrence-isomorphism = record
    { forward = retain-occurrence
    ; backward = return-occurrence
    ; backward-forward = recover-occurrence
    ; forward-backward = retain-return-occurrence
    }

------------------------------------------------------------------------
-- Families over occurrences

  -- Dependent pairs move exactly. Sections move pointwise in both
  -- directions; the two inverse laws are pointwise, and become
  -- identifications of sections only under the two extensionality
  -- hypotheses of `graph-family-sections-isomorphism`.

  module _ {ν : Level} (Q : Graph-Occurrence → Set ν) where

    Pullback-Family-Total : Set (ℓi ⊔ ℓc ⊔ ν)
    Pullback-Family-Total =
      Σ (Total pullback-space) (λ x → Q (return-occurrence x))

    retain-family-point : Σ Graph-Occurrence Q → Pullback-Family-Total
    retain-family-point (p , q) =
      retain-occurrence p , transport Q (recover-occurrence p ⁻¹) q

    return-family-point : Pullback-Family-Total → Σ Graph-Occurrence Q
    return-family-point (x , q) = return-occurrence x , q

    return-retain-family-point : (w : Σ Graph-Occurrence Q) →
      return-family-point (retain-family-point w) ＝ w
    return-retain-family-point ((d , i , refl , c) , q) = refl

    retain-return-family-point : (w : Pullback-Family-Total) →
      retain-family-point (return-family-point w) ＝ w
    retain-return-family-point ((i , c) , q) = refl

    graph-family-total-isomorphism :
      Σ Graph-Occurrence Q ≅ Pullback-Family-Total
    graph-family-total-isomorphism = record
      { forward = retain-family-point
      ; backward = return-family-point
      ; backward-forward = return-retain-family-point
      ; forward-backward = retain-return-family-point
      }

    Occurrence-Sections : Set (ℓi ⊔ ℓc ⊔ ℓd ⊔ ν)
    Occurrence-Sections = (p : Graph-Occurrence) → Q p

    Pullback-Sections : Set (ℓi ⊔ ℓc ⊔ ν)
    Pullback-Sections = (x : Total pullback-space) → Q (return-occurrence x)

    descend-sections : Occurrence-Sections → Pullback-Sections
    descend-sections f x = f (return-occurrence x)

    ascend-sections : Pullback-Sections → Occurrence-Sections
    ascend-sections f p =
      transport Q (recover-occurrence p) (f (retain-occurrence p))

    ascend-descend-sections : (f : Occurrence-Sections)
      (p : Graph-Occurrence) → ascend-sections (descend-sections f) p ＝ f p
    ascend-descend-sections f (d , i , refl , c) = refl

    descend-ascend-sections : (f : Pullback-Sections)
      (x : Total pullback-space) →
      descend-sections (ascend-sections f) x ＝ f x
    descend-ascend-sections f (i , c) = refl

    graph-family-sections-isomorphism :
      FunExt Graph-Occurrence Q →
      FunExt (Total pullback-space) (λ x → Q (return-occurrence x)) →
      Occurrence-Sections ≅ Pullback-Sections
    graph-family-sections-isomorphism upper lower = record
      { forward = descend-sections
      ; backward = ascend-sections
      ; backward-forward = λ f →
          upper (ascend-sections (descend-sections f)) f
            (ascend-descend-sections f)
      ; forward-backward = λ f →
          lower (descend-sections (ascend-sections f)) f
            (descend-ascend-sections f)
      }
