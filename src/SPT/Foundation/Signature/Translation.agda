{-# OPTIONS --safe --without-K #-}

module SPT.Foundation.Signature.Translation where

-- Exact translations between dependent signatures with different judgment
-- types. Judgments and operations map covariantly, and the positions of
-- each operation correspond to those of its image by maps inverse to each
-- other, compatibly with the boundaries (`Signature-Translation`):
--
--   f : J Σ → J Ω,   Op Σ j → Op Ω (f j),
--   Pos Σ o ≅ Pos Ω (map o),
--   f (∂ Σ o (project o q)) ＝ ∂ Ω (map o) q.
--
-- The target-to-source projection lets a translated node obtain the exact
-- source child at every target position; boundary coherence supplies only
-- the transport that child needs. Translations have identities and
-- composites, retaining the literal maps, with their components computing
-- pointwise by refl (`identity-signature-translation`,
-- `compose-signature-translation`). Translations store no tree, execution
-- or comparison of meanings, and give no injectivity of judgments or
-- operations and no identification of dependent child functions.

open import SPT.Base
open import SPT.Foundation.Signature using
  (Signature; Judgment; Op; Pos; boundary)

------------------------------------------------------------------------
-- Translations

record Signature-Translation {ℓj₁ ℓo₁ ℓp₁ ℓj₂ ℓo₂ ℓp₂ : Level}
  (source : Signature ℓj₁ ℓo₁ ℓp₁) (target : Signature ℓj₂ ℓo₂ ℓp₂)
  : Set (lsuc (ℓj₁ ⊔ ℓo₁ ⊔ ℓp₁ ⊔ ℓj₂ ⊔ ℓo₂ ⊔ ℓp₂)) where
  field
    map-judgment : Judgment source → Judgment target
    map-operation : {judgment : Judgment source} →
      Op source judgment → Op target (map-judgment judgment)
    map-position : {judgment : Judgment source}
      (operation : Op source judgment) →
      Pos source operation → Pos target (map-operation operation)
    project-position : {judgment : Judgment source}
      (operation : Op source judgment) →
      Pos target (map-operation operation) → Pos source operation
    project-map-position : {judgment : Judgment source}
      (operation : Op source judgment) (position : Pos source operation) →
      project-position operation (map-position operation position)
        ＝ position
    map-project-position : {judgment : Judgment source}
      (operation : Op source judgment)
      (position : Pos target (map-operation operation)) →
      map-position operation (project-position operation position)
        ＝ position
    boundary-coherence : {judgment : Judgment source}
      (operation : Op source judgment)
      (position : Pos target (map-operation operation)) →
      map-judgment
        (boundary source operation (project-position operation position))
        ＝ boundary target (map-operation operation) position

open Signature-Translation public

------------------------------------------------------------------------
-- Identity and composition

-- The identity keeps every judgment, operation and position literally;
-- the composite keeps the two-stage maps, composes the position maps
-- pointwise, and passes boundary coherence through the exact projected
-- middle position.

module _ {ℓj ℓo ℓp : Level} (signature : Signature ℓj ℓo ℓp) where

  identity-signature-translation : Signature-Translation signature signature
  identity-signature-translation = record
    { map-judgment = λ judgment → judgment
    ; map-operation = λ operation → operation
    ; map-position = λ operation position → position
    ; project-position = λ operation position → position
    ; project-map-position = λ operation position → refl
    ; map-project-position = λ operation position → refl
    ; boundary-coherence = λ operation position → refl
    }

module _ {ℓj₁ ℓo₁ ℓp₁ ℓj₂ ℓo₂ ℓp₂ ℓj₃ ℓo₃ ℓp₃ : Level}
  {source : Signature ℓj₁ ℓo₁ ℓp₁} {middle : Signature ℓj₂ ℓo₂ ℓp₂}
  {target : Signature ℓj₃ ℓo₃ ℓp₃} where

  compose-signature-translation : Signature-Translation source middle →
    Signature-Translation middle target →
    Signature-Translation source target
  compose-signature-translation first second = record
    { map-judgment = λ judgment →
        map-judgment second (map-judgment first judgment)
    ; map-operation = λ operation →
        map-operation second (map-operation first operation)
    ; map-position = λ operation position →
        map-position second (map-operation first operation)
          (map-position first operation position)
    ; project-position = λ operation position →
        project-position first operation
          (project-position second (map-operation first operation) position)
    ; project-map-position = λ operation position →
        ap (project-position first operation)
          (project-map-position second (map-operation first operation)
            (map-position first operation position))
          ∙ project-map-position first operation position
    ; map-project-position = λ operation position →
        ap (map-position second (map-operation first operation))
          (map-project-position first operation
            (project-position second (map-operation first operation)
              position))
          ∙ map-project-position second (map-operation first operation)
            position
    ; boundary-coherence = λ operation position →
        ap (map-judgment second)
          (boundary-coherence first operation
            (project-position second (map-operation first operation)
              position))
          ∙ boundary-coherence second (map-operation first operation)
            position
    }

------------------------------------------------------------------------
-- Pointwise computation laws

module _ {ℓj ℓo ℓp : Level} {signature : Signature ℓj ℓo ℓp} where

  identity-signature-translation-map-judgment :
    (judgment : Judgment signature) →
    map-judgment (identity-signature-translation signature) judgment
      ＝ judgment
  identity-signature-translation-map-judgment judgment = refl

  identity-signature-translation-map-operation :
    {judgment : Judgment signature} (operation : Op signature judgment) →
    map-operation (identity-signature-translation signature) operation
      ＝ operation
  identity-signature-translation-map-operation operation = refl

  identity-signature-translation-map-position :
    {judgment : Judgment signature} (operation : Op signature judgment)
    (position : Pos signature operation) →
    map-position (identity-signature-translation signature) operation
      position
      ＝ position
  identity-signature-translation-map-position operation position = refl

  identity-signature-translation-project-position :
    {judgment : Judgment signature} (operation : Op signature judgment)
    (position : Pos signature operation) →
    project-position (identity-signature-translation signature) operation
      position
      ＝ position
  identity-signature-translation-project-position operation position =
    refl

module _ {ℓj₁ ℓo₁ ℓp₁ ℓj₂ ℓo₂ ℓp₂ ℓj₃ ℓo₃ ℓp₃ : Level}
  {source : Signature ℓj₁ ℓo₁ ℓp₁} {middle : Signature ℓj₂ ℓo₂ ℓp₂}
  {target : Signature ℓj₃ ℓo₃ ℓp₃}
  (first : Signature-Translation source middle)
  (second : Signature-Translation middle target) where

  compose-signature-translation-map-judgment :
    (judgment : Judgment source) →
    map-judgment (compose-signature-translation first second) judgment
      ＝ map-judgment second (map-judgment first judgment)
  compose-signature-translation-map-judgment judgment = refl

  compose-signature-translation-map-operation :
    {judgment : Judgment source} (operation : Op source judgment) →
    map-operation (compose-signature-translation first second) operation
      ＝ map-operation second (map-operation first operation)
  compose-signature-translation-map-operation operation = refl

  compose-signature-translation-map-position :
    {judgment : Judgment source} (operation : Op source judgment)
    (position : Pos source operation) →
    map-position (compose-signature-translation first second) operation
      position
      ＝ map-position second (map-operation first operation)
        (map-position first operation position)
  compose-signature-translation-map-position operation position = refl

  compose-signature-translation-project-position :
    {judgment : Judgment source} (operation : Op source judgment)
    (position :
      Pos target (map-operation second (map-operation first operation))) →
    project-position (compose-signature-translation first second)
      operation position
      ＝ project-position first operation
        (project-position second (map-operation first operation) position)
  compose-signature-translation-project-position operation position = refl

  compose-signature-translation-boundary-coherence :
    {judgment : Judgment source} (operation : Op source judgment)
    (position :
      Pos target (map-operation second (map-operation first operation))) →
    boundary-coherence (compose-signature-translation first second)
      operation position
      ＝ ap (map-judgment second)
          (boundary-coherence first operation
            (project-position second (map-operation first operation)
              position))
        ∙ boundary-coherence second (map-operation first operation)
          position
  compose-signature-translation-boundary-coherence operation position =
    refl
