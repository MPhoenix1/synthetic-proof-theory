{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.Signature.LaxTranslation where

-- Lax translations between dependent signatures over different judgment
-- types. Writing f for the judgment map, a lax translation maps operations
-- covariantly and keeps, for every target position, only the source
-- position it is built from (`Lax-Signature-Translation`):
--
--   map-lax-operation : Op_S(i) → Op_T(f i),
--   project-lax-position : Pos_T(map o) → Pos_S(o),
--   lax-boundary-coherence : f (∂_S(o , project q)) ＝ ∂_T(map o , q).
--
-- Source positions may disappear: no forward position map or inverse law
-- is required, unlike an exact translation
-- (SPT.Cubical.Foundation.Signature.Translation), which forgets to a lax one
-- (`exact-signature-translation-to-lax`).
--
-- * Operation cells compare two operations over one judgment type, every
--   right position keeping its left antecedent (`Lax-Operation-Cell`).
--   Pointwise cells compare two lax translations with one source and one
--   judgment map, and judgment cells two translations along a supplied
--   pointwise path between their judgment maps; each keeps an operation
--   cell at every source operation, the agreement of the two projected
--   source positions, and the square of the boundary coherences
--   (`Lax-Signature-Translation-Pointwise-Cell`,
--   `Lax-Signature-Translation-Judgment-Cell`). Both are reflexive and
--   compose (`…-refl`, `compose-lax-operation-cell`,
--   `compose-lax-signature-translation-pointwise-cell`,
--   `compose-lax-signature-translation-judgment-cell`), the boundary
--   squares pasted by `paste-lax-boundary-squares` and
--   `paste-lax-judgment-boundary-squares`.
-- * Lax translations have an identity and compose
--   (`identity-lax-signature-translation`,
--   `compose-lax-signature-translation`), with computation laws by refl.
--
-- No equality of translations, operation maps, position functions or
-- coherence proofs, source-position coverage or tree action is supplied.

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Signature.Sum using
  (Signature-Over; Operation; Position; position-boundary; to-signature)
open import SPT.Cubical.Foundation.Signature.Translation using
  ( Signature-Translation; map-judgment; map-operation; project-position
  ; boundary-coherence )

------------------------------------------------------------------------
-- Lax signature translations

record Lax-Signature-Translation {ℓj₁ ℓo₁ ℓp₁ ℓj₂ ℓo₂ ℓp₂ : Level}
  {Source-Judgment : Set ℓj₁} {Target-Judgment : Set ℓj₂}
  (on-judgment : Source-Judgment → Target-Judgment)
  (source : Signature-Over Source-Judgment ℓo₁ ℓp₁)
  (target : Signature-Over Target-Judgment ℓo₂ ℓp₂)
  : Set (lsuc (ℓj₁ ⊔ ℓo₁ ⊔ ℓp₁ ⊔ ℓj₂ ⊔ ℓo₂ ⊔ ℓp₂)) where
  field
    map-lax-operation : {source-judgment : Source-Judgment} →
      Operation source source-judgment →
      Operation target (on-judgment source-judgment)
    project-lax-position : {source-judgment : Source-Judgment}
      (source-operation : Operation source source-judgment) →
      Position target (map-lax-operation source-operation) →
      Position source source-operation
    lax-boundary-coherence : {source-judgment : Source-Judgment}
      (source-operation : Operation source source-judgment)
      (target-position :
        Position target (map-lax-operation source-operation)) →
      on-judgment
        (position-boundary source source-operation
          (project-lax-position source-operation target-position))
        ＝ position-boundary target (map-lax-operation source-operation)
          target-position

open Lax-Signature-Translation public

------------------------------------------------------------------------
-- Cells between operations and between translations

-- Every right position keeps the exact left antecedent against which it
-- is compared; left positions may disappear. The output judgments are
-- related by a retained path, not identified definitionally.

record Lax-Operation-Cell {ℓj ℓo₁ ℓp₁ ℓo₂ ℓp₂ : Level} {J : Set ℓj}
  (left : Signature-Over J ℓo₁ ℓp₁) (right : Signature-Over J ℓo₂ ℓp₂)
  {left-judgment right-judgment : J}
  (left-operation : Operation left left-judgment)
  (right-operation : Operation right right-judgment)
  : Set (lsuc (ℓj ⊔ ℓo₁ ⊔ ℓp₁ ⊔ ℓo₂ ⊔ ℓp₂)) where
  field
    operation-result-cell : left-judgment ＝ right-judgment
    project-right-operation-position :
      Position right right-operation → Position left left-operation
    operation-boundary-coherence :
      (right-position : Position right right-operation) →
      position-boundary left left-operation
        (project-right-operation-position right-position)
        ＝ position-boundary right right-operation right-position

open Lax-Operation-Cell public

-- Two translations with one source and one judgment map: at every source
-- operation a local operation cell relates their images, both routes keep
-- the same literal source antecedent, and the boundary paths agree.

record Lax-Signature-Translation-Pointwise-Cell
  {ℓj₁ ℓo₁ ℓp₁ ℓj₂ ℓo₂L ℓp₂L ℓo₂R ℓp₂R : Level}
  {Source-Judgment : Set ℓj₁} {Target-Judgment : Set ℓj₂}
  {on-judgment : Source-Judgment → Target-Judgment}
  {source : Signature-Over Source-Judgment ℓo₁ ℓp₁}
  {left-target : Signature-Over Target-Judgment ℓo₂L ℓp₂L}
  {right-target : Signature-Over Target-Judgment ℓo₂R ℓp₂R}
  (left : Lax-Signature-Translation on-judgment source left-target)
  (right : Lax-Signature-Translation on-judgment source right-target)
  : Set (lsuc (ℓj₁ ⊔ ℓo₁ ⊔ ℓp₁ ⊔ ℓj₂ ⊔ ℓo₂L ⊔ ℓp₂L ⊔ ℓo₂R ⊔ ℓp₂R)) where
  field
    mapped-operation-cell : {source-judgment : Source-Judgment}
      (source-operation : Operation source source-judgment) →
      Lax-Operation-Cell left-target right-target
        (map-lax-operation left source-operation)
        (map-lax-operation right source-operation)
    projected-source-position-cell : {source-judgment : Source-Judgment}
      (source-operation : Operation source source-judgment)
      (right-position :
        Position right-target (map-lax-operation right source-operation)) →
      project-lax-position left source-operation
        (project-right-operation-position
          (mapped-operation-cell source-operation) right-position)
        ＝ project-lax-position right source-operation right-position
    mapped-operation-boundary-square : {source-judgment : Source-Judgment}
      (source-operation : Operation source source-judgment)
      (right-position :
        Position right-target (map-lax-operation right source-operation)) →
      lax-boundary-coherence left source-operation
        (project-right-operation-position
          (mapped-operation-cell source-operation) right-position)
        ∙ operation-boundary-coherence
          (mapped-operation-cell source-operation) right-position
        ＝ ap
          (λ source-position →
            on-judgment
              (position-boundary source source-operation source-position))
          (projected-source-position-cell source-operation right-position)
          ∙ lax-boundary-coherence right source-operation right-position

open Lax-Signature-Translation-Pointwise-Cell public

-- Across a supplied pointwise path between two judgment maps: the result
-- path of every mapped operation cell is that path at the source result,
-- and the boundary square includes it at the projected source child.

record Lax-Signature-Translation-Judgment-Cell
  {ℓj₁ ℓo₁ ℓp₁ ℓj₂ ℓo₂L ℓp₂L ℓo₂R ℓp₂R : Level}
  {Source-Judgment : Set ℓj₁} {Target-Judgment : Set ℓj₂}
  {left-judgment-map right-judgment-map :
    Source-Judgment → Target-Judgment}
  (judgment-cell : (source-judgment : Source-Judgment) →
    left-judgment-map source-judgment ＝ right-judgment-map source-judgment)
  {source : Signature-Over Source-Judgment ℓo₁ ℓp₁}
  {left-target : Signature-Over Target-Judgment ℓo₂L ℓp₂L}
  {right-target : Signature-Over Target-Judgment ℓo₂R ℓp₂R}
  (left : Lax-Signature-Translation left-judgment-map source left-target)
  (right : Lax-Signature-Translation right-judgment-map source right-target)
  : Set (lsuc (ℓj₁ ⊔ ℓo₁ ⊔ ℓp₁ ⊔ ℓj₂ ⊔ ℓo₂L ⊔ ℓp₂L ⊔ ℓo₂R ⊔ ℓp₂R)) where
  field
    judgment-mapped-operation-cell : {source-judgment : Source-Judgment}
      (source-operation : Operation source source-judgment) →
      Lax-Operation-Cell left-target right-target
        (map-lax-operation left source-operation)
        (map-lax-operation right source-operation)
    judgment-mapped-operation-result-cell :
      {source-judgment : Source-Judgment}
      (source-operation : Operation source source-judgment) →
      operation-result-cell (judgment-mapped-operation-cell source-operation)
        ＝ judgment-cell source-judgment
    judgment-mapped-source-position-cell :
      {source-judgment : Source-Judgment}
      (source-operation : Operation source source-judgment)
      (right-position :
        Position right-target (map-lax-operation right source-operation)) →
      project-lax-position left source-operation
        (project-right-operation-position
          (judgment-mapped-operation-cell source-operation) right-position)
        ＝ project-lax-position right source-operation right-position
    judgment-mapped-boundary-square : {source-judgment : Source-Judgment}
      (source-operation : Operation source source-judgment)
      (right-position :
        Position right-target (map-lax-operation right source-operation)) →
      lax-boundary-coherence left source-operation
        (project-right-operation-position
          (judgment-mapped-operation-cell source-operation) right-position)
        ∙ operation-boundary-coherence
          (judgment-mapped-operation-cell source-operation) right-position
        ＝ ap
          (λ source-position →
            left-judgment-map
              (position-boundary source source-operation source-position))
          (judgment-mapped-source-position-cell source-operation
            right-position)
          ∙ (judgment-cell
              (position-boundary source source-operation
                (project-lax-position right source-operation right-position))
            ∙ lax-boundary-coherence right source-operation right-position)

open Lax-Signature-Translation-Judgment-Cell public

------------------------------------------------------------------------
-- Reflexive cells

module _ {ℓj₁ ℓo₁ ℓp₁ ℓj₂ ℓo₂ ℓp₂ : Level} {Source-Judgment : Set ℓj₁}
  {Target-Judgment : Set ℓj₂}
  {on-judgment : Source-Judgment → Target-Judgment}
  {source : Signature-Over Source-Judgment ℓo₁ ℓp₁}
  {target : Signature-Over Target-Judgment ℓo₂ ℓp₂}
  (translation : Lax-Signature-Translation on-judgment source target)
  where

  lax-signature-translation-judgment-cell-refl :
    Lax-Signature-Translation-Judgment-Cell
      (λ source-judgment → refl) translation translation
  lax-signature-translation-judgment-cell-refl = record
    { judgment-mapped-operation-cell = λ source-operation → record
        { operation-result-cell = refl
        ; project-right-operation-position = λ right-position →
            right-position
        ; operation-boundary-coherence = λ right-position → refl
        }
    ; judgment-mapped-operation-result-cell = λ source-operation → refl
    ; judgment-mapped-source-position-cell =
        λ source-operation right-position → refl
    ; judgment-mapped-boundary-square = λ source-operation right-position →
        refl-right-neutral
          (lax-boundary-coherence translation source-operation
            right-position)
    }

  lax-signature-translation-pointwise-cell-refl :
    Lax-Signature-Translation-Pointwise-Cell translation translation
  lax-signature-translation-pointwise-cell-refl = record
    { mapped-operation-cell = λ source-operation → record
        { operation-result-cell = refl
        ; project-right-operation-position = λ right-position →
            right-position
        ; operation-boundary-coherence = λ right-position → refl
        }
    ; projected-source-position-cell = λ source-operation right-position →
        refl
    ; mapped-operation-boundary-square = λ source-operation right-position →
        refl-right-neutral
          (lax-boundary-coherence translation source-operation
            right-position)
    }

module _ {ℓj₁ ℓo₁ ℓp₁ ℓj₂ ℓo₂L ℓp₂L ℓo₂R ℓp₂R : Level}
  {Source-Judgment : Set ℓj₁} {Target-Judgment : Set ℓj₂}
  {on-judgment : Source-Judgment → Target-Judgment}
  {source : Signature-Over Source-Judgment ℓo₁ ℓp₁}
  {left-target : Signature-Over Target-Judgment ℓo₂L ℓp₂L}
  {right-target : Signature-Over Target-Judgment ℓo₂R ℓp₂R}
  {left : Lax-Signature-Translation on-judgment source left-target}
  {right : Lax-Signature-Translation on-judgment source right-target}
  where

  -- A judgment cell along the reflexive path is a pointwise cell.

  lax-signature-translation-judgment-cell-at-refl :
    Lax-Signature-Translation-Judgment-Cell (λ source-judgment → refl) left
      right →
    Lax-Signature-Translation-Pointwise-Cell left right
  lax-signature-translation-judgment-cell-at-refl cell = record
    { mapped-operation-cell = judgment-mapped-operation-cell cell
    ; projected-source-position-cell =
        judgment-mapped-source-position-cell cell
    ; mapped-operation-boundary-square =
        judgment-mapped-boundary-square cell
    }

------------------------------------------------------------------------
-- Pasting boundary squares

-- Two boundary squares along consecutive source paths paste into one
-- along their composite; the second form inserts the pointwise judgment
-- paths at the projected source child.

module _ {ℓs ℓt : Level} {Source : Set ℓs} {Target : Set ℓt}
  (on-source : Source → Target) where

  paste-lax-boundary-squares :
    {source-left source-middle source-right : Source}
    {target-left target-middle target-right : Target}
    (source-left-middle : source-left ＝ source-middle)
    (source-middle-right : source-middle ＝ source-right)
    (left-boundary : on-source source-left ＝ target-left)
    (left-middle-boundary : target-left ＝ target-middle)
    (middle-boundary : on-source source-middle ＝ target-middle)
    (middle-right-boundary : target-middle ＝ target-right)
    (right-boundary : on-source source-right ＝ target-right) →
    left-boundary ∙ left-middle-boundary
      ＝ ap on-source source-left-middle ∙ middle-boundary →
    middle-boundary ∙ middle-right-boundary
      ＝ ap on-source source-middle-right ∙ right-boundary →
    left-boundary ∙ (left-middle-boundary ∙ middle-right-boundary)
      ＝ ap on-source (source-left-middle ∙ source-middle-right)
        ∙ right-boundary
  paste-lax-boundary-squares source-left-middle source-middle-right
    left-boundary left-middle-boundary middle-boundary middle-right-boundary
    right-boundary left-square right-square =
    ∙assoc left-boundary left-middle-boundary middle-right-boundary ⁻¹
      ∙ ap (λ path → path ∙ middle-right-boundary) left-square
      ∙ ∙assoc (ap on-source source-left-middle) middle-boundary
        middle-right-boundary
      ∙ ap (λ path → ap on-source source-left-middle ∙ path) right-square
      ∙ ∙assoc (ap on-source source-left-middle)
        (ap on-source source-middle-right) right-boundary ⁻¹
      ∙ ap (λ path → path ∙ right-boundary)
        (ap-∙ on-source source-left-middle source-middle-right ⁻¹)

module _ {ℓs ℓt : Level} {Source : Set ℓs} {Target : Set ℓt}
  (left-map middle-map right-map : Source → Target)
  (left-middle-cell : (source : Source) →
    left-map source ＝ middle-map source)
  (middle-right-cell : (source : Source) →
    middle-map source ＝ right-map source) where

  paste-lax-judgment-boundary-squares :
    {source-left source-middle source-right : Source}
    {target-left target-middle target-right : Target}
    (source-left-middle : source-left ＝ source-middle)
    (source-middle-right : source-middle ＝ source-right)
    (left-boundary : left-map source-left ＝ target-left)
    (left-middle-boundary : target-left ＝ target-middle)
    (middle-boundary : middle-map source-middle ＝ target-middle)
    (middle-right-boundary : target-middle ＝ target-right)
    (right-boundary : right-map source-right ＝ target-right) →
    left-boundary ∙ left-middle-boundary
      ＝ ap left-map source-left-middle
        ∙ (left-middle-cell source-middle ∙ middle-boundary) →
    middle-boundary ∙ middle-right-boundary
      ＝ ap middle-map source-middle-right
        ∙ (middle-right-cell source-right ∙ right-boundary) →
    left-boundary ∙ (left-middle-boundary ∙ middle-right-boundary)
      ＝ ap left-map (source-left-middle ∙ source-middle-right)
        ∙ ((left-middle-cell source-right ∙ middle-right-cell source-right)
          ∙ right-boundary)
  paste-lax-judgment-boundary-squares {source-left} refl refl left-boundary
    left-middle-boundary middle-boundary middle-right-boundary right-boundary
    left-square right-square =
    ∙assoc left-boundary left-middle-boundary middle-right-boundary ⁻¹
      ∙ ap (λ path → path ∙ middle-right-boundary) left-square
      ∙ ∙assoc (left-middle-cell source-left) middle-boundary
        middle-right-boundary
      ∙ ap (λ path → left-middle-cell source-left ∙ path) right-square
      ∙ ∙assoc (left-middle-cell source-left) (middle-right-cell source-left)
        right-boundary ⁻¹

------------------------------------------------------------------------
-- Composite cells

module _ {ℓj ℓo₁ ℓp₁ ℓo₂ ℓp₂ ℓo₃ ℓp₃ : Level} {J : Set ℓj}
  {left-signature : Signature-Over J ℓo₁ ℓp₁}
  {middle-signature : Signature-Over J ℓo₂ ℓp₂}
  {right-signature : Signature-Over J ℓo₃ ℓp₃}
  {left-judgment middle-judgment right-judgment : J}
  {left-operation : Operation left-signature left-judgment}
  {middle-operation : Operation middle-signature middle-judgment}
  {right-operation : Operation right-signature right-judgment} where

  compose-lax-operation-cell :
    Lax-Operation-Cell left-signature middle-signature left-operation
      middle-operation →
    Lax-Operation-Cell middle-signature right-signature middle-operation
      right-operation →
    Lax-Operation-Cell left-signature right-signature left-operation
      right-operation
  compose-lax-operation-cell left-cell right-cell = record
    { operation-result-cell =
        operation-result-cell left-cell ∙ operation-result-cell right-cell
    ; project-right-operation-position = λ right-position →
        project-right-operation-position left-cell
          (project-right-operation-position right-cell right-position)
    ; operation-boundary-coherence = λ right-position →
        operation-boundary-coherence left-cell
          (project-right-operation-position right-cell right-position)
          ∙ operation-boundary-coherence right-cell right-position
    }

module _ {ℓj₁ ℓo₁ ℓp₁ ℓj₂ ℓo₂L ℓp₂L ℓo₂M ℓp₂M ℓo₂R ℓp₂R : Level}
  {Source-Judgment : Set ℓj₁} {Target-Judgment : Set ℓj₂}
  {on-judgment : Source-Judgment → Target-Judgment}
  {source : Signature-Over Source-Judgment ℓo₁ ℓp₁}
  {left-target : Signature-Over Target-Judgment ℓo₂L ℓp₂L}
  {middle-target : Signature-Over Target-Judgment ℓo₂M ℓp₂M}
  {right-target : Signature-Over Target-Judgment ℓo₂R ℓp₂R}
  {left : Lax-Signature-Translation on-judgment source left-target}
  {middle : Lax-Signature-Translation on-judgment source middle-target}
  {right : Lax-Signature-Translation on-judgment source right-target}
  where

  compose-lax-signature-translation-pointwise-cell :
    Lax-Signature-Translation-Pointwise-Cell left middle →
    Lax-Signature-Translation-Pointwise-Cell middle right →
    Lax-Signature-Translation-Pointwise-Cell left right
  compose-lax-signature-translation-pointwise-cell left-cell right-cell =
    record
    { mapped-operation-cell = λ source-operation →
        compose-lax-operation-cell
          (mapped-operation-cell left-cell source-operation)
          (mapped-operation-cell right-cell source-operation)
    ; projected-source-position-cell = λ source-operation right-position →
        projected-source-position-cell left-cell source-operation
          (project-right-operation-position
            (mapped-operation-cell right-cell source-operation)
            right-position)
          ∙ projected-source-position-cell right-cell source-operation
            right-position
    ; mapped-operation-boundary-square = λ source-operation right-position →
        paste-lax-boundary-squares
          (λ source-position →
            on-judgment
              (position-boundary source source-operation source-position))
          (projected-source-position-cell left-cell source-operation
            (project-right-operation-position
              (mapped-operation-cell right-cell source-operation)
              right-position))
          (projected-source-position-cell right-cell source-operation
            right-position)
          (lax-boundary-coherence left source-operation
            (project-right-operation-position
              (mapped-operation-cell left-cell source-operation)
              (project-right-operation-position
                (mapped-operation-cell right-cell source-operation)
                right-position)))
          (operation-boundary-coherence
            (mapped-operation-cell left-cell source-operation)
            (project-right-operation-position
              (mapped-operation-cell right-cell source-operation)
              right-position))
          (lax-boundary-coherence middle source-operation
            (project-right-operation-position
              (mapped-operation-cell right-cell source-operation)
              right-position))
          (operation-boundary-coherence
            (mapped-operation-cell right-cell source-operation)
            right-position)
          (lax-boundary-coherence right source-operation right-position)
          (mapped-operation-boundary-square left-cell source-operation
            (project-right-operation-position
              (mapped-operation-cell right-cell source-operation)
              right-position))
          (mapped-operation-boundary-square right-cell source-operation
            right-position)
    }

module _ {ℓj₁ ℓo₁ ℓp₁ ℓj₂ ℓo₂L ℓp₂L ℓo₂M ℓp₂M ℓo₂R ℓp₂R : Level}
  {Source-Judgment : Set ℓj₁} {Target-Judgment : Set ℓj₂}
  {left-judgment-map middle-judgment-map right-judgment-map :
    Source-Judgment → Target-Judgment}
  {left-middle-judgment-cell : (source-judgment : Source-Judgment) →
    left-judgment-map source-judgment ＝ middle-judgment-map source-judgment}
  {middle-right-judgment-cell : (source-judgment : Source-Judgment) →
    middle-judgment-map source-judgment
      ＝ right-judgment-map source-judgment}
  {source : Signature-Over Source-Judgment ℓo₁ ℓp₁}
  {left-target : Signature-Over Target-Judgment ℓo₂L ℓp₂L}
  {middle-target : Signature-Over Target-Judgment ℓo₂M ℓp₂M}
  {right-target : Signature-Over Target-Judgment ℓo₂R ℓp₂R}
  {left : Lax-Signature-Translation left-judgment-map source left-target}
  {middle :
    Lax-Signature-Translation middle-judgment-map source middle-target}
  {right : Lax-Signature-Translation right-judgment-map source right-target}
  where

  compose-lax-signature-translation-judgment-cell :
    Lax-Signature-Translation-Judgment-Cell left-middle-judgment-cell left
      middle →
    Lax-Signature-Translation-Judgment-Cell middle-right-judgment-cell middle
      right →
    Lax-Signature-Translation-Judgment-Cell
      (λ source-judgment →
        left-middle-judgment-cell source-judgment
          ∙ middle-right-judgment-cell source-judgment)
      left right
  compose-lax-signature-translation-judgment-cell left-cell right-cell =
    record
    { judgment-mapped-operation-cell = λ source-operation →
        compose-lax-operation-cell
          (judgment-mapped-operation-cell left-cell source-operation)
          (judgment-mapped-operation-cell right-cell source-operation)
    ; judgment-mapped-operation-result-cell =
        λ {source-judgment} source-operation →
          ap
            (λ result-cell →
              result-cell
                ∙ operation-result-cell
                  (judgment-mapped-operation-cell right-cell
                    source-operation))
            (judgment-mapped-operation-result-cell left-cell
              source-operation)
            ∙ ap
              (λ result-cell →
                left-middle-judgment-cell source-judgment ∙ result-cell)
              (judgment-mapped-operation-result-cell right-cell
                source-operation)
    ; judgment-mapped-source-position-cell =
        λ source-operation right-position →
          judgment-mapped-source-position-cell left-cell source-operation
            (project-right-operation-position
              (judgment-mapped-operation-cell right-cell source-operation)
              right-position)
            ∙ judgment-mapped-source-position-cell right-cell
              source-operation right-position
    ; judgment-mapped-boundary-square = λ source-operation right-position →
        paste-lax-judgment-boundary-squares
          (λ source-position →
            left-judgment-map
              (position-boundary source source-operation source-position))
          (λ source-position →
            middle-judgment-map
              (position-boundary source source-operation source-position))
          (λ source-position →
            right-judgment-map
              (position-boundary source source-operation source-position))
          (λ source-position →
            left-middle-judgment-cell
              (position-boundary source source-operation source-position))
          (λ source-position →
            middle-right-judgment-cell
              (position-boundary source source-operation source-position))
          (judgment-mapped-source-position-cell left-cell source-operation
            (project-right-operation-position
              (judgment-mapped-operation-cell right-cell source-operation)
              right-position))
          (judgment-mapped-source-position-cell right-cell source-operation
            right-position)
          (lax-boundary-coherence left source-operation
            (project-right-operation-position
              (judgment-mapped-operation-cell left-cell source-operation)
              (project-right-operation-position
                (judgment-mapped-operation-cell right-cell source-operation)
                right-position)))
          (operation-boundary-coherence
            (judgment-mapped-operation-cell left-cell source-operation)
            (project-right-operation-position
              (judgment-mapped-operation-cell right-cell source-operation)
              right-position))
          (lax-boundary-coherence middle source-operation
            (project-right-operation-position
              (judgment-mapped-operation-cell right-cell source-operation)
              right-position))
          (operation-boundary-coherence
            (judgment-mapped-operation-cell right-cell source-operation)
            right-position)
          (lax-boundary-coherence right source-operation right-position)
          (judgment-mapped-boundary-square left-cell source-operation
            (project-right-operation-position
              (judgment-mapped-operation-cell right-cell source-operation)
              right-position))
          (judgment-mapped-boundary-square right-cell source-operation
            right-position)
    }

------------------------------------------------------------------------
-- Identity, composition, and forgetting an exact translation

module _ {ℓj ℓo ℓp : Level} {J : Set ℓj}
  (signature : Signature-Over J ℓo ℓp) where

  identity-lax-signature-translation :
    Lax-Signature-Translation (λ judgment → judgment) signature signature
  identity-lax-signature-translation = record
    { map-lax-operation = λ source-operation → source-operation
    ; project-lax-position = λ source-operation target-position →
        target-position
    ; lax-boundary-coherence = λ source-operation target-position → refl
    }

module _ {ℓj₁ ℓo₁ ℓp₁ ℓj₂ ℓo₂ ℓp₂ ℓj₃ ℓo₃ ℓp₃ : Level}
  {Judgment₁ : Set ℓj₁} {Judgment₂ : Set ℓj₂} {Judgment₃ : Set ℓj₃}
  {on-judgment₁ : Judgment₁ → Judgment₂}
  {on-judgment₂ : Judgment₂ → Judgment₃}
  {source : Signature-Over Judgment₁ ℓo₁ ℓp₁}
  {middle : Signature-Over Judgment₂ ℓo₂ ℓp₂}
  {target : Signature-Over Judgment₃ ℓo₃ ℓp₃}
  (first : Lax-Signature-Translation on-judgment₁ source middle)
  (second : Lax-Signature-Translation on-judgment₂ middle target) where

  compose-lax-signature-translation :
    Lax-Signature-Translation
      (λ judgment → on-judgment₂ (on-judgment₁ judgment)) source target
  compose-lax-signature-translation = record
    { map-lax-operation = λ source-operation →
        map-lax-operation second (map-lax-operation first source-operation)
    ; project-lax-position = λ source-operation target-position →
        project-lax-position first source-operation
          (project-lax-position second
            (map-lax-operation first source-operation) target-position)
    ; lax-boundary-coherence = λ source-operation target-position →
        ap on-judgment₂
          (lax-boundary-coherence first source-operation
            (project-lax-position second
              (map-lax-operation first source-operation) target-position))
          ∙ lax-boundary-coherence second
            (map-lax-operation first source-operation) target-position
    }

  compose-lax-signature-translation-map-operation :
    {judgment : Judgment₁} (source-operation : Operation source judgment) →
    map-lax-operation compose-lax-signature-translation source-operation
      ＝ map-lax-operation second (map-lax-operation first source-operation)
  compose-lax-signature-translation-map-operation source-operation = refl

  compose-lax-signature-translation-project-position :
    {judgment : Judgment₁} (source-operation : Operation source judgment)
    (target-position :
      Position target
        (map-lax-operation second
          (map-lax-operation first source-operation))) →
    project-lax-position compose-lax-signature-translation source-operation
      target-position
      ＝ project-lax-position first source-operation
        (project-lax-position second
          (map-lax-operation first source-operation) target-position)
  compose-lax-signature-translation-project-position source-operation
    target-position = refl

module _ {ℓj ℓo ℓp : Level} {J : Set ℓj}
  {signature : Signature-Over J ℓo ℓp} where

  identity-lax-signature-translation-map-operation : {judgment : J}
    (source-operation : Operation signature judgment) →
    map-lax-operation (identity-lax-signature-translation signature)
      source-operation
      ＝ source-operation
  identity-lax-signature-translation-map-operation source-operation = refl

  identity-lax-signature-translation-project-position : {judgment : J}
    (source-operation : Operation signature judgment)
    (target-position : Position signature source-operation) →
    project-lax-position (identity-lax-signature-translation signature)
      source-operation target-position
      ＝ target-position
  identity-lax-signature-translation-project-position source-operation
    target-position = refl

module _ {ℓj₁ ℓo₁ ℓp₁ ℓj₂ ℓo₂ ℓp₂ : Level} {Source-Judgment : Set ℓj₁}
  {Target-Judgment : Set ℓj₂}
  (source : Signature-Over Source-Judgment ℓo₁ ℓp₁)
  (target : Signature-Over Target-Judgment ℓo₂ ℓp₂) where

  exact-signature-translation-to-lax :
    (translation :
      Signature-Translation (to-signature source) (to-signature target)) →
    Lax-Signature-Translation (map-judgment translation) source target
  exact-signature-translation-to-lax translation = record
    { map-lax-operation = map-operation translation
    ; project-lax-position = project-position translation
    ; lax-boundary-coherence = boundary-coherence translation
    }
