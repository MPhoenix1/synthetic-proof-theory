{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.Signature.Polynomial where

-- Quotient-free heterogeneous polynomials and their exact comparison with
-- the dependent signatures of Foundation.Signature. A polynomial from input
-- colors to output colors has operations at every output, positions at
-- every operation and an input color at every position (`Polynomial`):
--
--   Input ← Σ (j : Output). Σ (o : Operation j). Position o
--         → Σ (j : Output). Operation j → Output.
--
-- Positions are data, not merely their input colors. The extension at a
-- family X is the total space of the displayed space with the operations as
-- base and the dependent child functions as fibers
-- (`polynomial-extension-space`),
--
--   Total (polynomial-extension-space P X j)
--     = Σ (o : Operation P j). Π (p : Position P o). X (input P o p),
--
-- and pointwise maps of children act inside its fibers
-- (`map-polynomial-extension`), with identity and composition pointwise by
-- refl, and as identifications under extensionality for the child
-- functions. Endopolynomials are exactly the signatures over a fixed
-- judgment type, and bundled endopolynomials exactly the signatures, with
-- both round trips by refl (`polynomial-signature-over-isomorphism`,
-- `signature-polynomial-isomorphism`). A cartesian morphism keeps an
-- isomorphism of the position fibers of each operation with input
-- coherence along it (`Cartesian-Polynomial-Morphism`); morphisms have
-- identities and composites, and between the polynomials of two signatures
-- over one judgment map they are exactly the signature translations,
-- preserving identity and composition fieldwise. No composition of
-- polynomials, monad, tree, Retention correspondence or equipment law is
-- supplied here.
--
-- The morphisms between the polynomials of two signatures over one judgment
-- map are `Signature-Polynomial-Morphism`.

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Extensionality using (FunExt)
open import SPT.Cubical.Foundation.Isomorphisms using
  ( _≅_; forward; backward; backward-forward; forward-backward; ≅-refl
  ; ≅-trans
  )
open import SPT.Cubical.Foundation.Spaces using (DΣ; Total)
open import SPT.Cubical.Foundation.Spaces.Vertical using
  (family-displayed-space; Fiber-Map; fiber-map-total-map)
open import SPT.Cubical.Foundation.Signature using
  (Signature; Judgment; Op; Pos; boundary)
open import SPT.Cubical.Foundation.Signature.Sum using
  ( Signature-Over; module Signature-Over; position-boundary; to-signature
  ; from-signature
  )
open import SPT.Cubical.Foundation.Signature.Translation using
  ( Signature-Translation; map-judgment; map-operation; map-position
  ; project-position; project-map-position; map-project-position
  ; boundary-coherence; identity-signature-translation
  ; compose-signature-translation
  )

------------------------------------------------------------------------
-- Heterogeneous indexed polynomials

-- The output selects an operation fiber, and every position of a selected
-- operation retains its exact input color; distinct positions with one
-- input color stay distinguishable.

record Polynomial {ℓi ℓj : Level} (Input : Set ℓi) (Output : Set ℓj)
  (ℓo ℓp : Level) : Set (lsuc (ℓi ⊔ ℓj ⊔ ℓo ⊔ ℓp)) where
  field
    Operation : Output → Set ℓo
    Position : {output : Output} → Operation output → Set ℓp
    input : {output : Output} (operation : Operation output) →
      Position operation → Input

open Polynomial public

------------------------------------------------------------------------
-- Extensions and pointwise action

-- The complete operation is the literal base of the child telescope, so
-- pointwise child maps act inside its fiber and cannot replace it.

module _ {ℓi ℓj ℓo ℓp ℓx : Level} {Input : Set ℓi} {Output : Set ℓj}
  (polynomial : Polynomial Input Output ℓo ℓp) (X : Input → Set ℓx) where

  polynomial-extension-space : Output → DΣ ℓo (ℓp ⊔ ℓx)
  polynomial-extension-space output =
    family-displayed-space (Operation polynomial output)
      (λ o → (p : Position polynomial o) → X (input polynomial o p))

module _ {ℓi ℓj ℓo ℓp ℓx ℓy : Level} {Input : Set ℓi} {Output : Set ℓj}
  (polynomial : Polynomial Input Output ℓo ℓp) {X : Input → Set ℓx}
  {Y : Input → Set ℓy} (on-child : (color : Input) → X color → Y color)
  where

  map-polynomial-children : (output : Output) →
    Fiber-Map (Operation polynomial output)
      (λ o → (p : Position polynomial o) → X (input polynomial o p))
      (λ o → (p : Position polynomial o) → Y (input polynomial o p))
  map-polynomial-children output o children p =
    on-child (input polynomial o p) (children p)

  map-polynomial-extension : {output : Output} →
    Total (polynomial-extension-space polynomial X output) →
    Total (polynomial-extension-space polynomial Y output)
  map-polynomial-extension {output} (o , children) =
    fiber-map-total-map (map-polynomial-children output) o children

  map-polynomial-extension-operation : {output : Output}
    (extension : Total (polynomial-extension-space polynomial X output)) →
    pr₁ (map-polynomial-extension extension) ＝ pr₁ extension
  map-polynomial-extension-operation (o , children) = refl

  map-polynomial-extension-child : {output : Output}
    (o : Operation polynomial output)
    (children : (p : Position polynomial o) → X (input polynomial o p))
    (p : Position polynomial o) →
    pr₂ (map-polynomial-extension (o , children)) p
      ＝ on-child (input polynomial o p) (children p)
  map-polynomial-extension-child o children p = refl

module _ {ℓi ℓj ℓo ℓp ℓx : Level} {Input : Set ℓi} {Output : Set ℓj}
  (polynomial : Polynomial Input Output ℓo ℓp) (X : Input → Set ℓx) where

  map-polynomial-extension-identity-child : {output : Output}
    (o : Operation polynomial output)
    (children : (p : Position polynomial o) → X (input polynomial o p))
    (p : Position polynomial o) →
    pr₂ (map-polynomial-extension polynomial
      (λ (color : Input) (child : X color) → child) (o , children)) p
      ＝ children p
  map-polynomial-extension-identity-child o children p = refl

module _ {ℓi ℓj ℓo ℓp ℓx ℓy ℓz : Level} {Input : Set ℓi} {Output : Set ℓj}
  (polynomial : Polynomial Input Output ℓo ℓp) {X : Input → Set ℓx}
  {Y : Input → Set ℓy} {Z : Input → Set ℓz}
  (first : (color : Input) → X color → Y color)
  (second : (color : Input) → Y color → Z color) where

  map-polynomial-extension-composition-child : {output : Output}
    (o : Operation polynomial output)
    (children : (p : Position polynomial o) → X (input polynomial o p))
    (p : Position polynomial o) →
    pr₂ (map-polynomial-extension polynomial second
      (map-polynomial-extension polynomial first (o , children))) p
      ＝ pr₂ (map-polynomial-extension polynomial
        (λ color child → second color (first color child)) (o , children))
        p
  map-polynomial-extension-composition-child o children p = refl

------------------------------------------------------------------------
-- Identifications of complete extensions

-- Under extensionality for the child functions of each operation, passed
-- explicitly, the operation stays literal on both sides and pointwise
-- agreement of the children identifies the extensions. No polynomial,
-- operation, position or translation is identified, and no computation
-- law is added.

module _ {ℓi ℓj ℓo ℓp ℓx : Level} {Input : Set ℓi} {Output : Set ℓj}
  (polynomial : Polynomial Input Output ℓo ℓp) (X : Input → Set ℓx)
  (extensionality : {output : Output} (o : Operation polynomial output) →
    FunExt (Position polynomial o) (λ p → X (input polynomial o p)))
  where

  same-operation-equality : {output : Output}
    (o : Operation polynomial output)
    (left right : (p : Position polynomial o) → X (input polynomial o p)) →
    ((p : Position polynomial o) → left p ＝ right p) →
    _＝_ {A = Total (polynomial-extension-space polynomial X output)}
      (o , left) (o , right)
  same-operation-equality o left right pointwise =
    ap
      (λ (children : (p : Position polynomial o) →
          X (input polynomial o p)) → o , children)
      (extensionality o left right pointwise)

  map-polynomial-extension-identity : {output : Output}
    (extension : Total (polynomial-extension-space polynomial X output)) →
    map-polynomial-extension polynomial
      (λ (color : Input) (child : X color) → child) extension
      ＝ extension
  map-polynomial-extension-identity (o , children) =
    same-operation-equality o (λ p → children p) children
      (map-polynomial-extension-identity-child polynomial X o children)

  map-polynomial-extension-composition : {ℓw ℓy : Level}
    {W : Input → Set ℓw} {Y : Input → Set ℓy}
    (first : (color : Input) → W color → Y color)
    (second : (color : Input) → Y color → X color) {output : Output}
    (extension : Total (polynomial-extension-space polynomial W output)) →
    map-polynomial-extension polynomial second
      (map-polynomial-extension polynomial first extension)
      ＝ map-polynomial-extension polynomial
        (λ color child → second color (first color child)) extension
  map-polynomial-extension-composition first second (o , children) =
    same-operation-equality o
      (λ p → second (input polynomial o p)
        (first (input polynomial o p) (children p)))
      (λ p → second (input polynomial o p)
        (first (input polynomial o p) (children p)))
      (map-polynomial-extension-composition-child polynomial first second o
        children)

------------------------------------------------------------------------
-- Endopolynomials and signatures

-- A signature over a fixed judgment type is already an endopolynomial; the
-- two maps rename the three fields and reconstruct nothing.

module _ {ℓi ℓo ℓp : Level} {Input : Set ℓi} where

  polynomial-to-signature-over : Polynomial Input Input ℓo ℓp →
    Signature-Over Input ℓo ℓp
  polynomial-to-signature-over polynomial = record
    { Operation = Operation polynomial
    ; Position = Position polynomial
    ; position-boundary = input polynomial
    }

  signature-over-to-polynomial : Signature-Over Input ℓo ℓp →
    Polynomial Input Input ℓo ℓp
  signature-over-to-polynomial signature = record
    { Operation = Signature-Over.Operation signature
    ; Position = Signature-Over.Position signature
    ; input = position-boundary signature
    }

  signature-over-to-polynomial-to-signature-over :
    (polynomial : Polynomial Input Input ℓo ℓp) →
    signature-over-to-polynomial (polynomial-to-signature-over polynomial)
      ＝ polynomial
  signature-over-to-polynomial-to-signature-over polynomial = refl

  polynomial-to-signature-over-to-polynomial :
    (signature : Signature-Over Input ℓo ℓp) →
    polynomial-to-signature-over (signature-over-to-polynomial signature)
      ＝ signature
  polynomial-to-signature-over-to-polynomial signature = refl

  polynomial-signature-over-isomorphism :
    Polynomial Input Input ℓo ℓp ≅ Signature-Over Input ℓo ℓp
  polynomial-signature-over-isomorphism = record
    { forward = polynomial-to-signature-over
    ; backward = signature-over-to-polynomial
    ; backward-forward = signature-over-to-polynomial-to-signature-over
    ; forward-backward = polynomial-to-signature-over-to-polynomial
    }

module _ {ℓj ℓo ℓp : Level} where

  signature-polynomial : (signature : Signature ℓj ℓo ℓp) →
    Polynomial (Judgment signature) (Judgment signature) ℓo ℓp
  signature-polynomial signature =
    signature-over-to-polynomial (from-signature signature)

Bundled-Endopolynomial : (ℓj ℓo ℓp : Level) → Set (lsuc (ℓj ⊔ ℓo ⊔ ℓp))
Bundled-Endopolynomial ℓj ℓo ℓp =
  Σ (Set ℓj) (λ colors → Polynomial colors colors ℓo ℓp)

module _ {ℓj ℓo ℓp : Level} where

  signature-to-bundled-endopolynomial : Signature ℓj ℓo ℓp →
    Bundled-Endopolynomial ℓj ℓo ℓp
  signature-to-bundled-endopolynomial signature =
    Judgment signature , signature-polynomial signature

  bundled-endopolynomial-to-signature : Bundled-Endopolynomial ℓj ℓo ℓp →
    Signature ℓj ℓo ℓp
  bundled-endopolynomial-to-signature (colors , polynomial) =
    to-signature (polynomial-to-signature-over polynomial)

  bundled-endopolynomial-to-signature-to-bundled :
    (signature : Signature ℓj ℓo ℓp) →
    bundled-endopolynomial-to-signature
      (signature-to-bundled-endopolynomial signature)
      ＝ signature
  bundled-endopolynomial-to-signature-to-bundled signature = refl

  signature-to-bundled-endopolynomial-to-signature :
    (polynomial : Bundled-Endopolynomial ℓj ℓo ℓp) →
    signature-to-bundled-endopolynomial
      (bundled-endopolynomial-to-signature polynomial)
      ＝ polynomial
  signature-to-bundled-endopolynomial-to-signature polynomial = refl

  signature-polynomial-isomorphism :
    Signature ℓj ℓo ℓp ≅ Bundled-Endopolynomial ℓj ℓo ℓp
  signature-polynomial-isomorphism = record
    { forward = signature-to-bundled-endopolynomial
    ; backward = bundled-endopolynomial-to-signature
    ; backward-forward = bundled-endopolynomial-to-signature-to-bundled
    ; forward-backward = signature-to-bundled-endopolynomial-to-signature
    }

------------------------------------------------------------------------
-- Cartesian polynomial morphisms

-- Over maps of input and output colors, every operation maps to one of the
-- target, its position fiber is isomorphic to that of its image, and input
-- colors agree from a target position to its exact source preimage. The
-- isomorphism keeps both maps and both inverse witnesses; no naturality,
-- extension cell or identification of morphisms is supplied.

record Cartesian-Polynomial-Morphism
  {ℓi₁ ℓj₁ ℓo₁ ℓp₁ ℓi₂ ℓj₂ ℓo₂ ℓp₂ : Level}
  {Input₁ : Set ℓi₁} {Output₁ : Set ℓj₁}
  {Input₂ : Set ℓi₂} {Output₂ : Set ℓj₂}
  (on-input : Input₁ → Input₂) (on-output : Output₁ → Output₂)
  (source : Polynomial Input₁ Output₁ ℓo₁ ℓp₁)
  (target : Polynomial Input₂ Output₂ ℓo₂ ℓp₂)
  : Set (lsuc (ℓi₁ ⊔ ℓj₁ ⊔ ℓo₁ ⊔ ℓp₁ ⊔ ℓi₂ ⊔ ℓj₂ ⊔ ℓo₂ ⊔ ℓp₂)) where
  field
    map-polynomial-operation : {output : Output₁} →
      Operation source output → Operation target (on-output output)
    position-isomorphism : {output : Output₁}
      (o : Operation source output) →
      Position source o ≅ Position target (map-polynomial-operation o)
    input-coherence : {output : Output₁} (o : Operation source output)
      (q : Position target (map-polynomial-operation o)) →
      on-input (input source o (backward (position-isomorphism o) q))
        ＝ input target (map-polynomial-operation o) q

open Cartesian-Polynomial-Morphism public

-- Identities, and composites of `first` followed by `second`: the composite
-- isomorphism keeps both position maps and both inverse witnesses, and its
-- backward map projects through `second`, then through `first`.

module _ {ℓi ℓj ℓo ℓp : Level} {Input : Set ℓi} {Output : Set ℓj}
  (polynomial : Polynomial Input Output ℓo ℓp) where

  identity-cartesian-polynomial-morphism :
    Cartesian-Polynomial-Morphism (λ color → color) (λ color → color)
      polynomial polynomial
  identity-cartesian-polynomial-morphism = record
    { map-polynomial-operation = λ o → o
    ; position-isomorphism = λ o → ≅-refl
    ; input-coherence = λ o q → refl
    }

  identity-cartesian-polynomial-morphism-map-operation : {output : Output}
    (o : Operation polynomial output) →
    map-polynomial-operation identity-cartesian-polynomial-morphism o ＝ o
  identity-cartesian-polynomial-morphism-map-operation o = refl

  identity-cartesian-polynomial-morphism-map-position : {output : Output}
    (o : Operation polynomial output) (p : Position polynomial o) →
    forward (position-isomorphism identity-cartesian-polynomial-morphism o) p
      ＝ p
  identity-cartesian-polynomial-morphism-map-position o p = refl

  identity-cartesian-polynomial-morphism-project-position :
    {output : Output} (o : Operation polynomial output)
    (p : Position polynomial o) →
    backward (position-isomorphism identity-cartesian-polynomial-morphism o)
      p
      ＝ p
  identity-cartesian-polynomial-morphism-project-position o p = refl

module _ {ℓi₁ ℓj₁ ℓo₁ ℓp₁ ℓi₂ ℓj₂ ℓo₂ ℓp₂ ℓi₃ ℓj₃ ℓo₃ ℓp₃ : Level}
  {Input₁ : Set ℓi₁} {Output₁ : Set ℓj₁}
  {Input₂ : Set ℓi₂} {Output₂ : Set ℓj₂}
  {Input₃ : Set ℓi₃} {Output₃ : Set ℓj₃}
  {on-input₁ : Input₁ → Input₂} {on-output₁ : Output₁ → Output₂}
  {on-input₂ : Input₂ → Input₃} {on-output₂ : Output₂ → Output₃}
  {source : Polynomial Input₁ Output₁ ℓo₁ ℓp₁}
  {middle : Polynomial Input₂ Output₂ ℓo₂ ℓp₂}
  {target : Polynomial Input₃ Output₃ ℓo₃ ℓp₃}
  (first : Cartesian-Polynomial-Morphism on-input₁ on-output₁ source middle)
  (second :
    Cartesian-Polynomial-Morphism on-input₂ on-output₂ middle target)
  where

  compose-cartesian-polynomial-morphism :
    Cartesian-Polynomial-Morphism (λ color → on-input₂ (on-input₁ color))
      (λ color → on-output₂ (on-output₁ color)) source target
  compose-cartesian-polynomial-morphism = record
    { map-polynomial-operation = λ o →
        map-polynomial-operation second (map-polynomial-operation first o)
    ; position-isomorphism = λ o →
        ≅-trans (position-isomorphism first o)
          (position-isomorphism second (map-polynomial-operation first o))
    ; input-coherence = λ o q →
        ap on-input₂
          (input-coherence first o
            (backward
              (position-isomorphism second (map-polynomial-operation first o))
              q))
          ∙ input-coherence second (map-polynomial-operation first o) q
    }

  compose-cartesian-polynomial-morphism-map-operation : {output : Output₁}
    (o : Operation source output) →
    map-polynomial-operation compose-cartesian-polynomial-morphism o
      ＝ map-polynomial-operation second (map-polynomial-operation first o)
  compose-cartesian-polynomial-morphism-map-operation o = refl

  compose-cartesian-polynomial-morphism-map-position : {output : Output₁}
    (o : Operation source output) (p : Position source o) →
    forward (position-isomorphism compose-cartesian-polynomial-morphism o) p
      ＝ forward
        (position-isomorphism second (map-polynomial-operation first o))
        (forward (position-isomorphism first o) p)
  compose-cartesian-polynomial-morphism-map-position o p = refl

  compose-cartesian-polynomial-morphism-project-position :
    {output : Output₁} (o : Operation source output)
    (q : Position target
      (map-polynomial-operation second (map-polynomial-operation first o))) →
    backward (position-isomorphism compose-cartesian-polynomial-morphism o)
      q
      ＝ backward (position-isomorphism first o)
        (backward
          (position-isomorphism second (map-polynomial-operation first o))
          q)
  compose-cartesian-polynomial-morphism-project-position o q = refl

------------------------------------------------------------------------
-- Signature translations as cartesian morphisms

-- Between the polynomials of two signatures, over one map of judgments on
-- both colors, cartesian morphisms are exactly the signature translations:
-- the round trip from a translation is refl and the other direction
-- computes fieldwise.

module _ {ℓj₁ ℓo₁ ℓp₁ ℓj₂ ℓo₂ ℓp₂ : Level} where

  Signature-Polynomial-Morphism : Signature ℓj₁ ℓo₁ ℓp₁ →
    Signature ℓj₂ ℓo₂ ℓp₂ →
    Set (lsuc (ℓj₁ ⊔ ℓo₁ ⊔ ℓp₁ ⊔ ℓj₂ ⊔ ℓo₂ ⊔ ℓp₂))
  Signature-Polynomial-Morphism source target =
    Σ (Judgment source → Judgment target) (λ judgment-map →
      Cartesian-Polynomial-Morphism judgment-map judgment-map
        (signature-polynomial source) (signature-polynomial target))

module _ {ℓj₁ ℓo₁ ℓp₁ ℓj₂ ℓo₂ ℓp₂ : Level}
  {source : Signature ℓj₁ ℓo₁ ℓp₁} {target : Signature ℓj₂ ℓo₂ ℓp₂} where

  signature-translation-to-polynomial-morphism :
    Signature-Translation source target →
    Signature-Polynomial-Morphism source target
  signature-translation-to-polynomial-morphism translation =
    map-judgment translation , record
      { map-polynomial-operation = map-operation translation
      ; position-isomorphism = λ o → record
          { forward = map-position translation o
          ; backward = project-position translation o
          ; backward-forward = project-map-position translation o
          ; forward-backward = map-project-position translation o
          }
      ; input-coherence = boundary-coherence translation
      }

  polynomial-morphism-to-signature-translation :
    Signature-Polynomial-Morphism source target →
    Signature-Translation source target
  polynomial-morphism-to-signature-translation (judgment-map , morphism) =
    record
      { map-judgment = judgment-map
      ; map-operation = map-polynomial-operation morphism
      ; map-position = λ o → forward (position-isomorphism morphism o)
      ; project-position = λ o → backward (position-isomorphism morphism o)
      ; project-map-position = λ o →
          backward-forward (position-isomorphism morphism o)
      ; map-project-position = λ o →
          forward-backward (position-isomorphism morphism o)
      ; boundary-coherence = input-coherence morphism
      }

  signature-translation-to-polynomial-and-back :
    (translation : Signature-Translation source target) →
    polynomial-morphism-to-signature-translation
      (signature-translation-to-polynomial-morphism translation)
      ＝ translation
  signature-translation-to-polynomial-and-back translation = refl

  polynomial-signature-translation-map-judgment :
    (morphism : Signature-Polynomial-Morphism source target)
    (judgment : Judgment source) →
    map-judgment (polynomial-morphism-to-signature-translation morphism)
      judgment
      ＝ pr₁ morphism judgment
  polynomial-signature-translation-map-judgment morphism judgment = refl

  polynomial-signature-translation-map-operation :
    (morphism : Signature-Polynomial-Morphism source target)
    {output : Judgment source} (o : Op source output) →
    map-operation (polynomial-morphism-to-signature-translation morphism) o
      ＝ map-polynomial-operation (pr₂ morphism) o
  polynomial-signature-translation-map-operation morphism o = refl

  polynomial-signature-translation-map-position :
    (morphism : Signature-Polynomial-Morphism source target)
    {output : Judgment source} (o : Op source output) (p : Pos source o) →
    map-position (polynomial-morphism-to-signature-translation morphism) o
      p
      ＝ forward (position-isomorphism (pr₂ morphism) o) p
  polynomial-signature-translation-map-position morphism o p = refl

  polynomial-signature-translation-project-position :
    (morphism : Signature-Polynomial-Morphism source target)
    {output : Judgment source} (o : Op source output)
    (q : Pos target (map-polynomial-operation (pr₂ morphism) o)) →
    project-position (polynomial-morphism-to-signature-translation morphism)
      o q
      ＝ backward (position-isomorphism (pr₂ morphism) o) q
  polynomial-signature-translation-project-position morphism o q = refl

  polynomial-signature-translation-boundary-coherence :
    (morphism : Signature-Polynomial-Morphism source target)
    {output : Judgment source} (o : Op source output)
    (q : Pos target (map-polynomial-operation (pr₂ morphism) o)) →
    boundary-coherence
      (polynomial-morphism-to-signature-translation morphism) o q
      ＝ input-coherence (pr₂ morphism) o q
  polynomial-signature-translation-boundary-coherence morphism o q = refl

------------------------------------------------------------------------
-- Fieldwise preservation of identity and composition

module _ {ℓj ℓo ℓp : Level} (signature : Signature ℓj ℓo ℓp) where

  identity-signature-polynomial-morphism :
    Signature-Polynomial-Morphism signature signature
  identity-signature-polynomial-morphism =
    (λ judgment → judgment) ,
    identity-cartesian-polynomial-morphism (signature-polynomial signature)

  signature-identity-polynomial-map-judgment :
    (judgment : Judgment signature) →
    pr₁ (signature-translation-to-polynomial-morphism
      (identity-signature-translation signature)) judgment
      ＝ pr₁ identity-signature-polynomial-morphism judgment
  signature-identity-polynomial-map-judgment judgment = refl

  signature-identity-polynomial-map-operation :
    {judgment : Judgment signature} (o : Op signature judgment) →
    map-polynomial-operation
      (pr₂ (signature-translation-to-polynomial-morphism
        (identity-signature-translation signature)))
      o
      ＝ map-polynomial-operation (pr₂ identity-signature-polynomial-morphism)
        o
  signature-identity-polynomial-map-operation o = refl

  signature-identity-polynomial-map-position :
    {judgment : Judgment signature} (o : Op signature judgment)
    (p : Pos signature o) →
    forward
      (position-isomorphism
        (pr₂ (signature-translation-to-polynomial-morphism
          (identity-signature-translation signature)))
        o)
      p
      ＝ forward
        (position-isomorphism (pr₂ identity-signature-polynomial-morphism)
          o)
        p
  signature-identity-polynomial-map-position o p = refl

  signature-identity-polynomial-project-position :
    {judgment : Judgment signature} (o : Op signature judgment)
    (p : Pos signature o) →
    backward
      (position-isomorphism
        (pr₂ (signature-translation-to-polynomial-morphism
          (identity-signature-translation signature)))
        o)
      p
      ＝ backward
        (position-isomorphism (pr₂ identity-signature-polynomial-morphism)
          o)
        p
  signature-identity-polynomial-project-position o p = refl

  signature-identity-polynomial-project-map-position :
    {judgment : Judgment signature} (o : Op signature judgment)
    (p : Pos signature o) →
    backward-forward
      (position-isomorphism
        (pr₂ (signature-translation-to-polynomial-morphism
          (identity-signature-translation signature)))
        o)
      p
      ＝ backward-forward
        (position-isomorphism (pr₂ identity-signature-polynomial-morphism)
          o)
        p
  signature-identity-polynomial-project-map-position o p = refl

  signature-identity-polynomial-map-project-position :
    {judgment : Judgment signature} (o : Op signature judgment)
    (p : Pos signature o) →
    forward-backward
      (position-isomorphism
        (pr₂ (signature-translation-to-polynomial-morphism
          (identity-signature-translation signature)))
        o)
      p
      ＝ forward-backward
        (position-isomorphism (pr₂ identity-signature-polynomial-morphism)
          o)
        p
  signature-identity-polynomial-map-project-position o p = refl

  signature-identity-polynomial-input-coherence :
    {judgment : Judgment signature} (o : Op signature judgment)
    (p : Pos signature o) →
    input-coherence
      (pr₂ (signature-translation-to-polynomial-morphism
        (identity-signature-translation signature)))
      o p
      ＝ input-coherence (pr₂ identity-signature-polynomial-morphism) o p
  signature-identity-polynomial-input-coherence o p = refl

module _ {ℓj₁ ℓo₁ ℓp₁ ℓj₂ ℓo₂ ℓp₂ ℓj₃ ℓo₃ ℓp₃ : Level}
  {source : Signature ℓj₁ ℓo₁ ℓp₁} {middle : Signature ℓj₂ ℓo₂ ℓp₂}
  {target : Signature ℓj₃ ℓo₃ ℓp₃}
  (first : Signature-Translation source middle)
  (second : Signature-Translation middle target) where

  compose-signature-polynomial-morphisms :
    Signature-Polynomial-Morphism source target
  compose-signature-polynomial-morphisms =
    (λ judgment → map-judgment second (map-judgment first judgment)) ,
    compose-cartesian-polynomial-morphism
      (pr₂ (signature-translation-to-polynomial-morphism first))
      (pr₂ (signature-translation-to-polynomial-morphism second))

  signature-composition-polynomial-map-judgment :
    (judgment : Judgment source) →
    pr₁ (signature-translation-to-polynomial-morphism
      (compose-signature-translation first second)) judgment
      ＝ pr₁ compose-signature-polynomial-morphisms judgment
  signature-composition-polynomial-map-judgment judgment = refl

  signature-composition-polynomial-map-operation :
    {judgment : Judgment source} (o : Op source judgment) →
    map-polynomial-operation
      (pr₂ (signature-translation-to-polynomial-morphism
        (compose-signature-translation first second)))
      o
      ＝ map-polynomial-operation (pr₂ compose-signature-polynomial-morphisms)
        o
  signature-composition-polynomial-map-operation o = refl

  signature-composition-polynomial-map-position :
    {judgment : Judgment source} (o : Op source judgment)
    (p : Pos source o) →
    forward
      (position-isomorphism
        (pr₂ (signature-translation-to-polynomial-morphism
          (compose-signature-translation first second)))
        o)
      p
      ＝ forward
        (position-isomorphism (pr₂ compose-signature-polynomial-morphisms)
          o)
        p
  signature-composition-polynomial-map-position o p = refl

  signature-composition-polynomial-project-position :
    {judgment : Judgment source} (o : Op source judgment)
    (q : Pos target (map-operation second (map-operation first o))) →
    backward
      (position-isomorphism
        (pr₂ (signature-translation-to-polynomial-morphism
          (compose-signature-translation first second)))
        o)
      q
      ＝ backward
        (position-isomorphism (pr₂ compose-signature-polynomial-morphisms)
          o)
        q
  signature-composition-polynomial-project-position o q = refl

  signature-composition-polynomial-project-map-position :
    {judgment : Judgment source} (o : Op source judgment)
    (p : Pos source o) →
    backward-forward
      (position-isomorphism
        (pr₂ (signature-translation-to-polynomial-morphism
          (compose-signature-translation first second)))
        o)
      p
      ＝ backward-forward
        (position-isomorphism (pr₂ compose-signature-polynomial-morphisms)
          o)
        p
  signature-composition-polynomial-project-map-position o p = refl

  signature-composition-polynomial-map-project-position :
    {judgment : Judgment source} (o : Op source judgment)
    (q : Pos target (map-operation second (map-operation first o))) →
    forward-backward
      (position-isomorphism
        (pr₂ (signature-translation-to-polynomial-morphism
          (compose-signature-translation first second)))
        o)
      q
      ＝ forward-backward
        (position-isomorphism (pr₂ compose-signature-polynomial-morphisms)
          o)
        q
  signature-composition-polynomial-map-project-position o q = refl

  signature-composition-polynomial-input-coherence :
    {judgment : Judgment source} (o : Op source judgment)
    (q : Pos target (map-operation second (map-operation first o))) →
    input-coherence
      (pr₂ (signature-translation-to-polynomial-morphism
        (compose-signature-translation first second)))
      o q
      ＝ input-coherence (pr₂ compose-signature-polynomial-morphisms) o q
  signature-composition-polynomial-input-coherence o q = refl
