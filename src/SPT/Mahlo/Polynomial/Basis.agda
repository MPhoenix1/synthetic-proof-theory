{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Polynomial.Basis where

-- A small parent containing the carrier of an ordinary induction–recursive
-- universe. The small codes are the relative closure of the identity
-- operator over the ambient formers (`Small`, `small-decode`); as a
-- displayed seed (`small-seed`) they generate the universe of
-- Mahlo.Universe at the identity operator (`Code`, with its formers and
-- laws, `formers`, `laws`), whose code `codes` decodes to them
-- (`codes-decode-to-small`). Under extensionality for the families and
-- branches on decoded codes (`Realization-Extensionality`), every small
-- code is realized by a code of the universe with the identification of
-- their decodings, computed together, a dependent branch translated at the
-- point of its actual domain (`realize`, `include`, `include-β`):
--
--   Universe.decode (include E a) ＝ small-decode a.
--
-- The inclusion names the universe's formers on the small codes, a family
-- on an included domain pulled back along include-β (`pull-family`,
-- `branches-agree`), so the small codes form a closure of the identity
-- operator over the universe (`ordinary`), and the universe reflects it at
-- `codes` (`reflection`).

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.Identifications.Formers using
  (former-path; identity-type-path)
open import SPT.Foundation.Spaces using (DΣ)
open import SPT.Mahlo.Specification using (Formers; Closure; Reflection)
import SPT.Mahlo.Ambient as Ambient
open import SPT.Foundation.Tree.W using (W)
open import SPT.Mahlo.Decoding using (DecodingLaws)
import SPT.Mahlo.Relative as Relative
import SPT.Mahlo.Universe as Universe

------------------------------------------------------------------------
-- The small parent and the universe over it

Small : (ℓ : Level) → Set ℓ
Small ℓ = Relative.Generated (Ambient.formers ℓ) (λ F → F)

small-decode : {ℓ : Level} → Small ℓ → Set ℓ
small-decode {ℓ} = Relative.interpret (Ambient.formers ℓ) (λ F → F)

small-seed : (ℓ : Level) → DΣ ℓ ℓ
small-seed ℓ = record { Base = Small ℓ ; Fiber = small-decode }

Code : (ℓ : Level) → Set ℓ
Code ℓ = Universe.Code (small-seed ℓ) (λ F → F)

formers : (ℓ : Level) → Formers (Code ℓ) Universe.decode
formers ℓ = Universe.formers (small-seed ℓ) (λ F → F)

laws : (ℓ : Level) → DecodingLaws (formers ℓ)
laws ℓ = Universe.laws (small-seed ℓ) (λ F → F)

codes-decode-to-small : {ℓ : Level} →
  Universe.decode {U = small-seed ℓ} {Ψ = λ F → F} Universe.codes ＝ Small ℓ
codes-decode-to-small = refl

------------------------------------------------------------------------
-- Realizing the small codes

-- Equality of dependent functions is isolated here, at the decoded codes
-- where realization uses it.

record Realization-Extensionality (ℓ : Level) : Set (lsuc ℓ) where
  field
    family-extensionality : (c : Code ℓ) →
      FunExt (Universe.decode c) (λ x → Set ℓ)
    branch-extensionality : (c : Code ℓ) →
      FunExt (Universe.decode c) (λ x → Code ℓ)

open Realization-Extensionality public

-- The code and its decoding equation are computed together. In particular,
-- a dependent branch is translated at the point of its actual domain.

realize : {ℓ : Level} (E : Realization-Extensionality ℓ) (a : Small ℓ) →
  Σ (Code ℓ) (λ c → Universe.decode c ＝ small-decode a)
realize E Relative.empty = Universe.empty , refl
realize E Relative.unit = Universe.unit , refl
realize E Relative.two = Universe.two , refl
realize E Relative.natural = Universe.natural , refl
realize E (Relative.product a b) =
  let (c , p) = realize E a in
  Universe.product c
    (λ x → pr₁ (realize E (b (transport (λ X → X) p x)))) ,
  former-path (λ A B → (x : A) → B x) (family-extensionality E c) p
    (λ x → pr₂ (realize E (b (transport (λ X → X) p x))))
realize E (Relative.sum a b) =
  let (c , p) = realize E a in
  Universe.sum c (λ x → pr₁ (realize E (b (transport (λ X → X) p x)))) ,
  former-path Σ (family-extensionality E c) p
    (λ x → pr₂ (realize E (b (transport (λ X → X) p x))))
realize E (Relative.tree a b) =
  let (c , p) = realize E a in
  Universe.tree c (λ x → pr₁ (realize E (b (transport (λ X → X) p x)))) ,
  former-path W (family-extensionality E c) p
    (λ x → pr₂ (realize E (b (transport (λ X → X) p x))))
realize E (Relative.identity a x y) =
  let (c , p) = realize E a in
  Universe.identity c (transport (λ X → X) (p ⁻¹) x)
    (transport (λ X → X) (p ⁻¹) y) ,
  identity-type-path p x y
realize E (Relative.result a b) = realize E a
realize E (Relative.branch a b y) = realize E (b y)

include : {ℓ : Level} → Realization-Extensionality ℓ → Small ℓ → Code ℓ
include E a = pr₁ (realize E a)

include-β : {ℓ : Level} (E : Realization-Extensionality ℓ) (a : Small ℓ) →
  Universe.decode (include E a) ＝ small-decode a
include-β E a = pr₂ (realize E a)

------------------------------------------------------------------------
-- The ordinary closure

module _ {ℓ : Level} (E : Realization-Extensionality ℓ) where

  pull-family : (a : Small ℓ) →
    (Universe.decode (include E a) → Small ℓ) → small-decode a → Small ℓ
  pull-family a b x = b (transport (λ X → X) (include-β E a ⁻¹) x)

  branches-agree : (a : Small ℓ)
    (b : Universe.decode (include E a) → Small ℓ) →
    (λ x → include E
      (pull-family a b (transport (λ X → X) (include-β E a) x)))
      ＝ (λ x → include E (b x))
  branches-agree a b =
    branch-extensionality E (include E a)
      (λ x → include E
        (pull-family a b (transport (λ X → X) (include-β E a) x)))
      (λ x → include E (b x))
      (λ x → ap (λ y → include E (b y))
        (forth-and-back-transport (λ X → X) (include-β E a) x))

  ordinary : Closure (formers ℓ) (λ F → F) (Small ℓ)
  ordinary = record
    { interpret = include E
    ; empty = Relative.empty , refl
    ; unit = Relative.unit , refl
    ; two = Relative.two , refl
    ; natural = Relative.natural , refl
    ; product = λ F →
        Relative.product (pr₁ F) (pull-family (pr₁ F) (pr₂ F)) ,
        ap (Universe.product (include E (pr₁ F)))
          (branches-agree (pr₁ F) (pr₂ F))
    ; sum = λ F →
        Relative.sum (pr₁ F) (pull-family (pr₁ F) (pr₂ F)) ,
        ap (Universe.sum (include E (pr₁ F)))
          (branches-agree (pr₁ F) (pr₂ F))
    ; tree = λ F →
        Relative.tree (pr₁ F) (pull-family (pr₁ F) (pr₂ F)) ,
        ap (Universe.tree (include E (pr₁ F)))
          (branches-agree (pr₁ F) (pr₂ F))
    ; identity = λ a x y →
        Relative.identity a (transport (λ X → X) (include-β E a) x)
          (transport (λ X → X) (include-β E a) y) ,
        ap₂ (Universe.identity (include E a))
          (forth-and-back-transport (λ X → X) (include-β E a) x)
          (forth-and-back-transport (λ X → X) (include-β E a) y)
    ; inner = λ F → F
    ; inner-β = λ F → refl
    }

  reflection : Reflection (formers ℓ) (λ F → F)
  reflection = record { carrier = Universe.codes ; closure = ordinary }
