{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.DS.Realization.Family where

-- Families of codes in a closure of the ambient family, and the names the
-- closure gives them. The operator's returned family names every member at
-- its code (`name`, `action`); a named type and a family of codes over it
-- name their sum (`sum`). Adjoining an assignment q : A → K to a family F,
-- along a name of A, gives one family containing both, with both inclusions
-- keeping the decodings (`Extension`, `extend`).

open import SPT.Base
import SPT.Mahlo.Ambient as Ambient
import SPT.Mahlo.Specification as Specification

open import SPT.IR.Description using
  (Indexed; indexed; carrier; index)

------------------------------------------------------------------------
-- Transport along an identity of types

cast : {ℓ : Level} {A B : Set ℓ} → A ＝ B → A → B
cast refl x = x

cancel :
  {ℓ j : Level} {A B : Set ℓ} {Y : Set j} (e : A ＝ B) (f : B → Y)
  → (λ x → f (cast e (cast (e ⁻¹) x))) ＝ f
cancel refl f = refl

-- The two summands of an extension: the named arity, then the family.
choose : {ℓ : Level} {K : Set ℓ} → K → K → Lift ℓ 𝟚 → K
choose c a (lift ₀) = c
choose c a (lift ₁) = a

------------------------------------------------------------------------
-- Families of codes and their names

-- A family of codes presents the family of decoded types `view`, spelled
-- as the closure's map writes it. An identity of families names each member
-- by its code, so the returned family of the operator names every member of
-- Ψ at a family; a name of d and a family of codes over d name their sum.

module _
  {ℓ : Level} {Ψ : Ambient.Operator ℓ} {K : Set ℓ}
  (L : Specification.Closure (Ambient.formers ℓ) Ψ K)
  where

  open Specification.Closure L using (interpret)

  view :
    Specification.Family (Specification.Decode (λ X → X) interpret)
    → Indexed ℓ (Set ℓ)
  view (a , b) = indexed (interpret a) (λ x → interpret (b x))

  unit : Specification.Family (Specification.Decode (λ X → X) interpret)
  unit =
    pr₁ (Specification.Closure.unit L) ,
    (λ _ → pr₁ (Specification.Closure.unit L))

  name :
    (F : Specification.Family (Specification.Decode (λ X → X) interpret))
    {H : Specification.Family (λ (X : Set ℓ) → X)}
    → Specification.map (λ X → X) interpret F ＝ H
    → (z : pr₁ H) → Specification.Name interpret (pr₂ H z)
  name (a , b) refl z = b z , refl

  action :
    (F : Specification.Family (Specification.Decode (λ X → X) interpret))
    (z : pr₁ (Ψ (Specification.map (λ X → X) interpret F)))
    → Specification.Name interpret
        (pr₂ (Ψ (Specification.map (λ X → X) interpret F)) z)
  action F z =
    name (Specification.Closure.inner L F)
      (Specification.Closure.inner-β L F) z

  reindex :
    (d : Set ℓ) → Specification.Name interpret d → (d → K)
    → Specification.Family (Specification.Decode (λ X → X) interpret)
  reindex d (c , e) b = c , (λ x → b (cast e x))

  reindex-β :
    (d : Set ℓ) (n : Specification.Name interpret d) (b : d → K)
    → Specification.map (λ X → X) interpret (reindex d n b)
      ＝ (d , (λ x → interpret (b x)))
  reindex-β d (c , refl) b = refl

  sum :
    (d : Set ℓ) (n : Specification.Name interpret d) (b : d → K)
    → Specification.Name interpret (Σ d (λ x → interpret (b x)))
  sum d n b =
    pr₁ (Specification.Closure.sum L (reindex d n b)) ,
    ( pr₂ (Specification.Closure.sum L (reindex d n b))
    ∙ ap (Specification.Formers.sum (Ambient.formers ℓ)) (reindex-β d n b))

------------------------------------------------------------------------
-- Extensions of families

-- The extension is the sum over the two-point type of the named arity (at
-- ₀) and the given family (at ₁). Its branch reads q at ₀ and the family at
-- ₁; both inclusions keep the decoding, by `cancel` along the sum's naming
-- identity.

module _
  {ℓ : Level} {Ψ : Ambient.Operator ℓ} {K : Set ℓ}
  (L : Specification.Closure (Ambient.formers ℓ) Ψ K)
  where

  open Specification.Closure L using (interpret)

  branch :
    (c : K) {A : Set ℓ}
    (e : Specification.Decode (λ X → X) interpret c ＝ A) (q : A → K)
    (F : Specification.Family (Specification.Decode (λ X → X) interpret))
    → Σ (Specification.Formers.two (Ambient.formers ℓ))
        (λ u → interpret (choose c (pr₁ F) u))
    → K
  branch c e q F (lift ₀ , x) = q (cast e x)
  branch c e q F (lift ₁ , x) = pr₂ F x

  record Extension
    {A : Set ℓ} (q : A → K)
    (F : Specification.Family (Specification.Decode (λ X → X) interpret)) :
    Set (lsuc ℓ) where
    field
      family :
        Specification.Family (Specification.Decode (λ X → X) interpret)
      left : A → carrier (view L family)
      right : carrier (view L F) → carrier (view L family)
      left-β :
        (λ x → index (view L family) (left x))
        ＝ (λ x → interpret (q x))
      right-β :
        (λ x → index (view L family) (right x)) ＝ index (view L F)

  extend :
    (c : K) {A : Set ℓ}
    (e : Specification.Decode (λ X → X) interpret c ＝ A) (q : A → K)
    (F : Specification.Family (Specification.Decode (λ X → X) interpret))
    → Extension q F
  extend c e q F =
    let named =
          sum L (Specification.Formers.two (Ambient.formers ℓ))
            (Specification.Closure.two L) (choose c (pr₁ F))
        collapse =
          cancel (pr₂ named) (λ x → interpret (branch c e q F x))
    in record
      { family =
          pr₁ named , (λ x → branch c e q F (cast (pr₂ named) x))
      ; left = λ x → cast (pr₂ named ⁻¹) (lift ₀ , cast (e ⁻¹) x)
      ; right = λ x → cast (pr₂ named ⁻¹) (lift ₁ , x)
      ; left-β =
          ap (λ h → λ x → h (lift ₀ , cast (e ⁻¹) x)) collapse
          ∙ cancel e (λ x → interpret (q x))
      ; right-β = ap (λ h → λ x → h (lift ₁ , x)) collapse
      }
