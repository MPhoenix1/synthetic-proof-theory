{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.DS.Sorted.Family where

-- Families of codes in a closure of the two-sorted family, and the names
-- the closure gives them. A family of codes is a code of an index type with
-- a code at each index, viewed as an indexed family of names (`view`). The
-- operator's returned family names every member (`name`, `action`); a
-- name of any u and a family of codes over the decoding of u name their
-- sum (`reindex`, `sum`). Adjoining an assignment q : A → K to a family F
-- gives one family containing both (`Extension`, `extend`). A copy of
-- Realization.Family for the two-sorted family: identities
-- of names become identities of index types under `decode`.

open import SPT.Base
import SPT.Mahlo.Specification as Specification

open import SPT.IR.Description using
  (Indexed; indexed; carrier; index)
open import SPT.Mahlo.DS.Realization.Family using
  (cast; cancel; choose)
open import SPT.Mahlo.DS.Sorted using (Sort; decode; formers)

------------------------------------------------------------------------
-- Families of codes and their names

module _
  {ℓ κ : Level} {O : Set κ} {Ψ : Specification.Operator (decode ℓ O)}
  {K : Set ℓ} (L : Specification.Closure (formers ℓ O) Ψ K)
  where

  open Specification.Closure L using (interpret)

  view :
    Specification.Family (Specification.Decode (decode ℓ O) interpret)
    → Indexed ℓ (Sort ℓ O)
  view (a , b) = indexed (decode ℓ O (interpret a)) (λ x → interpret (b x))

  unit :
    Specification.Family (Specification.Decode (decode ℓ O) interpret)
  unit =
    pr₁ (Specification.Closure.unit L) ,
    (λ _ → pr₁ (Specification.Closure.unit L))

  name :
    (F : Specification.Family (Specification.Decode (decode ℓ O) interpret))
    {H : Specification.Family (decode ℓ O)}
    → Specification.map (decode ℓ O) interpret F ＝ H
    → (z : decode ℓ O (pr₁ H)) → Specification.Name interpret (pr₂ H z)
  name (a , b) refl z = b z , refl

  action :
    (F : Specification.Family (Specification.Decode (decode ℓ O) interpret))
    (z :
      decode ℓ O (pr₁ (Ψ (Specification.map (decode ℓ O) interpret F))))
    → Specification.Name interpret
        (pr₂ (Ψ (Specification.map (decode ℓ O) interpret F)) z)
  action F z =
    name (Specification.Closure.inner L F)
      (Specification.Closure.inner-β L F) z

  -- A name of u and a family of codes over the decoding of u.
  reindex :
    (u : Sort ℓ O) → Specification.Name interpret u
    → (decode ℓ O u → K)
    → Specification.Family (Specification.Decode (decode ℓ O) interpret)
  reindex u (c , e) b = c , (λ x → b (cast (ap (decode ℓ O) e) x))

  reindex-β :
    (u : Sort ℓ O) (n : Specification.Name interpret u)
    (b : decode ℓ O u → K)
    → Specification.map (decode ℓ O) interpret (reindex u n b)
      ＝ (u , (λ x → interpret (b x)))
  reindex-β u (c , refl) b = refl

  sum :
    (u : Sort ℓ O) (n : Specification.Name interpret u)
    (b : decode ℓ O u → K)
    → Specification.Name interpret
        (Specification.Formers.sum (formers ℓ O)
          (u , (λ x → interpret (b x))))
  sum u n b =
    pr₁ (Specification.Closure.sum L (reindex u n b)) ,
    ( pr₂ (Specification.Closure.sum L (reindex u n b))
    ∙ ap (Specification.Formers.sum (formers ℓ O)) (reindex-β u n b))

------------------------------------------------------------------------
-- Extensions of families

-- The extension is the sum over the two-point type of the named arity (at
-- ₀) and the given family (at ₁); both inclusions keep the names, by
-- `cancel` along the decoded identity of the sum's name.

module _
  {ℓ κ : Level} {O : Set κ} {Ψ : Specification.Operator (decode ℓ O)}
  {K : Set ℓ} (L : Specification.Closure (formers ℓ O) Ψ K)
  where

  open Specification.Closure L using (interpret)

  branch :
    (c : K) {A : Set ℓ} (e : decode ℓ O (interpret c) ＝ A) (q : A → K)
    (F : Specification.Family (Specification.Decode (decode ℓ O) interpret))
    → Σ (Lift ℓ 𝟚) (λ u → decode ℓ O (interpret (choose c (pr₁ F) u)))
    → K
  branch c e q F (lift ₀ , x) = q (cast e x)
  branch c e q F (lift ₁ , x) = pr₂ F x

  record Extension
    {A : Set ℓ} (q : A → K)
    (F : Specification.Family (Specification.Decode (decode ℓ O) interpret))
    : Set (lsuc ℓ ⊔ κ) where
    field
      family :
        Specification.Family (Specification.Decode (decode ℓ O) interpret)
      left : A → carrier (view L family)
      right : carrier (view L F) → carrier (view L family)
      left-β :
        (λ x → index (view L family) (left x)) ＝ (λ x → interpret (q x))
      right-β :
        (λ x → index (view L family) (right x)) ＝ index (view L F)

  extend :
    (c : K) {A : Set ℓ} (e : decode ℓ O (interpret c) ＝ A) (q : A → K)
    (F : Specification.Family (Specification.Decode (decode ℓ O) interpret))
    → Extension q F
  extend c e q F =
    let named =
          sum L (Specification.Formers.two (formers ℓ O))
            (Specification.Closure.two L) (choose c (pr₁ F))
        collapse =
          cancel (ap (decode ℓ O) (pr₂ named))
            (λ x → interpret (branch c e q F x))
    in record
      { family =
          pr₁ named ,
          (λ x → branch c e q F (cast (ap (decode ℓ O) (pr₂ named)) x))
      ; left = λ x →
          cast (ap (decode ℓ O) (pr₂ named) ⁻¹) (lift ₀ , cast (e ⁻¹) x)
      ; right = λ x → cast (ap (decode ℓ O) (pr₂ named) ⁻¹) (lift ₁ , x)
      ; left-β =
          ap (λ h → λ x → h (lift ₀ , cast (e ⁻¹) x)) collapse
          ∙ cancel e (λ x → interpret (q x))
      ; right-β = ap (λ h → λ x → h (lift ₁ , x)) collapse
      }
