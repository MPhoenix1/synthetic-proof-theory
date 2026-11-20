{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Residence.Adjoined.Generation where

-- Generated Tarski names admit no Mahlo reflector when a decoded name
-- retracts onto the adjoined index. The seed operator names the lower
-- family and every adjoined type; induction on Form proves that every
-- closure names every name (reach). The tree decoding law then rules
-- out a reflection (unmahlo), under function extensionality.

open import SPT.Base
import SPT.Mahlo.Specification as Reflection
open import SPT.Mahlo.Decoding using (DecodingLaws)
open import SPT.Mahlo.Retraction using (Retract)
open import SPT.Mahlo.Generation using
  (Generated; unreflected; formed; branch-named)
open import SPT.Mahlo.Residence.Names using (identity-name)
open import SPT.Foundation.Sets.Uniqueness using
  (Extensionality; extensional)
open import SPT.Mahlo.Residence.Adjoined using
  (Form; emptyᶠ; unitᶠ; twoᶠ; naturalᶠ; productᶠ; sumᶠ; treeᶠ; identityᶠ;
   liftedᶠ; belowᶠ; adjoinedᶠ; Name; decode; empty; unit; two; natural;
   product; sum; tree; identity; lifted; below; adjoined; name-formers;
   name-decoding)

------------------------------------------------------------------------
-- The seed

-- For a name c whose type retracts onto the adjoined index, one family:
-- indexed by a point, the names below and the points of c's type, it
-- names below, each name below, and through the retraction each adjoined
-- name (seed-branch). The seed sends every family to it.

module _ {ℓ : Level} {L : Set ℓ} {D : L → Set ℓ} {I : Set (lsuc ℓ)}
  {E : I → Set ℓ} where

  -- The names below, and c.
  parts : Name L D I E → decode L D I E two → Name L D I E
  parts c (lift ₀) = below
  parts c (lift ₁) = c

  -- A point, and the parts.
  kinds : Name L D I E → decode L D I E two → Name L D I E
  kinds c (lift ₀) = unit
  kinds c (lift ₁) = sum two (parts c)

  seed-branch : (c : Name L D I E) → Retract (decode L D I E c) I →
    decode L D I E (sum two (kinds c)) → Name L D I E
  seed-branch c retraction (lift ₀ , _) = below
  seed-branch c retraction (lift ₁ , (lift ₀ , l)) = lifted l
  seed-branch c retraction (lift ₁ , (lift ₁ , t)) =
    adjoined (Retract.out retraction t)

  seed : (c : Name L D I E) → Retract (decode L D I E c) I →
    Reflection.Operator (decode L D I E)
  seed c retraction _ = sum two (kinds c) , seed-branch c retraction

------------------------------------------------------------------------
-- The seed's branches are named

-- At the family of the unit code with constant branches, the closure's
-- value of the seed is the seed family, so each of its branches is named.

module _ {ℓ : Level} {L : Set ℓ} {D : L → Set ℓ} {I : Set (lsuc ℓ)}
  {E : I → Set ℓ} (c : Name L D I E)
  (retraction : Retract (decode L D I E c) I) {X : Set ℓ}
  (K : Reflection.Closure (name-formers L D I E) (seed c retraction) X)
  where

  open Reflection.Closure K using (interpret; inner; inner-β)

  -- A family of the closure: the unit code, with constant branches.
  start : Reflection.Family (λ x → decode L D I E (interpret x))
  start = pr₁ (Reflection.Closure.unit K)
    , (λ _ → pr₁ (Reflection.Closure.unit K))

  seeded : (t : decode L D I E (sum two (kinds c))) →
    Reflection.Name interpret (seed-branch c retraction t)
  seeded = branch-named K (inner start) (sum two (kinds c))
    (seed-branch c retraction) (inner-β start)

------------------------------------------------------------------------
-- Every closure under the formers and the seed names every name

-- By induction on names: the formers through formed and identity-named;
-- below, the names below and the adjoined names as branches of the seed
-- (seeded), the adjoined ones along the retraction.

module _ (ext : Extensionality) {ℓ : Level} {L : Set ℓ} {D : L → Set ℓ}
  {I : Set (lsuc ℓ)} {E : I → Set ℓ} (c : Name L D I E)
  (retraction : Retract (decode L D I E c) I) {X : Set ℓ}
  (K : Reflection.Closure (name-formers L D I E) (seed c retraction) X)
  where

  open Reflection.Closure K using (interpret)

  -- By recursion on the formation of a name, read at the name (reach).
  reachᶠ :
    {Y : Set ℓ} (f : Form L D I E Y) →
    Reflection.Name interpret (Y , f)
  reachᶠ emptyᶠ = Reflection.Closure.empty K
  reachᶠ unitᶠ = Reflection.Closure.unit K
  reachᶠ twoᶠ = Reflection.Closure.two K
  reachᶠ naturalᶠ = Reflection.Closure.natural K
  reachᶠ (productᶠ {A} {B} fa fb) = formed (λ _ → extensional ext) K
    (Reflection.Formers.product (name-formers L D I E))
    (Reflection.Closure.product K) (A , fa) (λ x → B x , fb x)
    (reachᶠ fa) (λ y → reachᶠ (fb y))
  reachᶠ (sumᶠ {A} {B} fa fb) = formed (λ _ → extensional ext) K
    (Reflection.Formers.sum (name-formers L D I E))
    (Reflection.Closure.sum K) (A , fa) (λ x → B x , fb x)
    (reachᶠ fa) (λ y → reachᶠ (fb y))
  reachᶠ (treeᶠ {A} {B} fa fb) = formed (λ _ → extensional ext) K
    (Reflection.Formers.tree (name-formers L D I E))
    (Reflection.Closure.tree K) (A , fa) (λ x → B x , fb x)
    (reachᶠ fa) (λ y → reachᶠ (fb y))
  reachᶠ (identityᶠ {A} fa y₁ y₂) =
    identity-name (name-formers L D I E) (seed c retraction)
      K (reachᶠ fa) y₁ y₂
  reachᶠ (liftedᶠ l) = seeded c retraction K (lift ₁ , (lift ₀ , l))
  reachᶠ belowᶠ = seeded c retraction K (lift ₀ , lift ⋆)
  reachᶠ (adjoinedᶠ i) =
    pr₁ (seeded c retraction K
      (lift ₁ , (lift ₁ , Retract.into retraction i)))
    , pr₂ (seeded c retraction K
        (lift ₁ , (lift ₁ , Retract.into retraction i)))
      ∙ ap adjoined (Retract.out-into retraction i)

  reach : (a : Name L D I E) → Reflection.Name interpret a
  reach (_ , f) = reachᶠ f

------------------------------------------------------------------------
-- No reflection for the seed

-- The names are generated by the formers from the seed's values, so a
-- reflection for the seed would name its own carrier.

module _ {ℓ : Level} {L : Set ℓ} {D : L → Set ℓ} {I : Set (lsuc ℓ)}
  {E : I → Set ℓ} where

  generated : Extensionality → (c : Name L D I E)
    (retraction : Retract (decode L D I E c) I) →
    Generated (name-formers L D I E) (seed c retraction)
  generated ext c retraction K = reach ext c retraction K

  unmahlo : Extensionality → (c : Name L D I E) →
    Retract (decode L D I E c) I →
    ¬ Reflection.Mahlo (name-formers L D I E)
  unmahlo ext c retraction μ = unreflected (name-formers L D I E)
    (DecodingLaws.tree-β (name-decoding L D I E)) (seed c retraction)
    (generated ext c retraction)
    (Reflection.Mahlo.reflect μ (seed c retraction))

