{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Residence.Fibered where

-- The obstructions to residence read off the pullback square of Families,
-- and what of a resident family's child is resident in the parent. A
-- resident family omits the code of its own W-type (`own-tree`), and the
-- squares' readings follow (`total-omits`, `restore-unsplit`,
-- `no-collection`, `families-unresident`, `operators-unresident`,
-- `no-return`). The child's families and operators are read off parent
-- fibers (`state-resident`, `actions-resident`); with
-- `operators-unresident` this is the size form of Dybjer–Setzer's Corollary
-- 5.6. No function extensionality is used.

open import SPT.Base
open import SPT.Foundation.Tree.W using (W)
open import SPT.Foundation.Tree.W using () renaming (sup to fork)
open import SPT.Mahlo.Decoding using (child-formers)
open import SPT.Mahlo.Retraction using
  (Retract; Similar; Unfolding; Retracts; inherited-retracts)
open import SPT.Mahlo.Specification using
  (Family; Operator; Formers; Closure; Reflection)
import SPT.Mahlo.Residence.Families as Families
import SPT.Mahlo.Residence.Reflection as Returned
open import SPT.Mahlo.Residence.Unreflected using
  (unfounded; no-retract)

------------------------------------------------------------------------
-- The code of a family's own W-type

module _ {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} where

  -- The family (c , j) names the W-type of its pullback, W (D c) (D ∘ j),
  -- as the parent code tree (c , j). A point x with j x that code makes
  -- the tree whose branches are all trees similar to one of its branches.
  own-tree :
      (Q : Formers C D)
    → Retracts Q
    → (c : C) (j : D c → C) (x : D c)
    → j x ＝ Formers.tree Q (c , j)
    → 𝟘
  own-tree Q R c j x named =
    let u = Retracts.tree R c j
        -- The tree whose branches are all trees over (D c , D ∘ j).
        whole : W (D c) (λ y → D (j y))
        whole = fork x (λ e → Unfolding.out u (transport D named e))
    in
    unfounded whole
      ( transport D (named ⁻¹) (Unfolding.into u whole))
      ( transport (λ v → Similar (Unfolding.out u v) whole)
          ( back-and-forth-transport D named (Unfolding.into u whole) ⁻¹)
          ( Unfolding.out-into u whole))

  -- Unreflected.no-retract: the section gives the point at tree (c , r).
  from-own-tree :
      (Q : Formers C D)
    → Retracts Q
    → (c : C) (r : D c → C) (s : C → D c)
    → ((a : C) → r (s a) ＝ a)
    → 𝟘
  from-own-tree Q R c r s rs =
    own-tree Q R c r (s (Formers.tree Q (c , r)))
      (rs (Formers.tree Q (c , r)))

------------------------------------------------------------------------
-- The pullback square and the operator square

module _ {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} where

  -- The top map of the pullback square misses the fiber over
  -- tree (r , j).
  total-omits :
      (Q : Formers C D)
    → Retracts Q
    → (r : C) (j : D r → C) (z : Σ (D r) (λ a → D (j a)))
    → pr₁ (Families.total D j z) ＝ Formers.tree Q (r , j)
    → 𝟘
  total-omits Q R r j z e =
    own-tree Q R r j (pr₁ z) (Families.square D j z ⁻¹ ∙ e)

  -- Restore, the vertical map of the operator square, has no section.
  restore-unsplit :
      (Q : Formers C D)
    → Retracts Q
    → (r : C) (j : D r → C)
      (σ : Family D → Family (λ a → D (j a)))
    → ((F : Family D) → Families.image D j (σ F) ＝ F)
    → 𝟘
  restore-unsplit Q R r j σ split =
    let t = Formers.tree Q (r , j)
        F = t , (λ _ → t)
    in own-tree Q R r j (pr₁ (σ F)) (ap pr₁ (split F))

  -- Among resident families and their maps, none receives the constant
  -- family at every code.
  no-collection :
      (Q : Formers C D)
    → Retracts Q
    → (t : Families.Resident D)
    → ((a : C) → Families.Map (λ (_ : D (Formers.unit Q)) → a)
         (Families.Resident.interpret t))
    → 𝟘
  no-collection Q R t m =
    let T = Formers.tree Q
              (Families.Resident.name t , Families.Resident.interpret t)
    in own-tree Q R (Families.Resident.name t)
         (Families.Resident.interpret t)
         (Families.Map.arrow (m T) (Retracts.point R))
         (Families.Map.triangle (m T) (Retracts.point R))

------------------------------------------------------------------------
-- The parent's families and operators

module _ {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} where

  -- No fiber retracts onto the parent's families.
  families-unresident :
      (Q : Formers C D)
    → Retracts Q
    → (c : C) (out : D c → Family D) (into : Family D → D c)
    → ((F : Family D) → out (into F) ＝ F)
    → 𝟘
  families-unresident Q R c out into back =
    let j = λ x → pr₁ (out x)
        t = Formers.tree Q (c , j)
        F = t , (λ _ → t)
    in own-tree Q R c j (into F) (ap pr₁ (back F))

  -- No fiber reads off the parent's operators, even pointwise.
  operators-unresident :
      (Q : Formers C D)
    → Retracts Q
    → (c : C) (decode : D c → Operator D) (encode : Operator D → D c)
    → ((Φ : Operator D) (F : Family D) → decode (encode Φ) F ＝ Φ F)
    → 𝟘
  operators-unresident Q R c decode encode back =
    families-unresident Q R c
      (λ x → decode x (c , (λ _ → c)))
      (λ F → encode (λ _ → F))
      (λ F → back (λ _ → F) (c , (λ _ → c)))

------------------------------------------------------------------------
-- Towers of resident composites

module _
  {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ}
  {Q : Formers C D} {Ψ : Operator D}
  where

  -- The composite of r with a reflection s in its child has as carrier a
  -- child code of r, whose decoding never retracts onto r's carrier.
  no-return :
      Retracts Q
    → (r : Reflection Q Ψ)
      (s : Reflection (child-formers (Reflection.closure r))
             (Closure.inner (Reflection.closure r)))
      (out : D (Reflection.carrier (Returned.compose r s))
             → D (Reflection.carrier r))
      (into : D (Reflection.carrier r)
              → D (Reflection.carrier (Returned.compose r s)))
    → ((a : D (Reflection.carrier r)) → out (into a) ＝ a)
    → 𝟘
  no-return R r s out into back =
    no-retract (child-formers (Reflection.closure r))
      (inherited-retracts R (Reflection.closure r))
      (Reflection.carrier s) out into back

------------------------------------------------------------------------
-- The child's families and operators in the parent

module _ {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} where

  -- The code of the maps from the decoding of j a into the carrier.
  arrows : (Q : Formers C D) (r : C) (j : D r → C) → D r → C
  arrows Q r j a = Formers.product Q (j a , (λ _ → r))

  -- The code of the child's families.
  states : (Q : Formers C D) (r : C) (j : D r → C) → C
  states Q r j = Formers.sum Q (r , arrows Q r j)

  -- The code of the operators on the child's families.
  dynamics : (Q : Formers C D) (r : C) (j : D r → C) → C
  dynamics Q r j =
    Formers.product Q (states Q r j , (λ _ → states Q r j))

  arrow-out :
      (Q : Formers C D) → Retracts Q → (r : C) (j : D r → C)
    → Σ (D r) (λ a → D (arrows Q r j a)) → Family (λ a → D (j a))
  arrow-out Q R r j (a , y) =
    a , Retract.out (Retracts.product R (j a) (λ _ → r)) y

  arrow-into :
      (Q : Formers C D) → Retracts Q → (r : C) (j : D r → C)
    → Family (λ a → D (j a)) → Σ (D r) (λ a → D (arrows Q r j a))
  arrow-into Q R r j (a , f) =
    a , Retract.into (Retracts.product R (j a) (λ _ → r)) f

  arrow-out-into :
      (Q : Formers C D) (R : Retracts Q) (r : C) (j : D r → C)
      (F : Family (λ a → D (j a)))
    → arrow-out Q R r j (arrow-into Q R r j F) ＝ F
  arrow-out-into Q R r j (a , f) =
    ap (λ g → a , g)
      (Retract.out-into (Retracts.product R (j a) (λ _ → r)) f)

  -- The child's families are a retract of the parent fiber at states.
  state-resident :
      (Q : Formers C D) → Retracts Q → (r : C) (j : D r → C)
    → Retract (D (states Q r j)) (Family (λ a → D (j a)))
  state-resident Q R r j =
    let pairs = Retracts.sum R r (arrows Q r j)
    in record
      { out = λ z → arrow-out Q R r j (Retract.out pairs z)
      ; into = λ F → Retract.into pairs (arrow-into Q R r j F)
      ; out-into = λ F →
          ap (arrow-out Q R r j)
            ( Retract.out-into pairs (arrow-into Q R r j F))
          ∙ arrow-out-into Q R r j F
      }

  -- Every operator on the child's families is read off a point of the
  -- parent fiber at dynamics, pointwise.
  actions-resident :
      (Q : Formers C D) → Retracts Q → (r : C) (j : D r → C)
    → Σ (D (dynamics Q r j) → Operator (λ a → D (j a)))
        (λ decode → Σ (Operator (λ a → D (j a)) → D (dynamics Q r j))
          (λ encode → (α : Operator (λ a → D (j a)))
            (X : Family (λ a → D (j a))) → decode (encode α) X ＝ α X))
  actions-resident Q R r j =
    let S = state-resident Q R r j
        P = Retracts.product R (states Q r j) (λ _ → states Q r j)
    in
    ( λ p X → Retract.out S (Retract.out P p (Retract.into S X)))
    , ( λ α → Retract.into P (λ z → Retract.into S (α (Retract.out S z))))
    , ( λ α X →
        ap (Retract.out S)
          ( ap (λ h → h (Retract.into S X))
              ( Retract.out-into P
                  ( λ z → Retract.into S (α (Retract.out S z)))))
        ∙ ( Retract.out-into S (α (Retract.out S (Retract.into S X)))
          ∙ ap α (Retract.out-into S X)))
