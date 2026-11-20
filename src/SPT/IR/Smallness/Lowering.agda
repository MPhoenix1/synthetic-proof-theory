{-# OPTIONS --safe --without-K #-}

module SPT.IR.Smallness.Lowering where

-- The smallness principle as lowerings of the raised fixed points. A
-- lowering of a description γ is a small type with maps both ways to the
-- raised fixed point μγ, the generated part of the identity algebra, that
-- keep the decodings (`Lowering`): a weak presentation of μγ by a small
-- type. Under extensionality for index families, a small algebra gives one
-- through its generated part (`lowered`, by Comparison), and a lowering
-- gives a small algebra: a small shape is carried to μγ by `up`, rolled
-- there, and brought down (`carry`, `raise`, `raise-law`). So the principle
-- is a lowering of every description (`lowerings`, `smallness`).

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)

open import SPT.IR.Action using (assemble)
open import SPT.IR.Algebra using
  (Algebra; Law; identity; identity-β)
import SPT.IR.Comparison as Comparison
open import SPT.IR.Description using
  (Desc; indexed; Shape; Mark)
import SPT.IR.Generated as Generated
open import SPT.IR.Restriction using (input)
open import SPT.IR.Smallness using (Smallness)

------------------------------------------------------------------------
-- Lowerings

-- Mathematical shape:
--
--   Σ (S : Set ℓ) (v : S → Set ℓ) (down : μγ → S) (up : S → μγ).
--     (Π u. v (down u) ＝ decode u) × (Π x. decode (up x) ＝ v x).
--
-- Nonclaim: the two maps are not asserted inverse.

record Lowering {ℓ : Level} (γ : Desc {s = ℓ} (Set ℓ)) : Set (lsuc ℓ) where
  field
    carrier : Set ℓ
    value : carrier → Set ℓ
    down : Generated.G (identity γ) → carrier
    up : carrier → Generated.G (identity γ)
    down-β :
      (u : Generated.G (identity γ))
      → value (down u) ＝ Generated.t (identity γ) u
    up-β : (x : carrier) → Generated.t (identity γ) (up x) ＝ value x

------------------------------------------------------------------------
-- A small algebra gives a lowering

-- Its generated part, with Comparison's two maps.

lowered :
  {ℓ : Level} {γ : Desc {s = ℓ} (Set ℓ)}
  → ((A : Set ℓ) → FunExt A (λ _ → Set ℓ))
  → (M : Algebra ℓ γ) → Law M → Lowering γ
lowered extensionality M law = record
  { carrier = Generated.G M
  ; value = Generated.t M
  ; down = Comparison.from M extensionality law
  ; up = Comparison.to M law
  ; down-β = Comparison.decode-from M extensionality law
  ; up-β = Comparison.decode M law
  }

------------------------------------------------------------------------
-- A lowering gives a small algebra

module _ {ℓ : Level} {γ : Desc {s = ℓ} (Set ℓ)} (lowering : Lowering γ) where

  open Lowering lowering using (carrier; value; down; up; down-β; up-β)

  -- A small shape is carried to a shape over μγ by `up` at every
  -- recursive input. A shape over μγ continues at the decodings of its
  -- inputs, the small shape at their values; extensionality identifies the
  -- two assignments before the continuation is read. The carried shape has
  -- the same output: Action's `assemble` at the points `up` gives.

  carry :
    ((A : Set ℓ) → FunExt A (λ _ → Set ℓ))
    → (S : Desc {s = ℓ} (Set ℓ)) (z : Shape S (indexed carrier value))
    → Σ (Shape S
          (indexed (Generated.G (identity γ)) (Generated.t (identity γ))))
        (λ y →
          Mark S
            (indexed (Generated.G (identity γ)) (Generated.t (identity γ)))
            y
            ＝ Mark S (indexed carrier value) z)
  carry extensionality S z =
    assemble extensionality (indexed carrier value)
      (indexed (Generated.G (identity γ)) (Generated.t (identity γ))) S z
      ( λ p →
          ( up (input S (indexed carrier value) z p)
          , up-β (input S (indexed carrier value) z p)))

  -- The operation carries a shape, rolls it in μγ, and comes down.

  raise : ((A : Set ℓ) → FunExt A (λ _ → Set ℓ)) → Algebra ℓ γ
  raise extensionality = record
    { K = carrier
    ; value = value
    ; operation = λ z →
        down (Generated.make (identity γ) (pr₁ (carry extensionality γ z)))
    }

  raise-law :
    (extensionality : (A : Set ℓ) → FunExt A (λ _ → Set ℓ))
    → Law (raise extensionality)
  raise-law extensionality z =
    down-β (Generated.make (identity γ) (pr₁ (carry extensionality γ z)))
    ∙ ( Generated.make-β (identity γ) (identity-β γ)
          (pr₁ (carry extensionality γ z))
      ∙ pr₂ (carry extensionality γ z))

------------------------------------------------------------------------
-- The principle as lowerings

-- Mathematical shape, under extensionality for index families:
--
--   Smallness ℓ ⇔ Π (γ : Desc (Set ℓ)). Lowering γ.

lowerings :
  {ℓ : Level} → ((A : Set ℓ) → FunExt A (λ _ → Set ℓ)) → Smallness ℓ
  → (γ : Desc {s = ℓ} (Set ℓ)) → Lowering γ
lowerings extensionality small γ =
  lowered extensionality (Smallness.algebra small γ) (Smallness.law small γ)

smallness :
  {ℓ : Level} → ((A : Set ℓ) → FunExt A (λ _ → Set ℓ))
  → ((γ : Desc {s = ℓ} (Set ℓ)) → Lowering γ) → Smallness ℓ
smallness extensionality lowering = record
  { algebra = λ γ → raise (lowering γ) extensionality
  ; law = λ γ → raise-law (lowering γ) extensionality
  }
