{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.DS.Sorted.Smallness where

-- The smallness principle for outputs in Sort ℓ O: every description with
-- outputs in small types and values of O has a small algebra, with its law
-- (`Smallness`). It contains the principle for outputs in O alone. Such a
-- description is one with outputs on the right of Sort ℓ O whose δ nodes
-- also ask for their inputs to be on the right (`Right`, `extract`,
-- `embed`); a shape over a right-valued algebra is a shape of the
-- embedding (`down`, `down-mark`), so a small algebra of the embedding,
-- cut down to its right-valued codes, is a small algebra of the
-- description (`outputs`, `outputs-law`). No extensionality.

open import SPT.Base

open import SPT.IR.Algebra using (Algebra; Law)
open import SPT.IR.Description using
  (DS; Desc; ι; σ; δ; Indexed; indexed; Shape; Mark)
open import SPT.Mahlo.DS.Sorted using (Sort)

------------------------------------------------------------------------
-- The principle

record Smallness {κ : Level} (ℓ : Level) (O : Set κ) : Set (lsuc ℓ ⊔ κ)
  where
  field
    algebra : (γ : Desc {s = ℓ} (Sort ℓ O)) → Algebra ℓ γ
    law : (γ : Desc {s = ℓ} (Sort ℓ O)) → Law (algebra γ)

------------------------------------------------------------------------
-- Outputs in O alone

module _ {ℓ κ : Level} {O : Set κ} where

  -- A name on the right, and its value there.
  Right : Sort ℓ O → Set ℓ
  Right (inl A) = Lift ℓ 𝟘
  Right (inr o) = Lift ℓ 𝟙

  extract : (u : Sort ℓ O) → Right u → O
  extract (inl A) (lift ())
  extract (inr o) _ = o

  -- Outputs on the right; a δ node also asks for its inputs to be on the
  -- right, and continues at their values.
  embed : Desc {s = ℓ} O → Desc {s = ℓ} (Sort ℓ O)
  embed (ι o) = ι (inr o)
  embed (σ A H) = σ A (λ a → embed (H a))
  embed (δ A H) =
    δ A
      (λ X →
        σ ((a : A) → Right (X a))
          (λ r → embed (H (λ a → extract (X a) (r a)))))

  -- An extracted value along an identity to the right.
  extracted :
    (u : Sort ℓ O) (o : O) (e : u ＝ inr o)
    → extract u (transport Right (e ⁻¹) (lift ⋆)) ＝ o
  extracted u o refl = refl

module _
  {ℓ κ : Level} {O : Set κ} {γ : Desc {s = ℓ} O}
  (M : Algebra ℓ (embed γ))
  where

  open Algebra M using (K; value; operation)

  -- The codes of M whose names are on the right, read at their values.
  Codes : Set ℓ
  Codes = Σ K (λ k → Right (value k))

  read : Codes → O
  read c = extract (value (pr₁ c)) (pr₂ c)

  down :
    (S : Desc {s = ℓ} O) → Shape S (indexed Codes read)
    → Shape (embed S) (indexed K value)
  down (ι o) _ = lift ⋆
  down (σ A H) (a , z) = a , down (H a) z
  down (δ A H) (g , z) =
    (λ a → pr₁ (g a)) ,
    ((λ a → pr₂ (g a)) , down (H (λ a → read (g a))) z)

  down-mark :
    (S : Desc {s = ℓ} O) (z : Shape S (indexed Codes read))
    → Mark (embed S) (indexed K value) (down S z)
      ＝ inr (Mark S (indexed Codes read) z)
  down-mark (ι o) _ = refl
  down-mark (σ A H) (a , z) = down-mark (H a) z
  down-mark (δ A H) (g , z) = down-mark (H (λ a → read (g a))) z

  -- With the law of M, every shape lands on the right.
  landed :
    Law M → (z : Shape γ (indexed Codes read))
    → value (operation (down γ z)) ＝ inr (Mark γ (indexed Codes read) z)
  landed law z = law (down γ z) ∙ down-mark γ z

  outputs : Law M → Algebra ℓ γ
  outputs law = record
    { K = Codes
    ; value = read
    ; operation = λ z →
        operation (down γ z) ,
        transport Right (landed law z ⁻¹) (lift ⋆)
    }

  outputs-law : (law : Law M) → Law (outputs law)
  outputs-law law z =
    extracted (value (operation (down γ z)))
      (Mark γ (indexed Codes read) z) (landed law z)
