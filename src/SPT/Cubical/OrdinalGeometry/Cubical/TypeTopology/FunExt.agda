{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.TypeTopology.FunExt where

-- TypeTopology's function extensionality (UF.FunExt.FunExt) from Cubical
-- function extensionality. The naive form, pointwise identification of
-- non-dependent functions, is a Cubical path between functions moved to
-- TypeTopology's identity type; TypeTopology's own theorem
-- naive-funext-gives-funext' upgrades it to the full form, happly an
-- equivalence for dependent functions. No equivalence is proved by hand.

open import Agda.Primitive using (Level; _⊔_)

open import SPT.Cubical.TypeTopology.UF.FunExt using (FunExt; naive-funext)
open import SPT.Cubical.TypeTopology.UF.FunExt-Properties
  using (naive-funext-gives-funext')

open import SPT.Cubical.OrdinalGeometry.Cubical.TypeTopology.Bridge using
  (path→＝; ＝→path)

-- Mathematical shape: f ∼ g → f ＝ g, for f g : X → Y.
naive : (ℓ ℓ′ : Level) → naive-funext ℓ ℓ′
naive ℓ ℓ′ h =
  path→＝ λ i x → ＝→path (h x) i

funext : FunExt
funext ℓ ℓ′ = naive-funext-gives-funext' (naive ℓ (ℓ ⊔ ℓ′)) (naive ℓ ℓ)
