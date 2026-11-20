{-# OPTIONS --safe --without-K #-}

module SPT.IR.Comparison.Discriminator where

-- The raised fixed point and the comparison have content. μγ decodes by
-- refl at a closed description: for the description whose leaf is 𝟚 and
-- whose step sends a decoded input X to X → X, the first codes decode to 𝟚,
-- 𝟚 → 𝟚 and (𝟚 → 𝟚) → (𝟚 → 𝟚) (`decode-leaf`, `decode-next`,
-- `decode-first`, `decode-second`). And `to` keeps recursive depth: for a
-- description with a leaf and a unary step whose outputs are all the unit
-- type, the one-point algebra satisfies the law, so its carrier forgets all
-- depth, and still the image of the second step over the leaf has depth two
-- in μγ (`depth`, `two`).

open import SPT.Base
import SPT.Foundation.Tree.Fold as Fold

open import SPT.IR.Algebra using (Algebra; Law; identity)
import SPT.IR.Comparison as Comparison
open import SPT.IR.Description using (Desc; ι; σ; δ)
import SPT.IR.Generated as Generated

------------------------------------------------------------------------
-- Decoding in the raised fixed point

-- ₀ ↦ the leaf 𝟚; ₁ ↦ one recursive input X and the output X → X.

arrows : 𝟚 → Desc {s = lzero} Set
arrows ₀ = ι 𝟚
arrows ₁ = δ 𝟙 (λ q → ι (q ⋆ → q ⋆))

arrow-self : Desc {s = lzero} Set
arrow-self = σ 𝟚 arrows

leaf : Generated.G (identity arrow-self)
leaf = Generated.make (identity arrow-self) (₀ , lift ⋆)

next : Generated.G (identity arrow-self) → Generated.G (identity arrow-self)
next u = Generated.make (identity arrow-self) (₁ , ((λ _ → u) , lift ⋆))

decode-leaf : Generated.t (identity arrow-self) leaf ＝ 𝟚
decode-leaf = refl

decode-next :
  (u : Generated.G (identity arrow-self))
  → Generated.t (identity arrow-self) (next u)
    ＝ (Generated.t (identity arrow-self) u
      → Generated.t (identity arrow-self) u)
decode-next u = refl

decode-first : Generated.t (identity arrow-self) (next leaf) ＝ (𝟚 → 𝟚)
decode-first = refl

decode-second :
  Generated.t (identity arrow-self) (next (next leaf))
  ＝ ((𝟚 → 𝟚) → (𝟚 → 𝟚))
decode-second = refl

------------------------------------------------------------------------
-- The comparison keeps recursive depth

-- ₀ ↦ a leaf; ₁ ↦ one recursive input. Every output is the unit type.

steps : 𝟚 → Desc {s = lzero} Set
steps ₀ = ι 𝟙
steps ₁ = δ 𝟙 (λ _ → ι 𝟙)

counter : Desc {s = lzero} Set
counter = σ 𝟚 steps

-- The one-point algebra.

one-point : Algebra lzero counter
one-point = record
  { K = 𝟙
  ; value = λ _ → 𝟙
  ; operation = λ _ → ⋆
  }

one-point-law : Law one-point
one-point-law (₀ , _) = refl
one-point-law (₁ , _) = refl

seed : Generated.G one-point
seed = Generated.make one-point (₀ , lift ⋆)

grow : Generated.G one-point → Generated.G one-point
grow g = Generated.make one-point (₁ , ((λ _ → g) , lift ⋆))

-- The depth of a raised code: zero at a leaf, and one more than its input
-- at a step.

depth-node :
  {e : Set} (o : Generated.Operation (identity counter) e)
  → ((p : Generated.positions (identity counter) o) → ℕ) → ℕ
depth-node (Generated.apply (₀ , _)) children = zero
depth-node (Generated.apply (₁ , _)) children = suc (children (inl ⋆))

depth-algebra :
  Fold.Algebra (Generated.signature (identity counter)) (λ _ → 𝟘)
    (λ _ → ℕ)
depth-algebra = record
  { on-hole = 𝟘-elim
  ; on-node = depth-node
  }

depth : Generated.G (identity counter) → ℕ
depth u = Fold.fold depth-algebra (pr₂ u)

two :
  depth (Comparison.to one-point one-point-law (grow (grow seed)))
  ＝ suc (suc zero)
two = refl
