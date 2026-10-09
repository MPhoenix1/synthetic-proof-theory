{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.TypeTopology.HeightLoss where

-- What rank forgets, in TypeTopology's terms.  rank′(t) = toOrdinal (rank t)
-- reads the rank of a height as a TypeTopology ordinal.  Its fiber over
-- toOrdinal (α + 1) contains the merely inhabited types as a split
-- retract, as in Fiber.Height: toOrdinal keeps the carrier, so recovery
-- still finds a point in the rank of the root.  So that fiber has no
-- finite h-level, formed with paths or with TypeTopology's Σ and ＝, nor
-- a finite h-level in TypeTopology's hierarchy, and rank′ is not an
-- embedding, in either sense.

open import Agda.Primitive using (Level; lsuc)
open import Data.Empty using (⊥)
import Data.Nat.Base as Nat

import Cubical.Foundations.Equiv as Equiv
import Cubical.Foundations.HLevels as HLevels
import Cubical.Foundations.Prelude as Cubical
import Cubical.Functions.Embedding as Embedding
import Cubical.Relation.Binary.Order.Woset.Base as Woset

import SPT.Cubical.Core.Generator.Tree as Tree
open import SPT.Cubical.OrdinalGeometry.Height.Ordinals using (Height)
open import SPT.Cubical.OrdinalGeometry.Cubical.Height.Rank using (rank)
open import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Ordinals using
  (successor; top)
open import SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Height using
  (InhabitedType; type-path; inhabited; copies; copies-rank; leaf)
open import SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Height.Unbounded
  using (base; not-finite-hlevel)
open import SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Higher.IteratedLoop
  using (PointedSplitEmbedding; pointed-split-embedding)
import SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Higher.SplitEmbedding
  as Split
open import SPT.Cubical.OrdinalGeometry.Cubical.TypeTopology.Bridge using
  (toOrdinal; path→＝; ＝→path; path→＝→path)
open import SPT.Cubical.OrdinalGeometry.Cubical.TypeTopology.Univalence
  using (univalence)
open import
  SPT.Cubical.OrdinalGeometry.Cubical.TypeTopology.IdentityFiberLoss
  using (TT-hlevel→hlevel)

import SPT.Cubical.TypeTopology.MLTT.Sigma-Type as TypeTopologySigma
import SPT.Cubical.TypeTopology.Notation.General as TypeTopologyNotation
import SPT.Cubical.TypeTopology.Ordinals.Type as TypeTopologyOrdinal
import SPT.Cubical.TypeTopology.UF.Embeddings as TypeTopologyEmbedding
open import SPT.Cubical.TypeTopology.UF.HLevels univalence using
  (_is-of-hlevel_)

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- The rank as a TypeTopology ordinal

-- rank′(t) = toOrdinal (rank t).
rank′ : Height ℓ → TypeTopologyOrdinal.Ordinal ℓ
rank′ t = toOrdinal (rank t)

-- RankFiber(α) = Σ t. rank′(t) = toOrdinal (α + 1), with paths.
RankFiber : Woset.Woset ℓ ℓ → Set (lsuc ℓ)
RankFiber α = Equiv.fiber rank′ (toOrdinal (successor α))

private
  retain : (α : Woset.Woset ℓ ℓ) → InhabitedType ℓ → RankFiber α
  retain α (Cubical._,_ A m) =
    copies A α Cubical., Cubical.cong toOrdinal (copies-rank A α m)

  -- The carrier of toOrdinal W is the carrier of W, so the path carries
  -- the top point of α + 1 back to the rank of the root.
  recover : (α : Woset.Woset ℓ ℓ) → RankFiber α → InhabitedType ℓ
  recover α (Cubical._,_ (Tree.hole ()) p)
  recover α (Cubical._,_ (Tree.node A f) p) =
    A Cubical.,
    inhabited A f
      (Cubical.transport
        (Cubical.cong TypeTopologySigma.Σ.pr₁ (Cubical.sym p)) (top α))

  recover-retain : (α : Woset.Woset ℓ ℓ) (X : InhabitedType ℓ)
    → recover α (retain α X) Cubical.≡ X
  recover-retain α X = type-path Cubical.refl

-- (InhabitedType ℓ, base) ◁∗ (RankFiber α, retain α base).
rankFiber-embedding : (α : Woset.Woset ℓ ℓ)
  → PointedSplitEmbedding (InhabitedType ℓ) base
      (RankFiber α) (retain α base)
rankFiber-embedding α =
  pointed-split-embedding
    (Split.split-embedding (retain α) (recover α) (recover-retain α))
    Cubical.refl

rankFiber-not-finite-hlevel : (α : Woset.Woset ℓ ℓ) (n : Nat.ℕ)
  → HLevels.isOfHLevel n (RankFiber α) → ⊥
rankFiber-not-finite-hlevel α = not-finite-hlevel (rankFiber-embedding α)

rank′-not-embedding : Embedding.isEmbedding (rank′ {ℓ}) → ⊥
rank′-not-embedding {ℓ} rank′-embedding =
  rankFiber-not-finite-hlevel (rank (leaf {ℓ})) 1
    (Embedding.isEmbedding→hasPropFibers rank′-embedding
      (toOrdinal (successor (rank leaf))))

------------------------------------------------------------------------
-- TypeTopology's fibers

-- RankIdentityFiber(α) = Σ t. rank′(t) ＝ toOrdinal (α + 1), with
-- TypeTopology's Σ and ＝.
RankIdentityFiber : Woset.Woset ℓ ℓ → Set (lsuc ℓ)
RankIdentityFiber α =
  TypeTopologyNotation.fiber rank′ (toOrdinal (successor α))

private
  path→identity : (α : Woset.Woset ℓ ℓ)
    → RankFiber α → RankIdentityFiber α
  path→identity α (Cubical._,_ t p) = TypeTopologySigma._,_ t (path→＝ p)

  identity→path : (α : Woset.Woset ℓ ℓ)
    → RankIdentityFiber α → RankFiber α
  identity→path α (TypeTopologySigma._,_ t p) = t Cubical., ＝→path p

  identity-retraction : (α : Woset.Woset ℓ ℓ) (x : RankFiber α)
    → identity→path α (path→identity α x) Cubical.≡ x
  identity-retraction α (Cubical._,_ t p) =
    Cubical.cong (t Cubical.,_) (path→＝→path p)

rankIdentityFiber-not-finite-hlevel : (α : Woset.Woset ℓ ℓ) (n : Nat.ℕ)
  → HLevels.isOfHLevel n (RankIdentityFiber α) → ⊥
rankIdentityFiber-not-finite-hlevel α n hlevel =
  rankFiber-not-finite-hlevel α n
    (HLevels.isOfHLevelRetract n
      (path→identity α) (identity→path α) (identity-retraction α) hlevel)

-- TypeTopology's h-level n is Cubical's n + 1.
rankIdentityFiber-not-finite-TT-hlevel : (α : Woset.Woset ℓ ℓ)
  (n : Nat.ℕ) → RankIdentityFiber α is-of-hlevel n → ⊥
rankIdentityFiber-not-finite-TT-hlevel α n hlevel =
  rankIdentityFiber-not-finite-hlevel α (Nat.suc n)
    (TT-hlevel→hlevel univalence n (RankIdentityFiber α) hlevel)

rank′-not-TT-embedding :
  TypeTopologyEmbedding.is-embedding (rank′ {ℓ}) → ⊥
rank′-not-TT-embedding {ℓ} rank′-embedding =
  rankIdentityFiber-not-finite-hlevel (rank (leaf {ℓ})) 1
    λ x y →
      ＝→path (rank′-embedding (toOrdinal (successor (rank leaf))) x y)
