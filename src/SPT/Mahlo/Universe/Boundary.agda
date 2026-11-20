{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Universe.Boundary where

-- Retained boundaries and their fills, by homogeneous indexed
-- induction–recursion over an index type, a seed family and the fills of
-- the seeds. A boundary is a seed, or a fan: a boundary with a boundary at
-- every fill of it (`RetainedBoundary`: `retained-seed`,
-- `filler-indexed-fan`). Its fills are decoded together with it
-- (`RetainedFill`): a seed's are its given fills, and a fan's are the
-- complete fans of child fills, one at every fill of the boundary, both by
-- refl:
--
--   RetainedFill (retained-seed s) = SeedFill s,
--   RetainedFill (filler-indexed-fan b k) = Π (p : RetainedFill b).
--                                             RetainedFill (k p).
--
-- Mahlo.Universe codes these boundaries and their fills inside its own
-- induction–recursive definition (`boundary`, `filling`).

open import SPT.Base

------------------------------------------------------------------------
-- Boundaries and their fills

-- A fan's positions are not fixed before its boundary is decoded: they
-- are the fills of a boundary generated in the same definition.

mutual

  data RetainedBoundary
      {ℓ : Level}
      (Index : Set ℓ)
      (Seed : Index → Set ℓ)
      (SeedFill : {i : Index} → Seed i → Set ℓ)
      : Index → Set ℓ where

    retained-seed :
        {i : Index}
      → (seed : Seed i)
      → RetainedBoundary Index Seed SeedFill i

    filler-indexed-fan :
        {i : Index}
      → (boundary : RetainedBoundary Index Seed SeedFill i)
      → (branch :
          RetainedFill boundary
          → RetainedBoundary Index Seed SeedFill i)
      → RetainedBoundary Index Seed SeedFill i

  RetainedFill :
      {ℓ : Level}
      {Index : Set ℓ}
      {Seed : Index → Set ℓ}
      {SeedFill : {i : Index} → Seed i → Set ℓ}
      {i : Index}
    → RetainedBoundary Index Seed SeedFill i
    → Set ℓ
  RetainedFill {SeedFill = SeedFill} (retained-seed seed) =
    SeedFill seed
  RetainedFill (filler-indexed-fan boundary branch) =
    (position : RetainedFill boundary) →
      RetainedFill (branch position)

------------------------------------------------------------------------
-- The decoding laws

module _
  {ℓ : Level} {Index : Set ℓ} {Seed : Index → Set ℓ}
  {SeedFill : {i : Index} → Seed i → Set ℓ} {i : Index}
  where

  retained-seed-fill-computes :
      (seed : Seed i)
    → RetainedFill
        ( retained-seed
            {Index = Index} {Seed = Seed} {SeedFill = SeedFill} seed)
      ＝ SeedFill seed
  retained-seed-fill-computes seed = refl

  filler-indexed-fan-fill-computes :
      (boundary : RetainedBoundary Index Seed SeedFill i)
      (branch :
        RetainedFill boundary
        → RetainedBoundary Index Seed SeedFill i)
    → RetainedFill (filler-indexed-fan boundary branch)
      ＝ ((position : RetainedFill boundary) →
            RetainedFill (branch position))
  filler-indexed-fan-fill-computes boundary branch = refl
