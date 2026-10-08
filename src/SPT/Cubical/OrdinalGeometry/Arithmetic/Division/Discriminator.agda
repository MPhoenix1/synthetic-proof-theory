{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Arithmetic.Division.Discriminator where

-- Division without a placement. Suppose every P had a division by every
-- inhabited D. Then an arbitrary Boolean stream s is decided by dividing
-- possible s, which has a point exactly when s hits true, by 2. The
-- remainder is a proper segment of 2. When its ceiling is the top, the
-- remainder has a point, and so does possible s. When its ceiling is the
-- old point, the remainder is empty, so possible s ≃ 2 · Q. Every block
-- of 2 · Q holds two points, one below the other: below (v, top) lies
-- ∂(v, top) ≃ 2 · ∂v + ∂top (doubled). But possible s has no two
-- comparable points, so s never hits (division). The placement that
-- Division asks for cannot be dropped: divisions of arbitrary
-- presentations give LPO.

open import Agda.Primitive using (lzero)
open import Data.Bool using (Bool; false)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
import SPT.Cubical.OrdinalGeometry.Presentation.Map as Maps
open import SPT.Cubical.OrdinalGeometry.Presentation.Sum using (_+_)
import SPT.Cubical.OrdinalGeometry.Presentation.Normalization as Normal
import SPT.Cubical.OrdinalGeometry.Presentation.Limit.Discriminator as Stream
open Stream using (two; bottom)
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Multiplication using
  (_·_; point; view)
import SPT.Cubical.OrdinalGeometry.Arithmetic.Cone as Cone
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Division using (Division)

private
  -- The entries of a successor presentation: old points and the top.
  module Entry = Presented.Diagonal.Successor

  -- Every block of 2 · Q holds two points, one below the other: below
  -- (v, top) lies its domain 2 · ∂v + ∂top, and ∂top has the old point.
  doubled : (Q : 𝒫 lzero) (v : Normal.Point Q)
    → Σ (𝒫.X (two · Q)) (λ y →
        𝒫._<_ (two · Q) y (point two Q v (Normal.class two Entry.top)))
  doubled Q v = Presented._≃𝒫_.to
    (Cone.product two Q v (Normal.class two Entry.top))
    (inj₂ (Entry.point tt , 𝒫.<-respʳ-≈ two
      (𝒫.≈-sym two (Normal.representative-class two Entry.top))
      Entry.point<top))

  -- The ceiling of the remainder decides s.
  decide : (s : ℕ → Bool) → Division (Stream.possible s) two
    → Stream.Hit s ⊎ ((n : ℕ) → s n ≡ false)
  decide s d = at B.ceiling B.below (Maps.Segment.covers (Division.below d))
    where
    Q : 𝒫 lzero
    Q = Division.quotient d

    R : 𝒫 lzero
    R = Division.remainder d

    module E = Presented._≃𝒫_ (Division.equation d)
    module B = Presented._≺𝒫_ (Maps.Segment.bound (Division.below d))

    at : (c : 𝒫.X two) → ((x : 𝒫.X R) → 𝒫._<_ two (B.to x) c)
      → ((y : 𝒫.X two) → 𝒫._<_ two y c
          → Σ (𝒫.X R) (λ x → 𝒫._≈_ two (B.to x) y))
      → Stream.Hit s ⊎ ((n : ℕ) → s n ≡ false)
    at Entry.top _ covers =
      inj₁ (E.to (inj₂ (proj₁ (covers (Entry.point tt) Entry.point<top))))
    at (Entry.point _) below _ = inj₂ (Stream.absent s λ h → split (E.from h))
      where
      -- A point of the empty remainder is impossible, and a point of the
      -- multiple gives two comparable points of possible s.
      split : 𝒫.X ((two · Q) + R) → ⊥
      split (inj₂ x) = bottom (below x)
      split (inj₁ u) = E.to-<
        {x = inj₁ (proj₁ (doubled Q (proj₁ (view two Q u))))}
        {y = inj₁ (point two Q (proj₁ (view two Q u))
          (Normal.class two Entry.top))}
        (proj₂ (doubled Q (proj₁ (view two Q u))))

-- Mathematical shape: (Π P D. D inhabited → Division P D) → LPO.
division : ((P D : 𝒫 lzero) → 𝒫.X D → Division P D) → Stream.LPO
division divide s =
  decide s (divide (Stream.possible s) two Entry.top)
