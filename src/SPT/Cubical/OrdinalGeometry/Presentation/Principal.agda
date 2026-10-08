{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Presentation.Principal where

-- Principal segments as presentations: the points below x form the
-- presentation with carrier Σ y. y < x.  Nested segments, the segments of
-- a successor P + 1, and principal segments addressed by a position of an
-- ω₁ geometry together with an optional point.

open import Agda.Primitive using (Level; lsuc)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Nat.Base using (zero)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import SPT.Cubical.Core.Equality.Isomorphism using (_≅_)
import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
import SPT.Cubical.OrdinalGeometry.Presentation.CountablyPresented as Geometry
import SPT.Cubical.OrdinalGeometry.Presentation.CountablyPresented.LowerCone
  as Cone
import SPT.Cubical.OrdinalGeometry.Presentation.Successor as Adjoin
import SPT.Cubical.OrdinalGeometry.Presentation.Map as Maps

private
  module Omega = Presented.ω₁.Geometry

-- The principal segment below x has carrier Σ y. y < x.  A segment of a
-- segment keeps both strict witnesses: `split` and `join` move the outer
-- one aside, with inverse laws by `refl`, while the equivalence
-- `restriction` with the segment below y forgets it.
module Segments {ℓ : Level} (P : Presented.CountableOrdinal𝒫 ℓ) where

  module P = Presented.CountableOrdinal𝒫 P
  module L = Cone (Geometry.from𝒫 P)

  lower : P.X → Presented.CountableOrdinal𝒫 ℓ
  lower = L.𝒫

  carrier-β : (x : P.X)
    → Presented.CountableOrdinal𝒫.X (lower x) ≡ Σ P.X (λ y → y P.< x)
  carrier-β x = refl

  inclusion : (x : P.X) → lower x Presented.≺𝒫 P
  inclusion x = record
    { to = proj₁
    ; to-≈ = λ q → q
    ; to-< = λ q → q
    ; reflects-< = λ q → q
    ; ceiling = x
    ; below = proj₂
    }

  module Inside (x y : P.X) (p : y P.< x) where

    private
      module Inner = Cone (Geometry.from𝒫 (lower x))

    principal : Presented.CountableOrdinal𝒫 ℓ
    principal = Inner.𝒫 (y , p)

    module N = Presented.CountableOrdinal𝒫 principal

    nested-β : N.X
      ≡ Σ (Σ P.X (λ z → z P.< x)) (λ u → proj₁ u P.< y)
    nested-β = refl

    Extra : L.T y → Set ℓ
    Extra u = proj₁ u P.< x

    split : N.X → Σ (L.T y) Extra
    split ((z , r) , q) = (z , q) , r

    join : Σ (L.T y) Extra → N.X
    join ((z , q) , r) = (z , r) , q

    exact : N.X ≅ Σ (L.T y) Extra
    exact = record
      { forward = split
      ; backward = join
      ; backward-forward = λ u → refl
      ; forward-backward = λ u → refl
      }

    down : N.X → L.T y
    down u = proj₁ (split u)

    up : L.T y → N.X
    up u = join (u , P.<-trans (proj₂ u) p)

    down-up : (u : L.T y) → down (up u) ≡ u
    down-up u = refl

    section : (λ u → down (up u)) ≡ (λ u → u)
    section = refl

    restriction : lower y Presented.≃𝒫 principal
    restriction = record
      { to = up
      ; from = down
      ; to-≈ = λ q → q
      ; from-≈ = λ q → q
      ; to-< = λ q → q
      ; from-< = λ q → q
      ; from-to-≈ = λ u → P.≈-refl (proj₁ u)
      ; to-from-≈ = λ u → P.≈-refl (proj₁ (proj₁ u))
      }

    point-β : (u : L.T y) → proj₁ (proj₁ (up u)) ≡ proj₁ u
    point-β u = refl

    witness-β : (u : L.T y) → proj₂ (up u) ≡ proj₂ u
    witness-β u = refl

    strict : lower y Presented.≺𝒫 lower x
    strict = record
      { to = λ u → proj₁ (up u)
      ; to-≈ = λ q → q
      ; to-< = λ q → q
      ; reflects-< = λ q → q
      ; ceiling = y , p
      ; below = proj₂
      }

-- In P + 1, the predecessors of the new top are exactly the points of P,
-- and the predecessors of an old point x are those of x in P, with their
-- strict witnesses.  Both inverse laws hold by `refl`, which is stronger
-- than the corresponding equivalences of presentations.
module Successor {ℓ : Level} (P : Presented.CountableOrdinal𝒫 ℓ) where

  module P = Presented.CountableOrdinal𝒫 P
  module S = Presented.Diagonal.Successor
    (Adjoin.constant P) zero
  module Original = Segments P

  open Maps.Successor P public using (next)

  module L = Segments next

  point : P.X → Presented.CountableOrdinal𝒫.X next
  point = S.point

  top : Presented.CountableOrdinal𝒫.X next
  top = S.top

  module Top where

    module N = Presented.CountableOrdinal𝒫 (L.lower top)

    to : P.X → N.X
    to x = point x , S.point<top

    from : N.X → P.X
    from (S.point x , S.point<top) = x

    exact : P.X ≅ N.X
    exact = record
      { forward = to
      ; backward = from
      ; backward-forward = λ x → refl
      ; forward-backward = λ { (S.point x , S.point<top) → refl }
      }

    private
      from-≈ : ∀ {u v} → u N.≈ v → from u P.≈ from v
      from-≈ {S.point x , S.point<top} {S.point y , S.point<top}
        (S.point≈ q) = q

      from-< : ∀ {u v} → u N.< v → from u P.< from v
      from-< {S.point x , S.point<top} {S.point y , S.point<top}
        (S.point< q) = q

    presentation : P Presented.≃𝒫 L.lower top
    presentation = record
      { to = to
      ; from = from
      ; to-≈ = S.point≈
      ; from-≈ = from-≈
      ; to-< = S.point<
      ; from-< = from-<
      ; from-to-≈ = P.≈-refl
      ; to-from-≈ = λ { (S.point x , S.point<top) → S.point≈ (P.≈-refl x) }
      }

  module Below (x : P.X) where

    module D = Presented.CountableOrdinal𝒫 (Original.lower x)
    module N = Presented.CountableOrdinal𝒫 (L.lower (point x))

    to : D.X → N.X
    to u = point (proj₁ u) , S.point< (proj₂ u)

    from : N.X → D.X
    from (S.point y , S.point< q) = y , q

    exact : D.X ≅ N.X
    exact = record
      { forward = to
      ; backward = from
      ; backward-forward = λ u → refl
      ; forward-backward = λ { (S.point y , S.point< q) → refl }
      }

    private
      from-≈ : ∀ {u v} → u N.≈ v → from u D.≈ from v
      from-≈ {S.point y , S.point< p} {S.point z , S.point< r} (S.point≈ q) = q

      from-< : ∀ {u v} → u N.< v → from u D.< from v
      from-< {S.point y , S.point< p} {S.point z , S.point< r} (S.point< q) = q

    presentation : Original.lower x Presented.≃𝒫 L.lower (point x)
    presentation = record
      { to = to
      ; from = from
      ; to-≈ = S.point≈
      ; from-≈ = from-≈
      ; to-< = S.point<
      ; from-< = from-<
      ; from-to-≈ = λ u → P.≈-refl (proj₁ u)
      ; to-from-≈ = λ { (S.point y , S.point< q) → S.point≈ (P.≈-refl y) }
      }

    point-β : (u : D.X) → proj₁ (to u) ≡ point (proj₁ u)
    point-β u = refl

    witness-β : (u : D.X) → proj₂ (from (to u)) ≡ proj₂ u
    witness-β u = refl

------------------------------------------------------------------------
-- Principal segments addressed in an ω₁ geometry

-- An address is a position of the geometry with an optional point of its
-- presentation: the whole domain, or the principal segment below that
-- point. The successor's top names every presentation, and below an old
-- point the old predecessors return with their strict witnesses.
module Address {ℓ : Level} (geometry : Presented.𝒫ω₁𝒢 ℓ) where

  Ordinal : Set (lsuc ℓ)
  Ordinal = Omega.Position geometry

  Carrier : Ordinal → Set ℓ
  Carrier α = Presented.CountableOrdinal𝒫.X (proj₁ α)

  Point : Set (lsuc ℓ)
  Point = Σ Ordinal (λ α → Maybe (Carrier α))

  Pred : Point → Set ℓ
  Pred (α , nothing) = Carrier α
  Pred (α , just x) = Σ (Carrier α) λ y →
    Presented.CountableOrdinal𝒫._<_ (proj₁ α) y x

  domain : Point → Presented.CountableOrdinal𝒫 ℓ
  domain (α , nothing) = proj₁ α
  domain (α , just x) = Segments.lower (proj₁ α) x

  carrier-β : (j : Point)
    → Presented.CountableOrdinal𝒫.X (domain j) ≡ Pred j
  carrier-β (α , nothing) = refl
  carrier-β (α , just x) = refl

  inclusion : (α : Ordinal) (x : Carrier α)
    → domain (α , just x) Presented.≺𝒫 domain (α , nothing)
  inclusion α = Segments.inclusion (proj₁ α)

  -- Nested restriction at a position keeps the inner strict witness and
  -- returns the outer one separately.
  module Inside (α : Ordinal) (x y : Carrier α)
    (p : Presented.CountableOrdinal𝒫._<_ (proj₁ α) y x) where

    private
      module Nested = Segments.Inside (proj₁ α) x y p

    address : Point
    address =
      Omega.position geometry (Segments.lower (proj₁ α) x) , just (y , p)

    restriction : domain (α , just y) Presented.≃𝒫 domain address
    restriction = Nested.restriction

    exact : Pred address
      ≅ Σ (Pred (α , just y)) λ u →
          Presented.CountableOrdinal𝒫._<_ (proj₁ α) (proj₁ u) x
    exact = Nested.exact

  -- The successor's top names a supplied presentation as a principal
  -- segment, including when its carrier is empty.
  module Name (P : Presented.CountableOrdinal𝒫 ℓ) where

    module P = Presented.CountableOrdinal𝒫 P

    private
      module Next = Successor P

    ordinal : Ordinal
    ordinal = Omega.position geometry Next.next

    top : Carrier ordinal
    top = Next.top

    point : Point
    point = ordinal , just top

    presentation : P Presented.≃𝒫 domain point
    presentation = Next.Top.presentation

    exact : P.X ≅ Pred point
    exact = Next.Top.exact

    module Below (x : P.X) where

      private
        module Old = Next.Below x

      address : Point
      address = ordinal , just (Next.point x)

      restriction : Segments.lower P x Presented.≃𝒫 domain address
      restriction = Old.presentation

      predecessors : Σ P.X (λ y → y P.< x) ≅ Pred address
      predecessors = Old.exact

  named : (P : Presented.CountableOrdinal𝒫 ℓ)
    → Σ Ordinal λ α → Σ (Carrier α) λ x →
        P Presented.≃𝒫 domain (α , just x)
  named P = Name.ordinal P , Name.top P , Name.presentation P
