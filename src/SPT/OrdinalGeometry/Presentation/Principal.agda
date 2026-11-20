{-# OPTIONS --safe --without-K #-}

module SPT.OrdinalGeometry.Presentation.Principal where

-- Principal presentations: the predecessors Σ y. y < x of a point x as a
-- presentation (`For.lower`), included below x (`For.inclusion`), and read
-- inside the predecessors of a larger point (`For.Inside`: `restriction` and
-- `strict`). The predecessors of the new top of P + 1 are P
-- (`Successor.Top`), and those of an old point are its old predecessors
-- (`Successor.Old`). These inverse laws on the carriers strengthen the
-- corresponding presentation equivalences and use no uniqueness of P's
-- witnesses.

open import SPT.Base hiding (lower)
open import SPT.Foundation.Isomorphisms using (_≅_)
import SPT.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (Countable-Ordinal𝒫 to 𝒫)
open import SPT.OrdinalGeometry.Presentation.CountablyPresented using
  (from𝒫)
import SPT.OrdinalGeometry.Presentation.CountablyPresented.LowerCone
  as LowerCone
open import SPT.OrdinalGeometry.Presentation.Successor using
  (constant-presentation-family; presentation-successor)

------------------------------------------------------------------------
-- Principal presentations of one presentation

-- The principal presentation has the literal carrier Σ y. y < x. Nested
-- restriction keeps the endpoint and the inner strict witness. Its
-- presentation equivalence forgets one outer witness; `split` keeps that
-- witness apart, with both exact inverse laws.
module For {ℓ : Level} (P : 𝒫 ℓ) where

  open Presented.Countable-Ordinal𝒫 P

  lower : X → 𝒫 ℓ
  lower = LowerCone.𝒫 (from𝒫 P)

  carrier-β : (x : X) → 𝒫.X (lower x) ＝ Σ X (λ y → y < x)
  carrier-β x = refl

  inclusion : (x : X) → lower x Presented.≺𝒫 P
  inclusion x = record
    { to = pr₁
    ; to-≈ = λ q → q
    ; to-< = λ q → q
    ; reflects-< = λ q → q
    ; ceiling = x
    ; below = pr₂
    }

  module Inside (x y : X) (p : y < x) where

    principal : 𝒫 ℓ
    principal = LowerCone.𝒫 (from𝒫 (lower x)) (y , p)

    nested-β : 𝒫.X principal ＝ Σ (Σ X (λ z → z < x)) (λ u → pr₁ u < y)
    nested-β = refl

    Extra : LowerCone.Cone (from𝒫 P) y → Set ℓ
    Extra u = pr₁ u < x

    split : 𝒫.X principal → Σ (LowerCone.Cone (from𝒫 P) y) Extra
    split ((z , r) , q) = (z , q) , r

    join : Σ (LowerCone.Cone (from𝒫 P) y) Extra → 𝒫.X principal
    join ((z , q) , r) = (z , r) , q

    exact : 𝒫.X principal ≅ Σ (LowerCone.Cone (from𝒫 P) y) Extra
    exact = record
      { forward = split
      ; backward = join
      ; backward-forward = λ u → refl
      ; forward-backward = λ u → refl
      }

    down : 𝒫.X principal → LowerCone.Cone (from𝒫 P) y
    down u = pr₁ (split u)

    up : LowerCone.Cone (from𝒫 P) y → 𝒫.X principal
    up u = join (u , <-trans (pr₂ u) p)

    down-up : (u : LowerCone.Cone (from𝒫 P) y) → down (up u) ＝ u
    down-up u = refl

    section : (λ u → down (up u)) ＝ (λ u → u)
    section = refl

    restriction : lower y Presented.≃𝒫 principal
    restriction = record
      { to = up
      ; from = down
      ; to-≈ = λ q → q
      ; from-≈ = λ q → q
      ; to-< = λ q → q
      ; from-< = λ q → q
      ; from-to-≈ = λ u → ≈-refl (pr₁ u)
      ; to-from-≈ = λ u → ≈-refl (pr₁ (pr₁ u))
      }

    point-β : (u : LowerCone.Cone (from𝒫 P) y) → pr₁ (pr₁ (up u)) ＝ pr₁ u
    point-β u = refl

    witness-β : (u : LowerCone.Cone (from𝒫 P) y) → pr₂ (up u) ＝ pr₂ u
    witness-β u = refl

    strict : lower y Presented.≺𝒫 lower x
    strict = record
      { to = λ u → pr₁ (up u)
      ; to-≈ = λ q → q
      ; to-< = λ q → q
      ; reflects-< = λ q → q
      ; ceiling = y , p
      ; below = pr₂
      }

------------------------------------------------------------------------
-- Principal presentations of the successor

-- The new top has exactly the old carrier as predecessors. Below an old
-- point, both the old endpoint and its strict witness are recovered
-- exactly.
module Successor {ℓ : Level} (P : 𝒫 ℓ) where

  next : 𝒫 ℓ
  next = presentation-successor P

  point : 𝒫.X P → 𝒫.X next
  point = Presented.Diagonal.Successor.point

  top : 𝒫.X next
  top = Presented.Diagonal.Successor.top

  strict : P Presented.≺𝒫 next
  strict = record
    { to = point
    ; to-≈ = Presented.Diagonal.Successor.point≈
    ; to-< = Presented.Diagonal.Successor.point<
    ; reflects-< = λ { (Presented.Diagonal.Successor.point< q) → q }
    ; ceiling = top
    ; below = λ _ → Presented.Diagonal.Successor.point<top
    }

  module Top where

    to : 𝒫.X P → 𝒫.X (For.lower next top)
    to x = point x , Presented.Diagonal.Successor.point<top

    from : 𝒫.X (For.lower next top) → 𝒫.X P
    from (Presented.Diagonal.Successor.point x ,
      Presented.Diagonal.Successor.point<top) = x

    exact : 𝒫.X P ≅ 𝒫.X (For.lower next top)
    exact = record
      { forward = to
      ; backward = from
      ; backward-forward = λ x → refl
      ; forward-backward = λ
          { (Presented.Diagonal.Successor.point x ,
              Presented.Diagonal.Successor.point<top) → refl }
      }

    from-≈ : (u v : 𝒫.X (For.lower next top)) →
      𝒫._≈_ (For.lower next top) u v → 𝒫._≈_ P (from u) (from v)
    from-≈
      (Presented.Diagonal.Successor.point x ,
        Presented.Diagonal.Successor.point<top)
      (Presented.Diagonal.Successor.point y ,
        Presented.Diagonal.Successor.point<top)
      (Presented.Diagonal.Successor.point≈ q) = q

    from-< : (u v : 𝒫.X (For.lower next top)) →
      𝒫._<_ (For.lower next top) u v → 𝒫._<_ P (from u) (from v)
    from-<
      (Presented.Diagonal.Successor.point x ,
        Presented.Diagonal.Successor.point<top)
      (Presented.Diagonal.Successor.point y ,
        Presented.Diagonal.Successor.point<top)
      (Presented.Diagonal.Successor.point< q) = q

    presentation : P Presented.≃𝒫 For.lower next top
    presentation = record
      { to = to
      ; from = from
      ; to-≈ = Presented.Diagonal.Successor.point≈
      ; from-≈ = λ {u} {v} → from-≈ u v
      ; to-< = Presented.Diagonal.Successor.point<
      ; from-< = λ {u} {v} → from-< u v
      ; from-to-≈ = 𝒫.≈-refl P
      ; to-from-≈ = λ
          { (Presented.Diagonal.Successor.point x ,
              Presented.Diagonal.Successor.point<top) →
              Presented.Diagonal.Successor.point≈ (𝒫.≈-refl P x) }
      }

  module Old (x : 𝒫.X P) where

    to : 𝒫.X (For.lower P x) → 𝒫.X (For.lower next (point x))
    to u = point (pr₁ u) , Presented.Diagonal.Successor.point< (pr₂ u)

    from : 𝒫.X (For.lower next (point x)) → 𝒫.X (For.lower P x)
    from (Presented.Diagonal.Successor.point y ,
      Presented.Diagonal.Successor.point< q) = y , q

    exact : 𝒫.X (For.lower P x) ≅ 𝒫.X (For.lower next (point x))
    exact = record
      { forward = to
      ; backward = from
      ; backward-forward = λ u → refl
      ; forward-backward = λ
          { (Presented.Diagonal.Successor.point y ,
              Presented.Diagonal.Successor.point< q) → refl }
      }

    from-≈ : (u v : 𝒫.X (For.lower next (point x))) →
      𝒫._≈_ (For.lower next (point x)) u v →
      𝒫._≈_ (For.lower P x) (from u) (from v)
    from-≈
      (Presented.Diagonal.Successor.point y ,
        Presented.Diagonal.Successor.point< p)
      (Presented.Diagonal.Successor.point z ,
        Presented.Diagonal.Successor.point< r)
      (Presented.Diagonal.Successor.point≈ q) = q

    from-< : (u v : 𝒫.X (For.lower next (point x))) →
      𝒫._<_ (For.lower next (point x)) u v →
      𝒫._<_ (For.lower P x) (from u) (from v)
    from-<
      (Presented.Diagonal.Successor.point y ,
        Presented.Diagonal.Successor.point< p)
      (Presented.Diagonal.Successor.point z ,
        Presented.Diagonal.Successor.point< r)
      (Presented.Diagonal.Successor.point< q) = q

    presentation : For.lower P x Presented.≃𝒫 For.lower next (point x)
    presentation = record
      { to = to
      ; from = from
      ; to-≈ = Presented.Diagonal.Successor.point≈
      ; from-≈ = λ {u} {v} → from-≈ u v
      ; to-< = Presented.Diagonal.Successor.point<
      ; from-< = λ {u} {v} → from-< u v
      ; from-to-≈ = λ u → 𝒫.≈-refl P (pr₁ u)
      ; to-from-≈ = λ
          { (Presented.Diagonal.Successor.point y ,
              Presented.Diagonal.Successor.point< q) →
              Presented.Diagonal.Successor.point≈ (𝒫.≈-refl P y) }
      }

    point-β : (u : 𝒫.X (For.lower P x)) → pr₁ (to u) ＝ point (pr₁ u)
    point-β u = refl

    witness-β : (u : 𝒫.X (For.lower P x)) → pr₂ (from (to u)) ＝ pr₂ u
    witness-β u = refl
