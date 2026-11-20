{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Presentation.Limit.Discriminator where

-- The small presentations of the LPO discriminators: possible s, which has
-- a point exactly when the Boolean stream s hits true, 1 and 2, and hits t,
-- the hits of t ordered as in ω.  A possibly inhabited singleton followed
-- by constant singleton stages has a singleton boundary. Deciding its first
-- image, or selecting the least stage of its boundary point, would decide
-- an arbitrary Boolean stream.

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Accessibility using (acc)
open import SPT.Cubical.Foundation.Isomorphisms using (_≅_)
open import SPT.Cubical.Foundation.Nat.WellFounded using (wfℕˢ)
open import SPT.Cubical.Foundation.WellFounded.Pullback using
  ( pullback-is-well-founded )

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
import SPT.Cubical.OrdinalGeometry.Presentation.Map as Maps
import SPT.Cubical.OrdinalGeometry.Presentation.Limit as Limit
import SPT.Cubical.OrdinalGeometry.ExactOrder.Base as Order
import SPT.Cubical.OrdinalGeometry.ExactOrder.Maps as Orders

Hit : (ℕ → 𝟚) → Set
Hit s = Σ ℕ (λ n → s n ＝ ₁)

private
  -- The entries of a successor presentation: old points and the top.
  module Entry = Presented.Diagonal.Successor

  entry : (b : 𝟚) → Maybe (b ＝ ₁)
  entry ₀ = nothing
  entry ₁ = just refl

  entered : (b : 𝟚) (p : b ＝ ₁) → entry b ＝ just p
  entered .₁ refl = refl

  -- The hits of s, each listed at its own index.
  enumeration : (s : ℕ → 𝟚) → ℕ → Maybe (Hit s)
  enumeration s n = maybe-map (n ,_) (entry (s n))

  listed : (s : ℕ → 𝟚) (x : Hit s) → enumeration s (pr₁ x) ＝ just x
  listed s (n , p) = ap (maybe-map (n ,_)) (entered (s n) p)

------------------------------------------------------------------------
-- The small presentations

-- possible s: the hits of s, all identified.
possible : (ℕ → 𝟚) → 𝒫 lzero
possible s = record
  { X = Hit s ; _≈_ = λ _ _ → 𝟙 ; _<_ = λ _ _ → 𝟘
  ; ≈-refl = λ _ → ⋆ ; ≈-sym = λ _ → ⋆ ; ≈-trans = λ _ _ → ⋆
  ; <-trans = λ () ; <-respˡ-≈ = λ _ () ; <-respʳ-≈ = λ _ ()
  ; <-wf = λ _ → acc λ _ () ; compare = λ _ _ → inr (inl ⋆)
  ; enum = enumeration s
  ; covers = λ x → pr₁ x , x , listed s x , ⋆
  }

one : 𝒫 lzero
one = record
  { X = 𝟙 ; _≈_ = λ _ _ → 𝟙 ; _<_ = λ _ _ → 𝟘
  ; ≈-refl = λ _ → ⋆ ; ≈-sym = λ _ → ⋆ ; ≈-trans = λ _ _ → ⋆
  ; <-trans = λ () ; <-respˡ-≈ = λ _ () ; <-respʳ-≈ = λ _ ()
  ; <-wf = λ _ → acc λ _ () ; compare = λ _ _ → inr (inl ⋆)
  ; enum = λ _ → just ⋆ ; covers = λ _ → zero , ⋆ , refl , ⋆
  }

-- 2 = 1 + 1; nothing lies below its old point.
two : 𝒫 lzero
two = Maps.Successor.next one

bottom : {u : 𝒫.X two} → 𝒫._<_ two u (Entry.point ⋆) → 𝟘
bottom (Entry.point< ())

-- possible s ≤ 1, and possible s ≃ 1 at a hit.
inclusion : (s : ℕ → 𝟚) → Maps.Initial (possible s) one
inclusion s = record
  { map = λ _ → ⋆ ; resp = λ _ → ⋆ ; strict = λ () ; lower = λ _ _ () }

single : (s : ℕ → 𝟚) → Hit s → possible s Presented.≃𝒫 one
single s h = record
  { to = λ _ → ⋆ ; from = λ _ → h
  ; to-≈ = λ _ → ⋆ ; from-≈ = λ _ → ⋆
  ; to-< = λ () ; from-< = λ ()
  ; from-to-≈ = λ _ → ⋆ ; to-from-≈ = λ _ → ⋆
  }

-- hits t: the hits of t ordered as in ω, {n ∈ ω | t n = true}.
hits : (ℕ → 𝟚) → 𝒫 lzero
hits t = record
  { X = Hit t
  ; _≈_ = λ u v → pr₁ u ＝ pr₁ v
  ; _<_ = λ u v → pr₁ u <ℕˢ pr₁ v
  ; ≈-refl = λ _ → refl
  ; ≈-sym = _⁻¹
  ; ≈-trans = _∙_
  ; <-trans = <ℕˢ-trans
  ; <-respˡ-≈ = λ {_} {_} {y} p q → transport (λ m → m <ℕˢ pr₁ y) p q
  ; <-respʳ-≈ = λ {x} p q → transport (λ m → pr₁ x <ℕˢ m) p q
  ; <-wf = pullback-is-well-founded pr₁ _<ℕˢ_ wfℕˢ
  ; compare = λ u v →
      Order.Order.compare Order.natural (pr₁ u) (pr₁ v)
  ; enum = enumeration t
  ; covers = λ x → pr₁ x , x , listed t x , refl
  }

------------------------------------------------------------------------
-- The boundary of possible s, 1, 1, …

private
  stages : (ℕ → 𝟚) → ℕ → 𝒫 lzero
  stages s zero = possible s
  stages s (suc n) = one

  edges : (s : ℕ → 𝟚) (n : ℕ)
    → Maps.Initial (stages s n) (stages s (suc n))
  edges s zero = inclusion s
  edges s (suc n) = Maps.identity one

chain : (ℕ → 𝟚) → Limit.Chain lzero
chain s = record { stage = stages s ; edge = edges s }

boundary : (ℕ → 𝟚) → 𝒫 lzero
boundary s = Limit.completion (chain s)

private
  members : (s : ℕ → 𝟚) (n : ℕ) → Maps.Initial (stages s n) one
  members s zero = inclusion s
  members s (suc n) = Maps.identity one

singleton : (s : ℕ → 𝟚) → boundary s Presented.≃𝒫 one
singleton s = Limit.exhaustion (chain s) one (members s)
  (λ _ → suc zero , ⋆ , ⋆)

-- The carrier of the boundary itself is isomorphic to ⊤.
equivalence : (s : ℕ → 𝟚) → 𝒫.X (boundary s) ≅ 𝟙
equivalence s = Orders.from-inverses
  (Presented._≃𝒫_.to (singleton s)) (Presented._≃𝒫_.from (singleton s))
  (λ x → Limit.equal (chain s) (Presented._≃𝒫_.from-to-≈ (singleton s) x))
  (λ _ → refl)

point : (s : ℕ → 𝟚) → 𝒫.X (boundary s)
point s = Maps.Initial.map (Limit.stage (chain s) (suc zero)) ⋆

collapsed : (s : ℕ → 𝟚) (x : Hit s)
  → Maps.Initial.map (Limit.stage (chain s) zero) x ＝ point s
collapsed s x = Limit.compatible (chain s) zero x ⁻¹

------------------------------------------------------------------------
-- LPO

LPO : Set
LPO = (s : ℕ → 𝟚) → Hit s ⊎ ((n : ℕ) → s n ＝ ₀)

-- Without a hit, s is false everywhere.
absent : (s : ℕ → 𝟚) → (Hit s → 𝟘) → (n : ℕ) → s n ＝ ₀
absent s no-hit n with s n in p
... | ₀ = refl
... | ₁ = 𝟘-elim (no-hit (n , p))

Image : (ℕ → 𝟚) → Set
Image s = Σ (Hit s) (λ x → 𝒫._≈_ one (Maps.Initial.map (inclusion s) x) ⋆)

image-decision : ((s : ℕ → 𝟚) → is-decidable (Image s)) → LPO
image-decision decide s with decide s
... | inl (x , _) = inl x
... | inr no-image = inr (absent s (λ x → no-image (x , ⋆)))

First : (s : ℕ → 𝟚) → Set
First s = Σ ℕ λ n →
  (Σ (𝒫.X (stages s n))
    (λ x → Maps.Initial.map (Limit.stage (chain s) n) x ＝ point s)) ×
  ((m : ℕ) (x : 𝒫.X (stages s m))
    → Maps.Initial.map (Limit.stage (chain s) m) x ＝ point s → n ≤ℕˢ m)

first-stage : ((s : ℕ → 𝟚) → First s) → LPO
first-stage first s with first s
... | zero , (x , _) , least = inl x
... | suc n , _ , least = inr (absent s no-hit)
  where
  no-hit : Hit s → 𝟘
  no-hit x with least zero x (collapsed s x)
  ... | ()
