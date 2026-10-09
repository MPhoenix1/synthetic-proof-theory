{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Presentation.Limit.Discriminator where

-- The small presentations of the LPO discriminators: possible s, which has
-- a point exactly when the Boolean stream s hits true, 1 and 2, and hits t,
-- the hits of t ordered as in ω.  A possibly inhabited singleton followed
-- by constant singleton stages has a singleton boundary. Deciding its first
-- image, or selecting the least stage of its boundary point, would decide
-- an arbitrary Boolean stream.

open import Agda.Primitive using (lzero)
open import Data.Bool using (Bool; false; true)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Nat using (ℕ; zero; suc; _≤_)
import Data.Nat as Nat
import Data.Nat.Properties as NatProperties
open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; sym; trans; subst)

open import SPT.Cubical.Core.WellFounded using (acc)
open import SPT.Cubical.Core.Equality.Isomorphism using (_≅_)
open import SPT.Cubical.Core.Nat.WellFounded using (wfℕˢ)
open import SPT.Cubical.Core.WellFounded.Pullback using (pullback-wf)
import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
import SPT.Cubical.OrdinalGeometry.Presentation.Map as Maps
import SPT.Cubical.OrdinalGeometry.Presentation.Limit as Limit
import SPT.Cubical.OrdinalGeometry.ExactOrder.Base as Order
import SPT.Cubical.OrdinalGeometry.ExactOrder.Maps as Orders

Hit : (ℕ → Bool) → Set
Hit s = Σ ℕ (λ n → s n ≡ true)

private
  -- The entries of a successor presentation: old points and the top.
  module Entry = Presented.Diagonal.Successor

  entry : (b : Bool) → Maybe (b ≡ true)
  entry false = nothing
  entry true = just refl

  entered : (b : Bool) (p : b ≡ true) → entry b ≡ just p
  entered .true refl = refl

  -- The hits of s, each listed at its own index.
  enumeration : (s : ℕ → Bool) → ℕ → Maybe (Hit s)
  enumeration s n = Maybe.map (n ,_) (entry (s n))

  listed : (s : ℕ → Bool) (x : Hit s) → enumeration s (proj₁ x) ≡ just x
  listed s (n , p) = cong (Maybe.map (n ,_)) (entered (s n) p)

------------------------------------------------------------------------
-- The small presentations

-- possible s: the hits of s, all identified.
possible : (ℕ → Bool) → 𝒫 lzero
possible s = record
  { X = Hit s ; _≈_ = λ _ _ → ⊤ ; _<_ = λ _ _ → ⊥
  ; ≈-refl = λ _ → tt ; ≈-sym = λ _ → tt ; ≈-trans = λ _ _ → tt
  ; <-trans = λ () ; <-respˡ-≈ = λ _ () ; <-respʳ-≈ = λ _ ()
  ; <-wf = λ _ → acc λ _ () ; compare = λ _ _ → inj₂ (inj₁ tt)
  ; enum = enumeration s
  ; covers = λ x → proj₁ x , x , listed s x , tt
  }

one : 𝒫 lzero
one = record
  { X = ⊤ ; _≈_ = λ _ _ → ⊤ ; _<_ = λ _ _ → ⊥
  ; ≈-refl = λ _ → tt ; ≈-sym = λ _ → tt ; ≈-trans = λ _ _ → tt
  ; <-trans = λ () ; <-respˡ-≈ = λ _ () ; <-respʳ-≈ = λ _ ()
  ; <-wf = λ _ → acc λ _ () ; compare = λ _ _ → inj₂ (inj₁ tt)
  ; enum = λ _ → just tt ; covers = λ _ → zero , tt , refl , tt
  }

-- 2 = 1 + 1; nothing lies below its old point.
two : 𝒫 lzero
two = Maps.Successor.next one

bottom : {u : 𝒫.X two} → 𝒫._<_ two u (Entry.point tt) → ⊥
bottom (Entry.point< ())

-- possible s ≤ 1, and possible s ≃ 1 at a hit.
inclusion : (s : ℕ → Bool) → Maps.Initial (possible s) one
inclusion s = record
  { map = λ _ → tt ; resp = λ _ → tt ; strict = λ () ; lower = λ _ _ () }

single : (s : ℕ → Bool) → Hit s → possible s Presented.≃𝒫 one
single s h = record
  { to = λ _ → tt ; from = λ _ → h
  ; to-≈ = λ _ → tt ; from-≈ = λ _ → tt
  ; to-< = λ () ; from-< = λ ()
  ; from-to-≈ = λ _ → tt ; to-from-≈ = λ _ → tt
  }

-- hits t: the hits of t ordered as in ω, {n ∈ ω | t n = true}.
hits : (ℕ → Bool) → 𝒫 lzero
hits t = record
  { X = Hit t
  ; _≈_ = λ u v → proj₁ u ≡ proj₁ v
  ; _<_ = λ u v → proj₁ u Nat.< proj₁ v
  ; ≈-refl = λ _ → refl
  ; ≈-sym = sym
  ; ≈-trans = trans
  ; <-trans = NatProperties.<-trans
  ; <-respˡ-≈ = λ {_} {_} {y} p q → subst (λ m → m Nat.< proj₁ y) p q
  ; <-respʳ-≈ = λ {x} p q → subst (λ m → proj₁ x Nat.< m) p q
  ; <-wf = pullback-wf {rank = proj₁} wfℕˢ
  ; compare = λ u v →
      Order.Order.compare Order.natural (proj₁ u) (proj₁ v)
  ; enum = enumeration t
  ; covers = λ x → proj₁ x , x , listed t x , refl
  }

------------------------------------------------------------------------
-- The boundary of possible s, 1, 1, …

private
  stages : (ℕ → Bool) → ℕ → 𝒫 lzero
  stages s zero = possible s
  stages s (suc n) = one

  edges : (s : ℕ → Bool) (n : ℕ)
    → Maps.Initial (stages s n) (stages s (suc n))
  edges s zero = inclusion s
  edges s (suc n) = Maps.identity one

chain : (ℕ → Bool) → Limit.Chain lzero
chain s = record { stage = stages s ; edge = edges s }

boundary : (ℕ → Bool) → 𝒫 lzero
boundary s = Limit.completion (chain s)

private
  members : (s : ℕ → Bool) (n : ℕ) → Maps.Initial (stages s n) one
  members s zero = inclusion s
  members s (suc n) = Maps.identity one

singleton : (s : ℕ → Bool) → boundary s Presented.≃𝒫 one
singleton s = Limit.exhaustion (chain s) one (members s)
  (λ _ → suc zero , tt , tt)

-- The carrier of the boundary itself is isomorphic to ⊤.
equivalence : (s : ℕ → Bool) → 𝒫.X (boundary s) ≅ ⊤
equivalence s = Orders.from-inverses
  (Presented._≃𝒫_.to (singleton s)) (Presented._≃𝒫_.from (singleton s))
  (λ x → Limit.equal (chain s) (Presented._≃𝒫_.from-to-≈ (singleton s) x))
  (λ _ → refl)

point : (s : ℕ → Bool) → 𝒫.X (boundary s)
point s = Maps.Initial.map (Limit.stage (chain s) (suc zero)) tt

collapsed : (s : ℕ → Bool) (x : Hit s)
  → Maps.Initial.map (Limit.stage (chain s) zero) x ≡ point s
collapsed s x = sym (Limit.compatible (chain s) zero x)

------------------------------------------------------------------------
-- LPO

LPO : Set
LPO = (s : ℕ → Bool) → Hit s ⊎ ((n : ℕ) → s n ≡ false)

-- Without a hit, s is false everywhere.
absent : (s : ℕ → Bool) → (Hit s → ⊥) → (n : ℕ) → s n ≡ false
absent s no-hit n with s n in p
... | false = refl
... | true = ⊥-elim (no-hit (n , p))

Image : (ℕ → Bool) → Set
Image s = Σ (Hit s) (λ x → 𝒫._≈_ one (Maps.Initial.map (inclusion s) x) tt)

image-decision : ((s : ℕ → Bool) → Dec (Image s)) → LPO
image-decision decide s with decide s
... | yes (x , _) = inj₁ x
... | no no-image = inj₂ (absent s (λ x → no-image (x , tt)))

First : (s : ℕ → Bool) → Set
First s = Σ ℕ λ n →
  (Σ (𝒫.X (stages s n))
    (λ x → Maps.Initial.map (Limit.stage (chain s) n) x ≡ point s)) ×
  ((m : ℕ) (x : 𝒫.X (stages s m))
    → Maps.Initial.map (Limit.stage (chain s) m) x ≡ point s → n ≤ m)

first-stage : ((s : ℕ → Bool) → First s) → LPO
first-stage first s with first s
... | zero , (x , _) , least = inj₁ x
... | suc n , _ , least = inj₂ (absent s no-hit)
  where
  no-hit : Hit s → ⊥
  no-hit x with least zero x (collapsed s x)
  ... | ()
