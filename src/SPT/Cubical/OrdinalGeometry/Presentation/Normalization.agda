{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Presentation.Normalization where

-- Countable ordinal classes represented by their least enumeration indices.
-- Equivalent inputs become equal points; validity and strict comparison
-- have unique witnesses. The enumeration determines codes, not their order.

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Accessibility using (acc; is-accessible)
open import SPT.Cubical.Foundation.Nat.Identifications using
  ( ℕ-identifications-agree )
open import SPT.Cubical.Foundation.Nat.Order using (cmpℕᶜ)
open import SPT.Cubical.Foundation.Two.Truth using (is-₁)

import SPT.Cubical.Foundation.Nat.FirstSuccess as Search
open Search.Sequence using
  (Hit; Address; First; value; hit; selects; normalize;
   clash; at; hit-proposition)
import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
open 𝒫
import SPT.Cubical.OrdinalGeometry.ExactOrder.Base as Order

private
  variable
    ℓ : Level

  matching : (P : 𝒫 ℓ) → X P → ℕ → Maybe (X P)
  matching P x n with enum P n
  ... | nothing = nothing
  ... | just r with compare P r x
  ...   | inl _ = nothing
  ...   | inr (inl _) = just r
  ...   | inr (inr _) = nothing

  sound : (P : 𝒫 ℓ) (x : X P) (n : ℕ)
    → Hit (matching P x) n
    → Σ (Hit (enum P) n) (λ h → _≈_ P (value (enum P) n h) x)
  sound P x n h with enum P n
  sound P x n () | nothing
  sound P x n h | just r with compare P r x
  sound P x n () | just r | inl _
  sound P x n h | just r | inr (inl p) = ⋆ , p
  sound P x n () | just r | inr (inr _)

  complete : (P : 𝒫 ℓ) (x : X P) (n : ℕ)
    → (h : Hit (enum P) n)
    → _≈_ P (value (enum P) n h) x → Hit (matching P x) n
  complete P x n h p with enum P n
  complete P x n () p | nothing
  complete P x n h p | just r with compare P r x
  ... | inl q = 𝟘-elim (Presented.Presentation.≈↛< P p q)
  ... | inr (inl _) = ⋆
  ... | inr (inr q) =
    𝟘-elim (Presented.Presentation.≈↛< P (≈-sym P p) q)

  hit-resp : (P : 𝒫 ℓ) {x y : X P}
    → _≈_ P x y → (n : ℕ)
    → Hit (matching P x) n → Hit (matching P y) n
  hit-resp P {x} {y} p n h with sound P x n h
  ... | entry , q = complete P y n entry (≈-trans P q p)

  abstract
    first : (P : 𝒫 ℓ) (x : X P) → First (matching P x)
    first P x with covers P x
    ... | n , r , selected , p = normalize (matching P x)
      (n , complete P x n (hit (enum P) n r selected)
        (transport (λ y → _≈_ P y x)
          ((just-is-injective (
            selects (enum P) n (hit (enum P) n r selected) ⁻¹
            ∙ selected)) ⁻¹) p))

code : (P : 𝒫 ℓ) → X P → ℕ
code P x = pr₁ (first P x)

code-resp : (P : 𝒫 ℓ) {x y : X P}
  → _≈_ P x y → code P x ＝ code P y
code-resp P {x} {y} p with cmpℕᶜ (code P x) (code P y)
... | inl earlier = 𝟘-elim (clash (matching P y) (code P x)
  (hit-resp P p (code P x) (pr₂ (pr₂ (first P x))))
  (at (matching P y) (code P x) (code P y) earlier
    (pr₁ (pr₂ (first P y)))))
... | inr (inl same) = same
... | inr (inr earlier) = 𝟘-elim (clash (matching P x) (code P y)
  (hit-resp P (≈-sym P p) (code P y) (pr₂ (pr₂ (first P y))))
  (at (matching P x) (code P y) (code P x) earlier
    (pr₁ (pr₂ (first P x)))))

private
  entry : (P : 𝒫 ℓ) (x : X P) → Hit (enum P) (code P x)
  entry P x = pr₁ (sound P x (code P x) (pr₂ (pr₂ (first P x))))

  represents : (P : 𝒫 ℓ) (x : X P)
    → _≈_ P (value (enum P) (code P x) (entry P x)) x
  represents P x = pr₂
    (sound P x (code P x) (pr₂ (pr₂ (first P x))))

Point : 𝒫 ℓ → Set
Point P = Σ (Address (enum P)) λ a →
  code P (value (enum P) (pr₁ a) (pr₂ a)) ＝ pr₁ a

index : (P : 𝒫 ℓ) → Point P → ℕ
index P a = pr₁ (pr₁ a)

representative : (P : 𝒫 ℓ) → Point P → X P
representative P ((n , h) , _) = value (enum P) n h

equal : (P : 𝒫 ℓ) {a b : Point P}
  → index P a ＝ index P b → a ＝ b
equal P {(n , h) , p} {(.n , k) , q} refl
  with hit-proposition (enum P) n h k
... | refl = ap ((n , h) ,_) (ℕ-identifications-agree p q)

class : (P : 𝒫 ℓ) → X P → Point P
class P x = (code P x , entry P x) , code-resp P (represents P x)

class-resp : (P : 𝒫 ℓ) {x y : X P}
  → _≈_ P x y → class P x ＝ class P y
class-resp P p = equal P (code-resp P p)

representative-class : (P : 𝒫 ℓ) (x : X P)
  → _≈_ P (representative P (class P x)) x
representative-class = represents

class-representative : (P : 𝒫 ℓ) (a : Point P)
  → class P (representative P a) ＝ a
class-representative P a = equal P (pr₂ a)

class-reflect : (P : 𝒫 ℓ) {x y : X P}
  → class P x ＝ class P y → _≈_ P x y
class-reflect P {x} {y} p = ≈-trans P (≈-sym P (represents P x))
  (transport (λ a → _≈_ P (representative P a) y) (p ⁻¹) (represents P y))

private
  less : (P : 𝒫 ℓ) → X P → X P → 𝟚
  less P x y with compare P x y
  ... | inl _ = ₁
  ... | inr _ = ₀

  less-sound : (P : 𝒫 ℓ) {x y : X P}
    → is-₁ (less P x y) → _<_ P x y
  less-sound P {x} {y} p with compare P x y
  ... | inl q = q
  ... | inr _ = 𝟘-elim p

  less-complete : (P : 𝒫 ℓ) {x y : X P}
    → _<_ P x y → is-₁ (less P x y)
  less-complete P {x} {y} p with compare P x y
  ... | inl _ = ⋆
  ... | inr (inl q) = 𝟘-elim (Presented.Presentation.≈↛< P q p)
  ... | inr (inr q) = 𝟘-elim (Presented.Presentation.<-asym P p q)

Strict : (P : 𝒫 ℓ) → Point P → Point P → Set
Strict P a b = is-₁ (less P (representative P a) (representative P b))

strict-unique : (P : 𝒫 ℓ) {a b : Point P}
  → (p q : Strict P a b) → p ＝ q
strict-unique P {a} {b} p q
  with less P (representative P a) (representative P b)
... | ₁ = refl
... | ₀ = 𝟘-elim p

representative-strict : (P : 𝒫 ℓ) {a b : Point P}
  → Strict P a b → _<_ P (representative P a) (representative P b)
representative-strict P = less-sound P

representative-reflect : (P : 𝒫 ℓ) {a b : Point P}
  → _<_ P (representative P a) (representative P b) → Strict P a b
representative-reflect P = less-complete P

class-strict : (P : 𝒫 ℓ) {x y : X P}
  → _<_ P x y → Strict P (class P x) (class P y)
class-strict P {x} {y} p = less-complete P
  (<-respʳ-≈ P (≈-sym P (represents P y))
    (<-respˡ-≈ P (≈-sym P (represents P x)) p))

class-reflects-strict : (P : 𝒫 ℓ) {x y : X P}
  → Strict P (class P x) (class P y) → _<_ P x y
class-reflects-strict P {x} {y} p =
  <-respʳ-≈ P (represents P y)
    (<-respˡ-≈ P (represents P x) (less-sound P p))

private
  accessible : (P : 𝒫 ℓ) (a : Point P)
    → is-accessible (_<_ P) (representative P a) → is-accessible (Strict P) a
  accessible P a (acc smaller) = acc λ b p →
    accessible P b (smaller (representative P b) (less-sound P p))

  comparison : (P : 𝒫 ℓ) (a b : Point P)
    → Strict P a b ⊎ ((a ＝ b) ⊎ Strict P b a)
  comparison P a b with compare P (representative P a) (representative P b)
  ... | inl p = inl ⋆
  ... | inr (inl p) = inr (inl (equal P
    (pr₂ a ⁻¹ ∙ (code-resp P p ∙ pr₂ b))))
  ... | inr (inr p) = inr (inr (less-complete P p))

  enumeration : (P : 𝒫 ℓ) → ℕ → Maybe (Point P)
  enumeration P n = maybe-map (class P) (enum P n)

  coverage : (P : 𝒫 ℓ) (a : Point P)
    → Σ ℕ (λ n → enumeration P n ＝ just a)
  coverage P a with covers P (representative P a)
  ... | n , r , selected , p = n ,
    ap (maybe-map (class P)) selected
    ∙ ap just (class-resp P p ∙ class-representative P a)

  abstract
    well-founded : (P : 𝒫 ℓ) (a : Point P)
      → is-accessible (Strict P) a
    well-founded P a = accessible P a (<-wf P (representative P a))

order : (P : 𝒫 ℓ) → Order.Order (Point P)
order P = record
  { _<_ = Strict P
  ; trans = λ p q → less-complete P
      (<-trans P (less-sound P p) (less-sound P q))
  ; wf = well-founded P
  ; compare = comparison P
  ; enum = enumeration P
  ; covers = coverage P
  }
