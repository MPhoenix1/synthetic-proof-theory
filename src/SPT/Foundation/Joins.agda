{-# OPTIONS --safe --without-K #-}

module SPT.Foundation.Joins where

-- Maps out of the iterated joins of a type F into a type Y, unfolded by
-- the universal property of the join, so that no join is formed
-- (`join-maps`, `constant-map`, `restriction`):
--
--   maps 0       = F → Y,
--   maps (n + 1) = Σ (f : F → Y). Σ (g : maps n). Π a. constant n (f a) ＝ g,
--
-- with the restriction (f , g , h) ↦ g along the inclusion of each join
-- into the next. Their functional sequential limit (Limits.Sequential)
-- receives the constant families (`Join-Limit`, `constant-family`).
--
-- At a point a₀ of F every type is that limit (`pointed-join-limit`,
-- `constant-family-is-equivalence`). The point of a limit is the value at
-- a₀ of its first map one stage up (`limit-point`). Its constant family is
-- the limit itself: each stage is reached through the third component at
-- a₀ (`contraction`), the values at a₀ agree along the stages
-- (`settled`, `point-path`, `limit-stage-path`), and the commutation with
-- the restrictions is one square, by refl after matching its three free
-- identifications (`coherence-step`):
--
--   ap c ρ ∙ (contraction v ∙ ε) ＝ ap r (ap c′ (ρ ∙ ap ev t ⁻¹) ∙ t) ∙ ε.
--
-- The alignment of Limits.Sequential.Identity identifies them. Over a
-- cover, every member of a family is the limit over the fiber at it, since
-- being an equivalence is a proposition and the fibers at the images are
-- pointed (`members-are-join-limits`). The higher coherences of a
-- coherently constant map are identity types of the stage below; nothing
-- above identity types is asked for. This is the dual of Rijke's join
-- construction: maps out of the colimit of the joins, as a limit.

open import SPT.Base
open import SPT.Foundation.Contractible using (is-contractible)
open import SPT.Foundation.Covers using (Cover; descend)
open import SPT.Foundation.Equivalences using
  (being-equivalence-is-proposition)
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.Extensionality.Levels using (funext-below)
open import SPT.Foundation.Fibers using (fiber; has-contractible-fibers)
open import SPT.Foundation.Isomorphisms using (_≅_)
open import SPT.Foundation.Univalence using
  (isomorphisms-have-contractible-fibers)
open import SPT.Foundation.Limits.Sequential using
  (limit; stage; adjacent; Functional-Limit)
open import SPT.Foundation.Limits.Sequential.Path using (alignment)
open import SPT.Foundation.Limits.Sequential.Identity using (alignment-path)

------------------------------------------------------------------------
-- Maps out of the iterated joins

module _ {κ ℓ : Level} (F : Set κ) (Y : Set ℓ) where

  join-maps : ℕ → Set (κ ⊔ ℓ)
  constant-map : (n : ℕ) → Y → join-maps n

  join-maps zero = F → Y
  join-maps (suc n) =
    Σ (F → Y) (λ f →
      Σ (join-maps n) (λ g → (a : F) → constant-map n (f a) ＝ g))

  constant-map zero y = λ a → y
  constant-map (suc n) y = (λ a → y) , (constant-map n y , (λ a → refl))

  -- Restriction along the inclusion of the n-th join into the next.
  restriction : (n : ℕ) → join-maps (suc n) → join-maps n
  restriction n m = pr₁ (pr₂ m)

  Join-Limit : Set (κ ⊔ ℓ)
  Join-Limit = Functional-Limit join-maps restriction

  constant-family : Y → Join-Limit
  constant-family y = limit (λ n → constant-map n y) (λ n → refl)

------------------------------------------------------------------------
-- At a point of F

module _ {κ ℓ : Level} (F : Set κ) (Y : Set ℓ) (a₀ : F) where

  evaluation : (n : ℕ) → join-maps F Y (suc n) → Y
  evaluation n m = pr₁ m a₀

  contraction : (n : ℕ) (m : join-maps F Y (suc n)) →
    constant-map F Y n (evaluation n m) ＝ restriction F Y n m
  contraction n m = pr₂ (pr₂ m) a₀

  limit-point : Join-Limit F Y → Y
  limit-point L = evaluation zero (stage L (suc zero))

  -- The square of one restriction, with its three identifications free.
  coherence-step : (n : ℕ) {y₀ y′ : Y} {v : join-maps F Y (suc n)}
    {w : join-maps F Y n} (t : constant-map F Y (suc n) y′ ＝ v)
    (ρ : y₀ ＝ evaluation n v) (ε : restriction F Y n v ＝ w) →
    ap (constant-map F Y n) ρ ∙ (contraction n v ∙ ε)
      ＝ ap (restriction F Y n)
          (ap (constant-map F Y (suc n)) (ρ ∙ ap (evaluation n) t ⁻¹) ∙ t)
        ∙ ε
  coherence-step n refl refl refl = refl

  module _ (L : Join-Limit F Y) where

    -- A stage one up is the constant map of its value at a₀.
    settled : (n : ℕ) →
      constant-map F Y (suc n) (evaluation (suc n) (stage L (suc (suc n))))
        ＝ stage L (suc n)
    settled n = contraction (suc n) (stage L (suc (suc n))) ∙ adjacent L (suc n)

    -- The values at a₀ agree along the stages.
    point-path : (n : ℕ) →
      evaluation zero (stage L (suc zero)) ＝ evaluation n (stage L (suc n))
    point-path zero = refl
    point-path (suc n) = point-path n ∙ ap (evaluation n) (settled n) ⁻¹

    -- Each stage is the constant map of the limit's point.
    limit-stage-path : (n : ℕ) →
      constant-map F Y n (evaluation zero (stage L (suc zero))) ＝ stage L n
    limit-stage-path n =
      ap (constant-map F Y n) (point-path n)
        ∙ (contraction n (stage L (suc n)) ∙ adjacent L n)

    limit-round-trip :
      ((X : Set (κ ⊔ ℓ)) (Z : X → Set (κ ⊔ ℓ)) → FunExt X Z) →
      constant-family F Y (limit-point L) ＝ L
    limit-round-trip functions =
      alignment-path (restriction F Y)
        (λ f → funext-below (κ ⊔ ℓ) functions ℕ
          (λ n → Σ (join-maps F Y n) (λ p → f n ＝ p)))
        (λ f → funext-below (κ ⊔ ℓ) functions ℕ
          (λ n → restriction F Y n (f (suc n)) ＝ f n))
        (alignment limit-stage-path
          (λ n → coherence-step n (settled n) (point-path n) (adjacent L n)))

  pointed-join-limit :
    ((X : Set (κ ⊔ ℓ)) (Z : X → Set (κ ⊔ ℓ)) → FunExt X Z) →
    Y ≅ Join-Limit F Y
  pointed-join-limit functions = record
    { forward = constant-family F Y
    ; backward = limit-point
    ; backward-forward = λ y → refl
    ; forward-backward = λ L → limit-round-trip L functions
    }

  constant-family-is-equivalence :
    ((X : Set (κ ⊔ ℓ)) (Z : X → Set (κ ⊔ ℓ)) → FunExt X Z) →
    has-contractible-fibers (constant-family F Y)
  constant-family-is-equivalence functions =
    isomorphisms-have-contractible-fibers (pointed-join-limit functions)

------------------------------------------------------------------------
-- Over a cover

module _ {ℓ : Level} {E X : Set ℓ} {q : E → X} where

  members-are-join-limits :
    ((U : Set ℓ) (Z : U → Set ℓ) → FunExt U Z) → Cover ℓ q →
    (B : X → Set ℓ) (x : X) →
    has-contractible-fibers (constant-family (fiber q x) (B x))
  members-are-join-limits functions cover B =
    descend cover
      (λ x → has-contractible-fibers (constant-family (fiber q x) (B x)))
      (λ x → being-equivalence-is-proposition
        (constant-family (fiber q x) (B x))
        (functions (Join-Limit (fiber q x) (B x))
          (λ l → is-contractible
            (fiber (constant-family (fiber q x) (B x)) l)))
        (λ l c → functions (fiber (constant-family (fiber q x) (B x)) l)
          (λ y → c ＝ y)))
      (λ e → constant-family-is-equivalence (fiber q (q e)) (B (q e))
        (e , refl) functions)
