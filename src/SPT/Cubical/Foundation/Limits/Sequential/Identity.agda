{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.Limits.Sequential.Identity where

-- Identifications of points of a functional sequential limit. An
-- identification is read stagewise as an alignment
-- (Limits.Sequential.Path), with unit squares at refl (`from-path`). With
-- extensionality for the stage family and for the witnesses over a fixed
-- stage family, every alignment gives an identification whose stages are
-- its paths (`alignment-path`, `alignment-path-β`), by homotopy induction
-- over the stages. With extensionality for the identifications of witnesses
-- as well, the aligned points of u are contractible, and the two correspond
-- exactly, every square recovered (`identifications-are-alignments`):
--
--   (u ＝ v) ≅ Alignment r u v.

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Contractible using (is-contractible)
open import SPT.Cubical.Foundation.Extensionality using (FunExt)
open import SPT.Cubical.Foundation.Happly using
  (homotopy-induction; homotopies-are-contractible)
open import SPT.Cubical.Foundation.Isomorphisms using (_≅_)
open import SPT.Cubical.Foundation.Limits.Sequential using
  (limit; stage; adjacent; Functional-Limit)
open import SPT.Cubical.Foundation.Limits.Sequential.Path using
  (Squares; Alignment; alignment; stage-path; square)

------------------------------------------------------------------------
-- Identifications read stagewise

module _ {ℓ : Level} {Stage : ℕ → Set ℓ}
  (r : (n : ℕ) → Stage (suc n) → Stage n) where

  from-path : {u v : Functional-Limit Stage r} → u ＝ v → Alignment r u v
  from-path {u} refl =
    alignment (λ n → refl) (λ n → refl-right-neutral (adjacent u n))

  -- An identification of witnesses over one stage family has constant
  -- stages.
  constant-stages : (f : (n : ℕ) → Stage n)
    {a b : (n : ℕ) → r n (f (suc n)) ＝ f n} (e : a ＝ b) (n : ℕ) →
    ap (λ (w : Functional-Limit Stage r) → stage w n) (ap (limit f) e)
      ＝ refl
  constant-stages f refl n = refl

------------------------------------------------------------------------
-- Alignments give identifications

module _ {ℓ : Level} {Stage : ℕ → Set ℓ}
  (r : (n : ℕ) → Stage (suc n) → Stage n)
  (stages : (f : (n : ℕ) → Stage n) →
    FunExt ℕ (λ n → Σ (Stage n) (λ p → f n ＝ p)))
  (routes : (f : (n : ℕ) → Stage n) →
    FunExt ℕ (λ n → r n (f (suc n)) ＝ f n))
  where

  -- At constant stages, the squares identify the witnesses.
  aligned-at-refl : (u : Functional-Limit Stage r)
    (b : (n : ℕ) → r n (stage u (suc n)) ＝ stage u n) →
    Squares r u (limit (stage u) b) (λ n → refl) →
    Σ (u ＝ limit (stage u) b) (λ p → (n : ℕ) →
      ap (λ (w : Functional-Limit Stage r) → stage w n) p ＝ refl)
  aligned-at-refl u b squares =
    let e = routes (stage u) (adjacent u) b
              (λ n → refl-right-neutral (adjacent u n) ⁻¹ ∙ squares n)
    in ap (limit (stage u)) e , constant-stages r (stage u) e

  -- By homotopy induction over the stage paths.
  calibrated : (u v : Functional-Limit Stage r) (h : Alignment r u v) →
    Σ (u ＝ v) (λ p → (n : ℕ) →
      ap (λ (w : Functional-Limit Stage r) → stage w n) p ＝ stage-path h n)
  calibrated u v h =
    homotopy-induction (stage u) (stages (stage u))
      (λ g h′ → (b : (n : ℕ) → r n (g (suc n)) ＝ g n) →
        Squares r u (limit g b) h′ →
        Σ (u ＝ limit g b) (λ p → (n : ℕ) →
          ap (λ (w : Functional-Limit Stage r) → stage w n) p ＝ h′ n))
      (aligned-at-refl u)
      (stage v) (stage-path h) (adjacent v) (square h)

  alignment-path : {u v : Functional-Limit Stage r} → Alignment r u v →
    u ＝ v
  alignment-path {u} {v} h = pr₁ (calibrated u v h)

  alignment-path-β : {u v : Functional-Limit Stage r}
    (h : Alignment r u v) (n : ℕ) →
    ap (λ (w : Functional-Limit Stage r) → stage w n) (alignment-path h)
      ＝ stage-path h n
  alignment-path-β {u} {v} h = pr₂ (calibrated u v h)

------------------------------------------------------------------------
-- Identifications are alignments

module _ {ℓ : Level} {Stage : ℕ → Set ℓ}
  (r : (n : ℕ) → Stage (suc n) → Stage n)
  (stages : (f : (n : ℕ) → Stage n) →
    FunExt ℕ (λ n → Σ (Stage n) (λ p → f n ＝ p)))
  (routes : (f : (n : ℕ) → Stage n)
    (a : (n : ℕ) → r n (f (suc n)) ＝ f n) →
    FunExt ℕ (λ n → Σ (r n (f (suc n)) ＝ f n) (λ p → a n ＝ p)))
  (u : Functional-Limit Stage r)
  where

  -- The aligned points of u, centered at u itself.
  aligned-center : Σ (Functional-Limit Stage r) (λ v → Alignment r u v)
  aligned-center = u , from-path r refl

  -- An aligned point with constant stages, from a family of witnesses
  -- with its squares.
  refl-aligned-point :
    Σ ((n : ℕ) → r n (stage u (suc n)) ＝ stage u n) (λ b →
      (n : ℕ) → adjacent u n ∙ refl ＝ b n) →
    Σ (Functional-Limit Stage r) (λ v → Alignment r u v)
  refl-aligned-point c =
    limit (stage u) (pr₁ c) , alignment (λ n → refl) (pr₂ c)

  route-comparisons-are-contractible :
    is-contractible
      (Σ ((n : ℕ) → r n (stage u (suc n)) ＝ stage u n) (λ b →
        (n : ℕ) → adjacent u n ∙ refl ＝ b n))
  route-comparisons-are-contractible =
    homotopies-are-contractible (λ n → adjacent u n ∙ refl)
      (routes (stage u) (λ n → adjacent u n ∙ refl))

  private
    from-center :
      (c : Σ ((n : ℕ) → r n (stage u (suc n)) ＝ stage u n) (λ b →
        (n : ℕ) → adjacent u n ∙ refl ＝ b n)) →
      refl-aligned-point (pr₁ route-comparisons-are-contractible)
        ＝ refl-aligned-point c
    from-center c =
      ap refl-aligned-point (pr₂ route-comparisons-are-contractible c)

    at-refl : (b : (n : ℕ) → r n (stage u (suc n)) ＝ stage u n)
      (squares : Squares r u (limit (stage u) b) (λ n → refl)) →
      aligned-center ＝ (limit (stage u) b , alignment (λ n → refl) squares)
    at-refl b squares =
      from-center (adjacent u , (λ n → refl-right-neutral (adjacent u n)))
        ⁻¹
      ∙ from-center (b , squares)

    initial : (v : Functional-Limit Stage r) (h : Alignment r u v) →
      aligned-center ＝ (v , h)
    initial v h =
      homotopy-induction (stage u) (stages (stage u))
        (λ g h′ → (b : (n : ℕ) → r n (g (suc n)) ＝ g n)
          (squares : Squares r u (limit g b) h′) →
          aligned-center ＝ (limit g b , alignment h′ squares))
        at-refl
        (stage v) (stage-path h) (adjacent v) (square h)

  opaque

    aligned-contraction : (v : Functional-Limit Stage r)
      (h : Alignment r u v) → aligned-center ＝ (v , h)
    aligned-contraction v h =
      initial u (from-path r refl) ⁻¹ ∙ initial v h

    aligned-contraction-at-center :
      aligned-contraction u (from-path r refl) ＝ refl
    aligned-contraction-at-center = left-inverse (initial u (from-path r refl))

  private
    recover : {v : Functional-Limit Stage r} {h : Alignment r u v}
      (p : aligned-center ＝ (v , h)) → from-path r (ap pr₁ p) ＝ h
    recover refl = refl

    evaluate : {v : Functional-Limit Stage r} {h : Alignment r u v}
      (p : aligned-center ＝ (v , h)) (n : ℕ) →
      ap (λ (w : Functional-Limit Stage r) → stage w n) (ap pr₁ p)
        ＝ stage-path h n
    evaluate refl n = refl

  exact-path : {v : Functional-Limit Stage r} → Alignment r u v → u ＝ v
  exact-path {v} h = ap pr₁ (aligned-contraction v h)

  exact-path-β : {v : Functional-Limit Stage r} (h : Alignment r u v)
    (n : ℕ) →
    ap (λ (w : Functional-Limit Stage r) → stage w n) (exact-path h)
      ＝ stage-path h n
  exact-path-β {v} h = evaluate (aligned-contraction v h)

  from-path-of-exact-path : {v : Functional-Limit Stage r}
    (h : Alignment r u v) → from-path r (exact-path h) ＝ h
  from-path-of-exact-path {v} h = recover (aligned-contraction v h)

  exact-path-of-from-path : {v : Functional-Limit Stage r} (p : u ＝ v) →
    exact-path (from-path r p) ＝ p
  exact-path-of-from-path refl = ap (ap pr₁) aligned-contraction-at-center

  identifications-are-alignments : (v : Functional-Limit Stage r) →
    (u ＝ v) ≅ Alignment r u v
  identifications-are-alignments v = record
    { forward = from-path r
    ; backward = exact-path
    ; backward-forward = exact-path-of-from-path
    ; forward-backward = from-path-of-exact-path
    }
