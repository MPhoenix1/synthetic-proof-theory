{-# OPTIONS --safe --without-K #-}

module SPT.OrdinalGeometry.Presentation.CountableOrdinal where

-- Presentations of countable ordinals, independent of any fixed notation
-- system (`Countable-Ordinal𝒫`): a well-founded strict linear order modulo
-- an equivalence, both type-valued, with a comparison and a partial ℕ
-- enumeration covering every point up to equivalence. The enumeration
-- returns the exact representative used at a successful index, so later
-- family constructions never select representatives from a quotient.
--
--   Countable-Ordinal𝒫 ℓ ≃ Σ X. Σ ≈ <. Equivalence ≈ × Transitive < ×
--     Respects < ≈ × WellFounded < × Trichotomy ≈ < ×
--     Σ e : ℕ → Maybe X. Π x. Σ n. Σ r. (e n ＝ just r) × (r ≈ x).
--
-- The module derives the laws of one presentation (`Presentation`), defines
-- bounded strict embeddings (`_≺𝒫_`) and their algebra (`Embedding`, with
-- `Embedding.wf`: ≺𝒫 is well-founded), the countable diagonal of a
-- ℕ-family (`Diagonal.𝒫`, strictly above every member) and equivalences of
-- presentations (`_≃𝒫_`). No ℕ-family covers all presentations, up to
-- identification (`Exact`), up to equivalence (`Shadow`) or cofinally
-- (`Cofinality`); the last is Regularity's theorem at the presentations,
-- which bound their ℕ-families by the diagonal
-- (`presentations-bound-families`). It ends with the ω₁ boundary, one
-- point above every presentation (`Boundary`), and the ω₁ geometry record
-- over it (`𝒫ω₁𝒢`, inhabited by `PresentedOmegaOne.Geometry.canonical`).

open import SPT.Base
open import SPT.Foundation.Accessibility using
  ( is-accessible; acc; accessible-induction; is-well-founded
  ; accessible-points-have-no-loops )
open import SPT.Foundation.WellFounded.Lexicographic using
  ( dependent-lexicographic; earlier; within
  ; dependent-lexicographic-is-transitive
  ; dependent-lexicographic-is-well-founded )
open import SPT.Foundation.Nat.Order using (_<ℕᶜ_; <ℕᶜ-trans; cmpℕᶜ)
open import SPT.Foundation.Nat.WellFounded using (wfℕᶜ)
open import SPT.OrdinalGeometry.Regularity using
  (Bounded-Families; no-family-is-cofinal)

------------------------------------------------------------------------
-- Presentations

-- A countable presentation of a well-founded strict linear order modulo a
-- retained equivalence. The partial enumeration permits empty and finite
-- carriers. Irreflexivity, asymmetry, the incompatibility of equivalence
-- with strictness, and extensionality by agreement of strict lower cones
-- are derived below. No quotient carrier, uniqueness of enumeration
-- indices, order-type identification or choice of representatives is
-- included.

record Countable-Ordinal𝒫 (ℓ : Level) : Set (lsuc ℓ) where
  infix 6 _≈_
  infix 30 _<_
  field
    X : Set ℓ
    _≈_ : X → X → Set ℓ
    _<_ : X → X → Set ℓ
    ≈-refl : (x : X) → x ≈ x
    ≈-sym : {x y : X} → x ≈ y → y ≈ x
    ≈-trans : {x y z : X} → x ≈ y → y ≈ z → x ≈ z
    <-trans : {x y z : X} → x < y → y < z → x < z
    <-respˡ-≈ : {x x′ y : X} → x ≈ x′ → x < y → x′ < y
    <-respʳ-≈ : {x y y′ : X} → y ≈ y′ → x < y → x < y′
    <-wf : is-well-founded _<_
    compare : (x y : X) → Trichotomy _≈_ _<_ x y
    enum : ℕ → Maybe X
    covers : (x : X) →
      Σ ℕ (λ n → Σ X (λ r → (enum n ＝ just r) × (r ≈ x)))

------------------------------------------------------------------------
-- Laws derived from the presentation data

module Presentation {ℓ : Level} (P : Countable-Ordinal𝒫 ℓ) where

  open Countable-Ordinal𝒫 P

  <-irrefl : (x : X) → ¬ (x < x)
  <-irrefl x = accessible-points-have-no-loops (<-wf x)

  <-asym : {x y : X} → x < y → ¬ (y < x)
  <-asym {x} x<y y<x = <-irrefl x (<-trans x<y y<x)

  ≈↛< : {x y : X} → x ≈ y → ¬ (x < y)
  ≈↛< {x} {y} x≈y x<y = <-irrefl y (<-respˡ-≈ x≈y x<y)

  -- Agreement of strict lower cones, pointwise in both directions:
  --
  --   x ≈↓ y = (Π z. z < x → z < y) × (Π z. z < y → z < x).

  infix 6 _≈↓_

  _≈↓_ : X → X → Set ℓ
  x ≈↓ y = ((z : X) → z < x → z < y) × ((z : X) → z < y → z < x)

  ≈↓→≈ : {x y : X} → x ≈↓ y → x ≈ y
  ≈↓→≈ {x} {y} (x→y , y→x) with compare x y
  ... | inl x<y = 𝟘-elim (<-irrefl x (y→x x x<y))
  ... | inr (inl x≈y) = x≈y
  ... | inr (inr y<x) = 𝟘-elim (<-irrefl y (x→y y y<x))

------------------------------------------------------------------------
-- Strict upper embeddings

-- A bounded order embedding of P into Q: a map preserving ≈ and <,
-- reflecting <, with a `ceiling` in Q strictly above its whole image.
--
--   P ≺𝒫 Q ≃ Σ to : |P| → |Q|. Preserves ≈ × Preserves < × Reflects < ×
--     Σ c : |Q|. Π x. to x <Q c.
--
-- No initial-segment law, least-ceiling law or identification of
-- presentation records is asserted.

infix 30 _≺𝒫_

record _≺𝒫_ {ℓ : Level} (P Q : Countable-Ordinal𝒫 ℓ) : Set ℓ where
  open Countable-Ordinal𝒫 P using ()
    renaming (X to X₁; _≈_ to infix 6 _≈₁_; _<_ to infix 30 _<₁_)
  open Countable-Ordinal𝒫 Q using ()
    renaming (X to X₂; _≈_ to infix 6 _≈₂_; _<_ to infix 30 _<₂_)
  field
    to : X₁ → X₂
    to-≈ : {x y : X₁} → x ≈₁ y → to x ≈₂ to y
    to-< : {x y : X₁} → x <₁ y → to x <₂ to y
    reflects-< : {x y : X₁} → to x <₂ to y → x <₁ y
    ceiling : X₂
    below : (x : X₁) → to x <₂ ceiling

------------------------------------------------------------------------
-- The lexicographic countable diagonal presentation

-- One successor block keeps a literal point of the indexed presentation or
-- its newly adjoined top. The family index determines the presentation
-- from which a `point` is drawn.

module Diagonal where

  module Successor {ℓ : Level} (P : ℕ → Countable-Ordinal𝒫 ℓ) (n : ℕ) where

    data Entry : Set ℓ where
      point : Countable-Ordinal𝒫.X (P n) → Entry
      top : Entry

    infix 6 _≈_
    infix 30 _<_

    data _≈_ : Entry → Entry → Set ℓ where
      point≈ : {x y : Countable-Ordinal𝒫.X (P n)} →
        Countable-Ordinal𝒫._≈_ (P n) x y → point x ≈ point y
      top≈ : top ≈ top

    data _<_ : Entry → Entry → Set ℓ where
      point< : {x y : Countable-Ordinal𝒫.X (P n)} →
        Countable-Ordinal𝒫._<_ (P n) x y → point x < point y
      point<top : {x : Countable-Ordinal𝒫.X (P n)} → point x < top

    ≈-refl : (x : Entry) → x ≈ x
    ≈-refl (point x) = point≈ (Countable-Ordinal𝒫.≈-refl (P n) x)
    ≈-refl top = top≈

    ≈-sym : {x y : Entry} → x ≈ y → y ≈ x
    ≈-sym (point≈ x≈y) = point≈ (Countable-Ordinal𝒫.≈-sym (P n) x≈y)
    ≈-sym top≈ = top≈

    ≈-trans : {x y z : Entry} → x ≈ y → y ≈ z → x ≈ z
    ≈-trans (point≈ x≈y) (point≈ y≈z) =
      point≈ (Countable-Ordinal𝒫.≈-trans (P n) x≈y y≈z)
    ≈-trans top≈ top≈ = top≈

    <-trans : {x y z : Entry} → x < y → y < z → x < z
    <-trans (point< x<y) (point< y<z) =
      point< (Countable-Ordinal𝒫.<-trans (P n) x<y y<z)
    <-trans (point< x<y) point<top = point<top

    <-respˡ-≈ : {x x′ y : Entry} → x ≈ x′ → x < y → x′ < y
    <-respˡ-≈ (point≈ x≈x′) (point< x<y) =
      point< (Countable-Ordinal𝒫.<-respˡ-≈ (P n) x≈x′ x<y)
    <-respˡ-≈ (point≈ x≈x′) point<top = point<top

    <-respʳ-≈ : {x y y′ : Entry} → y ≈ y′ → x < y → x < y′
    <-respʳ-≈ (point≈ y≈y′) (point< x<y) =
      point< (Countable-Ordinal𝒫.<-respʳ-≈ (P n) y≈y′ x<y)
    <-respʳ-≈ top≈ point<top = point<top

    compare : (x y : Entry) → Trichotomy _≈_ _<_ x y
    compare (point x) (point y) with Countable-Ordinal𝒫.compare (P n) x y
    ... | inl x<y = inl (point< x<y)
    ... | inr (inl x≈y) = inr (inl (point≈ x≈y))
    ... | inr (inr y<x) = inr (inr (point< y<x))
    compare (point x) top = inl point<top
    compare top (point y) = inr (inr point<top)
    compare top top = inr (inl top≈)

    point-accessible : {x : Countable-Ordinal𝒫.X (P n)} →
      is-accessible (Countable-Ordinal𝒫._<_ (P n)) x →
      is-accessible _<_ (point x)
    point-accessible (acc smaller) =
      acc λ where
        (point y) (point< y<x) → point-accessible (smaller y y<x)

    <-wf : is-well-founded _<_
    <-wf (point x) = point-accessible (Countable-Ordinal𝒫.<-wf (P n) x)
    <-wf top =
      acc λ where
        (point x) point<top →
          point-accessible (Countable-Ordinal𝒫.<-wf (P n) x)

  -- The dependent lexicographic sum of the successor blocks P n + 1,
  -- enumerated along the pairing of ℕ:
  --
  --   Diagonal.X P = Σ n : ℕ. |P n| + 1,
  --   (n , x) < (m , y) iff n < m, or n = m is the same block and x < y.
  --
  -- The block is kept literally by `same` and `within`: no transport between
  -- distinct members of the family, nor identification of family functions.

  module _ {ℓ : Level} (P : ℕ → Countable-Ordinal𝒫 ℓ) where

    X : Set ℓ
    X = Σ ℕ (Successor.Entry P)

    infix 6 _≈_
    infix 30 _<_

    data _≈_ : X → X → Set ℓ where
      same : {n : ℕ} {x y : Successor.Entry P n} →
        Successor._≈_ P n x y → (n , x) ≈ (n , y)

    _<_ : X → X → Set ℓ
    _<_ =
      dependent-lexicographic (Successor.Entry P) _<ℕᶜ_ (Successor._<_ P)

    ≈-refl : (x : X) → x ≈ x
    ≈-refl (n , x) = same (Successor.≈-refl P n x)

    ≈-sym : {x y : X} → x ≈ y → y ≈ x
    ≈-sym (same {n} x≈y) = same (Successor.≈-sym P n x≈y)

    ≈-trans : {x y z : X} → x ≈ y → y ≈ z → x ≈ z
    ≈-trans (same {n} x≈y) (same y≈z) = same (Successor.≈-trans P n x≈y y≈z)

    <-trans : {x y z : X} → x < y → y < z → x < z
    <-trans =
      dependent-lexicographic-is-transitive (Successor.Entry P) _<ℕᶜ_
        (Successor._<_ P) (λ {a} {b} {c} a<b b<c → <ℕᶜ-trans a b c a<b b<c)
        (Successor.<-trans P)

    <-respˡ-≈ : {x x′ y : X} → x ≈ x′ → x < y → x′ < y
    <-respˡ-≈ (same x≈x′) (earlier m<n) = earlier m<n
    <-respˡ-≈ (same x≈x′) (within n x<y) =
      within n (Successor.<-respˡ-≈ P n x≈x′ x<y)

    <-respʳ-≈ : {x y y′ : X} → y ≈ y′ → x < y → x < y′
    <-respʳ-≈ (same y≈y′) (earlier m<n) = earlier m<n
    <-respʳ-≈ (same y≈y′) (within n x<y) =
      within n (Successor.<-respʳ-≈ P n y≈y′ x<y)

    compare : (x y : X) → Trichotomy _≈_ _<_ x y
    compare (m , x) (n , y) with cmpℕᶜ m n
    ... | inl m<n = inl (earlier m<n)
    ... | inr (inr n<m) = inr (inr (earlier n<m))
    ... | inr (inl refl) with Successor.compare P m x y
    ...   | inl x<y = inl (within m x<y)
    ...   | inr (inl x≈y) = inr (inl (same x≈y))
    ...   | inr (inr y<x) = inr (inr (within m y<x))

    <-wf : is-well-founded _<_
    <-wf =
      dependent-lexicographic-is-well-founded (Successor.Entry P) _<ℕᶜ_
        (Successor._<_ P) wfℕᶜ (Successor.<-wf P)

    -- The entry at a block index and an index inside the block: the top at
    -- zero, and the enumerated point of P n at a successor.
    point-entry : (n : ℕ) → Maybe (Countable-Ordinal𝒫.X (P n)) → Maybe X
    point-entry n nothing = nothing
    point-entry n (just x) = just (n , Successor.point x)

    block-entry : ℕ → ℕ → Maybe X
    block-entry n zero = just (n , Successor.top)
    block-entry n (suc i) =
      point-entry n (Countable-Ordinal𝒫.enum (P n) i)

    enum : ℕ → Maybe X
    enum code = block-entry (pr₁ (ℕ-unpair code)) (pr₂ (ℕ-unpair code))

    enum-top : (n : ℕ) → enum (ℕ-pair n zero) ＝ just (n , Successor.top)
    enum-top n =
      ap (λ u → block-entry (pr₁ u) (pr₂ u)) (ℕ-unpair-pair n zero)

    enum-point : (n i : ℕ) (x : Countable-Ordinal𝒫.X (P n)) →
      Countable-Ordinal𝒫.enum (P n) i ＝ just x →
      enum (ℕ-pair n (suc i)) ＝ just (n , Successor.point x)
    enum-point n i x selected =
      ap (λ u → block-entry (pr₁ u) (pr₂ u)) (ℕ-unpair-pair n (suc i)) ∙
      ap (point-entry n) selected

    covers : (x : X) →
      Σ ℕ (λ code → Σ X (λ r → (enum code ＝ just r) × (r ≈ x)))
    covers (n , Successor.top) =
      ℕ-pair n zero , (n , Successor.top) , enum-top n , same Successor.top≈
    covers (n , Successor.point x)
      with Countable-Ordinal𝒫.covers (P n) x
    ... | i , r , selected , r≈x =
      ℕ-pair n (suc i) , (n , Successor.point r) , enum-point n i r selected ,
      same (Successor.point≈ r≈x)

    -- The exact countable presentation of the lexicographic sum of the
    -- successor blocks P n + 1.

    𝒫 : Countable-Ordinal𝒫 ℓ
    𝒫 = record
      { X = X
      ; _≈_ = _≈_
      ; _<_ = _<_
      ; ≈-refl = ≈-refl
      ; ≈-sym = ≈-sym
      ; ≈-trans = ≈-trans
      ; <-trans = <-trans
      ; <-respˡ-≈ = <-respˡ-≈
      ; <-respʳ-≈ = <-respʳ-≈
      ; <-wf = <-wf
      ; compare = compare
      ; enum = enum
      ; covers = covers
      }

    module _ (n : ℕ) where

      reflects : {x y : Countable-Ordinal𝒫.X (P n)} →
        (n , Successor.point x) < (n , Successor.point y) →
        Countable-Ordinal𝒫._<_ (P n) x y
      reflects {x} {y} embedded with Countable-Ordinal𝒫.compare (P n) x y
      ... | inl x<y = x<y
      ... | inr (inl x≈y) =
        𝟘-elim
          (Presentation.≈↛< 𝒫 (same (Successor.point≈ x≈y)) embedded)
      ... | inr (inr y<x) =
        𝟘-elim
          (Presentation.<-asym 𝒫 embedded
            (within n (Successor.point< y<x)))

      member : P n ≺𝒫 𝒫
      member = record
        { to = λ x → n , Successor.point x
        ; to-≈ = λ x≈y → same (Successor.point≈ x≈y)
        ; to-< = λ x<y → within n (Successor.point< x<y)
        ; reflects-< = reflects
        ; ceiling = n , Successor.top
        ; below = λ x → within n Successor.point<top
        }

    -- A strict upper presentation of the family P, with no choice.

    Upper : Set (lsuc ℓ)
    Upper = Σ (Countable-Ordinal𝒫 ℓ) (λ Q → (n : ℕ) → P n ≺𝒫 Q)

    upper : Upper
    upper = 𝒫 , member

------------------------------------------------------------------------
-- Strict-upper embedding algebra

module Embedding where

  open _≺𝒫_ public

  -- The composite takes the image in R of the inner ceiling as its own
  -- ceiling. This is the exact bound used by `wf` below.

  trans : {ℓ : Level} {P Q R : Countable-Ordinal𝒫 ℓ} →
    P ≺𝒫 Q → Q ≺𝒫 R → P ≺𝒫 R
  trans e₁ e₂ = record
    { to = λ x → to e₂ (to e₁ x)
    ; to-≈ = λ x≈y → to-≈ e₂ (to-≈ e₁ x≈y)
    ; to-< = λ x<y → to-< e₂ (to-< e₁ x<y)
    ; reflects-< = λ tox<toy → reflects-< e₁ (reflects-< e₂ tox<toy)
    ; ceiling = to e₂ (ceiling e₁)
    ; below = λ x → to-< e₂ (below e₁ x)
    }

  -- A predecessor P ≺𝒫 Q supplies its own ceiling in Q; recursion starts at
  -- that literal point, and composite ceilings decrease inside Q.

  accessible-from-ceiling : {ℓ : Level} {P Q : Countable-Ordinal𝒫 ℓ}
    (e : P ≺𝒫 Q) →
    is-accessible (Countable-Ordinal𝒫._<_ Q) (ceiling e) →
    is-accessible (_≺𝒫_ {ℓ}) P
  accessible-from-ceiling e (acc smaller) =
    acc λ R R≺P →
      accessible-from-ceiling (trans R≺P e)
        (smaller (to e (ceiling R≺P)) (below e (ceiling R≺P)))

  wf : {ℓ : Level} → is-well-founded (_≺𝒫_ {ℓ})
  wf Q =
    acc λ P P≺Q →
      accessible-from-ceiling P≺Q (Countable-Ordinal𝒫.<-wf Q (ceiling P≺Q))

  self↛descending : {ℓ : Level} {P : Countable-Ordinal𝒫 ℓ}
    (e : P ≺𝒫 P) (x : Countable-Ordinal𝒫.X P) →
    ¬ (Countable-Ordinal𝒫._<_ P (to e x) x)
  self↛descending {ℓ} {P} e x =
    accessible-induction
      (λ y → ¬ (Countable-Ordinal𝒫._<_ P (to e y) y))
      (λ y smaller toy<y → smaller (to e y) toy<y (to-< e toy<y))
      x (Countable-Ordinal𝒫.<-wf P x)

  irrefl : {ℓ : Level} (P : Countable-Ordinal𝒫 ℓ) → ¬ (P ≺𝒫 P)
  irrefl P e = self↛descending e (ceiling e) (below e (ceiling e))

------------------------------------------------------------------------
-- Equivalence of complete presentations

-- Two complete presentations may present the same linear order without
-- their carriers, relations, enumerations or fields being identified:
--
--   P ≃𝒫 Q ≃ Σ f : |P| → |Q|. Σ g : |Q| → |P|. f and g preserve ≈ and < ×
--     (Π x. g (f x) ≈P x) × (Π y. f (g y) ≈Q y).
--
-- The inverse laws are pointwise ≈-witnesses, never identifications of
-- functions; both maps and both round trips stay available. No quotient
-- carrier, univalence, identification of presentation records, canonical
-- normal form or initial-segment identification is constructed.

infix 5 _≃𝒫_

record _≃𝒫_ {ℓ : Level} (P Q : Countable-Ordinal𝒫 ℓ) : Set ℓ where
  open Countable-Ordinal𝒫 P using ()
    renaming (X to X₁; _≈_ to infix 6 _≈₁_; _<_ to infix 30 _<₁_)
  open Countable-Ordinal𝒫 Q using ()
    renaming (X to X₂; _≈_ to infix 6 _≈₂_; _<_ to infix 30 _<₂_)
  field
    to : X₁ → X₂
    from : X₂ → X₁
    to-≈ : {x y : X₁} → x ≈₁ y → to x ≈₂ to y
    from-≈ : {x y : X₂} → x ≈₂ y → from x ≈₁ from y
    to-< : {x y : X₁} → x <₁ y → to x <₂ to y
    from-< : {x y : X₂} → x <₂ y → from x <₁ from y
    from-to-≈ : (x : X₁) → from (to x) ≈₁ x
    to-from-≈ : (y : X₂) → to (from y) ≈₂ y

open _≃𝒫_ public

≃𝒫-refl : {ℓ : Level} (P : Countable-Ordinal𝒫 ℓ) → P ≃𝒫 P
≃𝒫-refl P = record
  { to = λ x → x
  ; from = λ x → x
  ; to-≈ = λ x≈y → x≈y
  ; from-≈ = λ x≈y → x≈y
  ; to-< = λ x<y → x<y
  ; from-< = λ x<y → x<y
  ; from-to-≈ = Countable-Ordinal𝒫.≈-refl P
  ; to-from-≈ = Countable-Ordinal𝒫.≈-refl P
  }

≃𝒫-sym : {ℓ : Level} {P Q : Countable-Ordinal𝒫 ℓ} → P ≃𝒫 Q → Q ≃𝒫 P
≃𝒫-sym e = record
  { to = from e
  ; from = to e
  ; to-≈ = from-≈ e
  ; from-≈ = to-≈ e
  ; to-< = from-< e
  ; from-< = to-< e
  ; from-to-≈ = to-from-≈ e
  ; to-from-≈ = from-to-≈ e
  }

≃𝒫-trans : {ℓ : Level} {P Q R : Countable-Ordinal𝒫 ℓ} →
  P ≃𝒫 Q → Q ≃𝒫 R → P ≃𝒫 R
≃𝒫-trans {ℓ} {P} {Q} {R} e₁ e₂ = record
  { to = λ x → to e₂ (to e₁ x)
  ; from = λ x → from e₁ (from e₂ x)
  ; to-≈ = λ x≈y → to-≈ e₂ (to-≈ e₁ x≈y)
  ; from-≈ = λ x≈y → from-≈ e₁ (from-≈ e₂ x≈y)
  ; to-< = λ x<y → to-< e₂ (to-< e₁ x<y)
  ; from-< = λ x<y → from-< e₁ (from-< e₂ x<y)
  ; from-to-≈ = λ x →
      Countable-Ordinal𝒫.≈-trans P
        (from-≈ e₁ (from-to-≈ e₂ (to e₁ x))) (from-to-≈ e₁ x)
  ; to-from-≈ = λ y →
      Countable-Ordinal𝒫.≈-trans R
        (to-≈ e₂ (to-from-≈ e₁ (from e₂ y))) (to-from-≈ e₂ y)
  }

module _ {ℓ : Level} {P Q : Countable-Ordinal𝒫 ℓ} where

  open Countable-Ordinal𝒫 P using ()
    renaming (X to X₁; _<_ to infix 30 _<₁_)
  open Countable-Ordinal𝒫 Q using ()
    renaming (X to X₂; _<_ to infix 30 _<₂_)

  ≃𝒫-to-reflects-< : (e : P ≃𝒫 Q) {x y : X₁} → to e x <₂ to e y → x <₁ y
  ≃𝒫-to-reflects-< e {x} {y} tox<toy =
    Countable-Ordinal𝒫.<-respʳ-≈ P (from-to-≈ e y)
      (Countable-Ordinal𝒫.<-respˡ-≈ P (from-to-≈ e x) (from-< e tox<toy))

  ≃𝒫-from-reflects-< : (e : P ≃𝒫 Q) {x y : X₂} →
    from e x <₁ from e y → x <₂ y
  ≃𝒫-from-reflects-< e {x} {y} fromx<fromy =
    Countable-Ordinal𝒫.<-respʳ-≈ Q (to-from-≈ e y)
      (Countable-Ordinal𝒫.<-respˡ-≈ Q (to-from-≈ e x) (to-< e fromx<fromy))

-- An equivalence P ≃𝒫 Q followed by a bounded embedding P ≺𝒫 Q closes to a
-- bounded self-embedding of Q: back through the equivalence, then forward
-- through the embedding. The reflection of < by the backward map is derived
-- pointwise above, so no identification of inverse functions is needed.

≃𝒫→self≺𝒫 : {ℓ : Level} {P Q : Countable-Ordinal𝒫 ℓ} →
  P ≃𝒫 Q → P ≺𝒫 Q → Q ≺𝒫 Q
≃𝒫→self≺𝒫 e bounded = record
  { to = λ x → Embedding.to bounded (from e x)
  ; to-≈ = λ x≈y → Embedding.to-≈ bounded (from-≈ e x≈y)
  ; to-< = λ x<y → Embedding.to-< bounded (from-< e x<y)
  ; reflects-< = λ tox<toy →
      ≃𝒫-from-reflects-< e (Embedding.reflects-< bounded tox<toy)
  ; ceiling = Embedding.ceiling bounded
  ; below = λ x → Embedding.below bounded (from e x)
  }

≃𝒫↛≺𝒫 : {ℓ : Level} {P Q : Countable-Ordinal𝒫 ℓ} →
  P ≃𝒫 Q → ¬ (P ≺𝒫 Q)
≃𝒫↛≺𝒫 {ℓ} {P} {Q} e bounded = Embedding.irrefl Q (≃𝒫→self≺𝒫 e bounded)

------------------------------------------------------------------------
-- No enumeration of all presentations

-- Exact coverage identifies complete presentation records, with their
-- carrier, relations, laws and enumeration.

module Exact where

  Covers : {ℓ : Level} → (ℕ → Countable-Ordinal𝒫 ℓ) → Set (lsuc ℓ)
  Covers {ℓ} F = (P : Countable-Ordinal𝒫 ℓ) → Σ ℕ (λ n → F n ＝ P)

  no-enumeration : {ℓ : Level} →
    ¬ (Σ (ℕ → Countable-Ordinal𝒫 ℓ) Covers)
  no-enumeration (F , covers) with Diagonal.upper F
  ... | Q , F≺Q with covers Q
  ... | n , Fₙ≡Q =
    Embedding.irrefl Q (transport (λ P → P ≺𝒫 Q) Fₙ≡Q (F≺Q n))

-- `Shadow.Covers F` disregards duplicate records only through supplied
-- equivalences of presentations. It constructs no quotient or separate
-- carrier.

module Shadow where

  Covers : {ℓ : Level} → (ℕ → Countable-Ordinal𝒫 ℓ) → Set (lsuc ℓ)
  Covers {ℓ} F = (P : Countable-Ordinal𝒫 ℓ) → Σ ℕ (λ n → F n ≃𝒫 P)

  no-enumeration : {ℓ : Level} →
    ¬ (Σ (ℕ → Countable-Ordinal𝒫 ℓ) Covers)
  no-enumeration (F , covers) with Diagonal.upper F
  ... | Q , F≺Q with covers Q
  ... | n , Fₙ≃Q = ≃𝒫↛≺𝒫 Fₙ≃Q (F≺Q n)

------------------------------------------------------------------------
-- Exact presentation-relative cofinality

infix 30 _≼𝒫_

_≼𝒫_ : {ℓ : Level} → Countable-Ordinal𝒫 ℓ → Countable-Ordinal𝒫 ℓ →
  Set (lsuc ℓ)
P ≼𝒫 Q = (P ＝ Q) ⊎ (P ≺𝒫 Q)

-- A strict bound followed by an identification or a strict bound is a
-- strict bound.
≺𝒫-≼𝒫-trans : {ℓ : Level} {P Q R : Countable-Ordinal𝒫 ℓ} →
  P ≺𝒫 Q → Q ≼𝒫 R → P ≺𝒫 R
≺𝒫-≼𝒫-trans e (inl refl) = e
≺𝒫-≼𝒫-trans e (inr f) = Embedding.trans e f

-- The presentations of level ℓ with the ℕ-indexed families, the presented
-- ω₁: an instance of Regularity, the countable diagonal of a family as its
-- bound.
presentations-bound-families : {ℓ : Level} →
  Bounded-Families (Countable-Ordinal𝒫 ℓ) _≺𝒫_ _≼𝒫_ 𝟙 (λ _ → ℕ)
presentations-bound-families = record
  { strict-is-irreflexive = Embedding.irrefl
  ; strict-then-weak = ≺𝒫-≼𝒫-trans
  ; upper-bound = λ _ F → Diagonal.upper F
  }

module Cofinality where

  Covers : {ℓ : Level} → (ℕ → Countable-Ordinal𝒫 ℓ) → Set (lsuc ℓ)
  Covers {ℓ} F = (P : Countable-Ordinal𝒫 ℓ) → Σ ℕ (λ n → P ≼𝒫 F n)

  -- No ℕ-family is cofinal: Regularity at the presentations.
  no-family : {ℓ : Level} → ¬ (Σ (ℕ → Countable-Ordinal𝒫 ℓ) Covers)
  no-family (F , cofinal) =
    no-family-is-cofinal presentations-bound-families ⋆ F cofinal

------------------------------------------------------------------------
-- The ω₁ boundary

-- The presentations of level ℓ and one point above all of them, with one
-- strict relation, embed P < boundary:
--
--   Point ℓ = Countable-Ordinal𝒫 ℓ + 1,   Strict (embed P) boundary.
--
-- Every strict predecessor of the boundary is an embedded presentation
-- (`spectrum`), so Σ x. x < boundary is the type of all presentations.

module Boundary where

  data Point (ℓ : Level) : Set (lsuc ℓ) where
    embed : Countable-Ordinal𝒫 ℓ → Point ℓ
    boundary : Point ℓ

  data Strict {ℓ : Level} : Point ℓ → Point ℓ → Set (lsuc ℓ) where
    below : (P : Countable-Ordinal𝒫 ℓ) → Strict (embed P) boundary

  spectrum : {ℓ : Level} {predecessor : Point ℓ} →
    Strict predecessor boundary →
    Σ (Countable-Ordinal𝒫 ℓ) (λ P → predecessor ＝ embed P)
  spectrum (below P) = P , refl

  -- A point above every embedded presentation; `upper` is `boundary`.

  Upper : (ℓ : Level) → Set (lsuc ℓ)
  Upper ℓ =
    Σ (Point ℓ) (λ upper → (P : Countable-Ordinal𝒫 ℓ) → Strict (embed P) upper)

  upper : {ℓ : Level} → Upper ℓ
  upper = boundary , below

------------------------------------------------------------------------
-- Presented omega-one geometry

-- An ω₁ geometry at level ℓ: a point above every presentation, whose strict
-- predecessors are exactly the embedded presentations, with the diagonal
-- and the impossibility of enumerating presentations:
--
--   𝒫ω₁𝒢 ℓ = Boundary.Upper ℓ × Π (x < upper). Σ P. x ＝ embed P
--     × Π (f : ℕ → Countable-Ordinal𝒫 ℓ). Diagonal.Upper f
--     × ¬ Σ f. Shadow.Covers f.
--
-- `PresentedOmegaOne.Geometry.canonical` inhabits it. It is data, not a
-- well-order; the order is built from its positions in the Cubical
-- reflection.

record 𝒫ω₁𝒢 (ℓ : Level) : Set (lsuc ℓ) where
  field
    upper : Boundary.Upper ℓ
    spectrum : {predecessor : Boundary.Point ℓ} →
      Boundary.Strict predecessor (pr₁ upper) →
      Σ (Countable-Ordinal𝒫 ℓ) (λ P → predecessor ＝ Boundary.embed P)
    diagonal : (F : ℕ → Countable-Ordinal𝒫 ℓ) → Diagonal.Upper F
    no-cover : ¬ (Σ (ℕ → Countable-Ordinal𝒫 ℓ) Shadow.Covers)

module PresentedOmegaOne where

  module Geometry where

    canonical : {ℓ : Level} → 𝒫ω₁𝒢 ℓ
    canonical = record
      { upper = Boundary.upper
      ; spectrum = Boundary.spectrum
      ; diagonal = Diagonal.upper
      ; no-cover = Shadow.no-enumeration
      }

    -- The predecessors of the upper point of a geometry are exactly the
    -- embedded presentations:
    --
    --   x < upper G ⇔ Σ P. x ＝ embed P.
    --
    -- The forward map is stored by the geometry; the reverse map transports
    -- the route of P along the given identification of endpoints. Neither
    -- map identifies presentations or routes.

    spectrum : {ℓ : Level} (geometry : 𝒫ω₁𝒢 ℓ)
      (predecessor : Boundary.Point ℓ) →
      (Boundary.Strict predecessor (pr₁ (𝒫ω₁𝒢.upper geometry)) →
        Σ (Countable-Ordinal𝒫 ℓ) (λ P → predecessor ＝ Boundary.embed P))
      ×
      (Σ (Countable-Ordinal𝒫 ℓ) (λ P → predecessor ＝ Boundary.embed P) →
        Boundary.Strict predecessor (pr₁ (𝒫ω₁𝒢.upper geometry)))
    spectrum geometry predecessor =
      𝒫ω₁𝒢.spectrum geometry ,
      λ where
        (P , predecessor-computes) →
          transport
            (λ source →
              Boundary.Strict source (pr₁ (𝒫ω₁𝒢.upper geometry)))
            (predecessor-computes ⁻¹)
            (pr₂ (𝒫ω₁𝒢.upper geometry) P)

    --------------------------------------------------------------------
    -- Complete positions

    upper : {ℓ : Level} → 𝒫ω₁𝒢 ℓ → Boundary.Point ℓ
    upper geometry = pr₁ (𝒫ω₁𝒢.upper geometry)

    -- A position keeps the literal presentation with its exact route into
    -- the upper boundary; the presentation is never recovered from the
    -- route's endpoint.
    --
    --   Position G = Σ P : Countable-Ordinal𝒫 ℓ. embed P < upper G.
    --
    -- No identification of routes, uniqueness of the presentation at an
    -- endpoint, or ordinal comparison of routes is asserted.

    Position : {ℓ : Level} → 𝒫ω₁𝒢 ℓ → Set (lsuc ℓ)
    Position {ℓ} geometry =
      Σ (Countable-Ordinal𝒫 ℓ)
        (λ P → Boundary.Strict (Boundary.embed P) (upper geometry))

    position : {ℓ : Level} (geometry : 𝒫ω₁𝒢 ℓ) (P : Countable-Ordinal𝒫 ℓ) →
      Position geometry
    position geometry P = P , pr₂ (𝒫ω₁𝒢.upper geometry) P

    -- Every predecessor of the upper point is the endpoint of a position:
    --
    --   x < upper G → Σ q : Position G. x ＝ embed (pr₁ q).
    --
    -- The given route is transported once along the endpoint classification
    -- of the geometry; it is not discarded and rebuilt from the selected
    -- presentation.

    covers : {ℓ : Level} (geometry : 𝒫ω₁𝒢 ℓ)
      {predecessor : Boundary.Point ℓ} →
      Boundary.Strict predecessor (upper geometry) →
      Σ (Position geometry)
        (λ position → predecessor ＝ Boundary.embed (pr₁ position))
    covers geometry predecessor<upper
      with 𝒫ω₁𝒢.spectrum geometry predecessor<upper
    ... | P , predecessor-computes =
      (P ,
        transport (λ source → Boundary.Strict source (upper geometry))
          predecessor-computes predecessor<upper) ,
      predecessor-computes
