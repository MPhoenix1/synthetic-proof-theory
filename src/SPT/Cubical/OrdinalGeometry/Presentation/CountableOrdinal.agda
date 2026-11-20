{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal where

-- Presentations of countable ordinals: a well-founded strict linear order
-- modulo an equivalence, both type-valued, with a comparison function and a
-- partial enumeration covering every point up to equivalence.  Bounded
-- strict embeddings and their well-foundedness, the countable diagonal,
-- equivalence of presentations, the impossibility of enumerating all
-- presentations, and the ω₁ geometry: one point above every presentation.

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Accessibility using
  ( acc; accessible-induction; accessible-points-have-no-loops; is-accessible
  ; is-well-founded )
open import SPT.Cubical.Foundation.Nat.Order using (_<ℕᶜ_; <ℕᶜ-trans; cmpℕᶜ)
open import SPT.Cubical.Foundation.Nat.WellFounded using (wfℕᶜ)
open import SPT.Cubical.Foundation.WellFounded.Lexicographic using
  ( dependent-lexicographic; earlier; within
  ; dependent-lexicographic-is-transitive
  ; dependent-lexicographic-is-well-founded )

------------------------------------------------------------------------
-- Presentations

-- A presentation at level ℓ:
--
--   CountableOrdinal𝒫(ℓ)
--     ≃ Σ(X : Set ℓ). Σ(≈ < : X → X → Set ℓ).
--         Equivalence(≈) × Transitive(<) × Respects₂(<,≈) × WellFounded(<)
--       × (Π x y. x < y + (x ≈ y + y < x))
--       × Σ(e : ℕ → Maybe X). Π x. Σ n. Σ r. (e(n) = just(r)) × (r ≈ x).
--
-- Both relations are type-valued; nothing is quotiented.  The enumeration
-- is partial, so empty and finite presentations need no default point, and
-- `covers` returns an index and the representative found there.
-- Irreflexivity, asymmetry and extensionality modulo ≈ are derived below.

record CountableOrdinal𝒫 (ℓ : Level) : Set (lsuc ℓ) where

  infix 6 _≈_
  infix 30 _<_

  field

    X : Set ℓ

    _≈_ : X → X → Set ℓ

    _<_ : X → X → Set ℓ

    ≈-refl :
      (x : X) → x ≈ x

    ≈-sym :
      ∀ {x y}
      → x ≈ y
      → y ≈ x

    ≈-trans :
      ∀ {x y z}
      → x ≈ y
      → y ≈ z
      → x ≈ z

    <-trans :
      ∀ {x y z}
      → x < y
      → y < z
      → x < z

    <-respˡ-≈ :
      ∀ {x x′ y}
      → x ≈ x′
      → x < y
      → x′ < y

    <-respʳ-≈ :
      ∀ {x y y′}
      → y ≈ y′
      → x < y
      → x < y′

    <-wf :
      is-well-founded _<_

    compare :
      (x y : X)
      → Trichotomy _≈_ _<_ x y

    enum :
      ℕ → Maybe X

    covers :
      (x : X)
      → Σ ℕ λ n →
          Σ X λ r →
            (enum n ＝ just r)
            × (r ≈ x)

------------------------------------------------------------------------
-- Derived laws

module Presentation {ℓ : Level} (P : CountableOrdinal𝒫 ℓ) where

  open CountableOrdinal𝒫 P

  <-irrefl :
      (x : X)
    → ¬ x < x
  <-irrefl x =
    accessible-points-have-no-loops (<-wf x)

  <-asym :
      ∀ {x y}
    → x < y
    → ¬ y < x
  <-asym x<y y<x =
    <-irrefl _ (<-trans x<y y<x)

  ≈↛< :
      ∀ {x y}
    → x ≈ y
    → ¬ x < y
  ≈↛< x≈y x<y =
    <-irrefl _ (<-respˡ-≈ x≈y x<y)

  -- Agreement of strict lower cones,
  --
  --   x ≈↓ y = (Π z. z < x → z < y) × (Π z. z < y → z < x),
  --
  -- implies x ≈ y (`≈↓→≈`), by `compare`.

  infix 6 _≈↓_

  _≈↓_ : X → X → Set ℓ
  x ≈↓ y =
    ((z : X) → z < x → z < y)
    ×
    ((z : X) → z < y → z < x)

  ≈↓→≈ :
      ∀ {x y}
    → x ≈↓ y
    → x ≈ y
  ≈↓→≈ {x} {y} (x→y , y→x)
      with compare x y
  ... | inl x<y =
    𝟘-elim (<-irrefl x (y→x x x<y))
  ... | inr (inl x≈y) =
    x≈y
  ... | inr (inr y<x) =
    𝟘-elim (<-irrefl y (x→y y y<x))

------------------------------------------------------------------------
-- Bounded strict embeddings

-- A bounded strict embedding P ≺𝒫 Q: an order embedding modulo ≈ together
-- with a ceiling in Q above its whole image,
--
--   P ≺𝒫 Q ≃ Σ(to : |P| → |Q|). Preserves≈(to) × Preserves<(to)
--              × Reflects<(to) × Σ(c : |Q|). Π x. to(x) <Q c.
--
-- The image need not be downward closed.

infix 30 _≺𝒫_

record _≺𝒫_
    {ℓ : Level}
    (P Q : CountableOrdinal𝒫 ℓ)
    : Set ℓ where

  private
    module P′ = CountableOrdinal𝒫 P
    module Q′ = CountableOrdinal𝒫 Q

  field

    to :
      P′.X → Q′.X

    to-≈ :
      ∀ {x y}
      → x P′.≈ y
      → to x Q′.≈ to y

    to-< :
      ∀ {x y}
      → x P′.< y
      → to x Q′.< to y

    reflects-< :
      ∀ {x y}
      → to x Q′.< to y
      → x P′.< y

    ceiling :
      Q′.X

    below :
      (x : P′.X)
      → to x Q′.< ceiling

------------------------------------------------------------------------
-- The countable diagonal

-- For a family P : ℕ → CountableOrdinal𝒫 ℓ, the ordered sum of the
-- successors P(n) + 1.  Each P(n) embeds into it below the new top point of
-- its block, so the sum bounds the whole family (`upper`).

module Diagonal where

  module Successor
      {ℓ : Level}
      (P : ℕ → CountableOrdinal𝒫 ℓ)
      (n : ℕ)
    where

    private
      module Pₙ = CountableOrdinal𝒫 (P n)

    data Entry : Set ℓ where

      point :
          Pₙ.X
        → Entry

      top :
        Entry

    infix 6 _≈_
    infix 30 _<_

    data _≈_ : Entry → Entry → Set ℓ where

      point≈ :
          ∀ {x y}
        → x Pₙ.≈ y
        → point x ≈ point y

      top≈ :
        top ≈ top

    data _<_ : Entry → Entry → Set ℓ where

      point< :
          ∀ {x y}
        → x Pₙ.< y
        → point x < point y

      point<top :
          ∀ {x}
        → point x < top

    ≈-refl :
        (x : Entry)
      → x ≈ x
    ≈-refl (point x) =
      point≈ (Pₙ.≈-refl x)
    ≈-refl top =
      top≈

    ≈-sym :
        ∀ {x y}
      → x ≈ y
      → y ≈ x
    ≈-sym (point≈ x≈y) =
      point≈ (Pₙ.≈-sym x≈y)
    ≈-sym top≈ =
      top≈

    ≈-trans :
        ∀ {x y z}
      → x ≈ y
      → y ≈ z
      → x ≈ z
    ≈-trans (point≈ x≈y) (point≈ y≈z) =
      point≈ (Pₙ.≈-trans x≈y y≈z)
    ≈-trans top≈ top≈ =
      top≈

    <-trans :
        ∀ {x y z}
      → x < y
      → y < z
      → x < z
    <-trans (point< x<y) (point< y<z) =
      point< (Pₙ.<-trans x<y y<z)
    <-trans (point< x<y) point<top =
      point<top

    <-respˡ-≈ :
        ∀ {x x′ y}
      → x ≈ x′
      → x < y
      → x′ < y
    <-respˡ-≈ (point≈ x≈x′) (point< x<y) =
      point< (Pₙ.<-respˡ-≈ x≈x′ x<y)
    <-respˡ-≈ (point≈ x≈x′) point<top =
      point<top

    <-respʳ-≈ :
        ∀ {x y y′}
      → y ≈ y′
      → x < y
      → x < y′
    <-respʳ-≈ (point≈ y≈y′) (point< x<y) =
      point< (Pₙ.<-respʳ-≈ y≈y′ x<y)
    <-respʳ-≈ top≈ point<top =
      point<top

    compare :
        (x y : Entry)
      → Trichotomy _≈_ _<_ x y
    compare (point x) (point y)
        with Pₙ.compare x y
    ... | inl x<y =
      inl (point< x<y)
    ... | inr (inl x≈y) =
      inr (inl (point≈ x≈y))
    ... | inr (inr y<x) =
      inr (inr (point< y<x))
    compare (point x) top =
      inl point<top
    compare top (point y) =
      inr (inr point<top)
    compare top top =
      inr (inl top≈)

    private
      point-acc :
          ∀ {x}
        → is-accessible Pₙ._<_ x
        → is-accessible _<_ (point x)
      point-acc (acc smaller) =
        acc λ where
          (point y) (point< y<x) →
            point-acc (smaller y y<x)

    <-wf : is-well-founded _<_
    <-wf (point x) =
      point-acc (Pₙ.<-wf x)
    <-wf top =
      acc λ where
        (point x) point<top →
          point-acc (Pₙ.<-wf x)

-- The sum Σ(n : ℕ). (P(n) + 1), ordered lexicographically: first by block,
-- then within a block.  Its enumeration interleaves the blocks through a
-- pairing of ℕ × ℕ with ℕ.

  module _
      {ℓ : Level}
      (P : ℕ → CountableOrdinal𝒫 ℓ)
    where

    X : Set ℓ
    X = Σ ℕ (Successor.Entry P)

    infix 6 _≈⁺_ _≈_
    infix 30 _<⁺_ _<_

    private
      _≈⁺_ :
          ∀ {n}
        → Successor.Entry P n
        → Successor.Entry P n
        → Set ℓ
      _≈⁺_ {n} =
        Successor._≈_ P n

      _<⁺_ :
          ∀ {n}
        → Successor.Entry P n
        → Successor.Entry P n
        → Set ℓ
      _<⁺_ {n} =
        Successor._<_ P n

    data _≈_ : X → X → Set ℓ where

      same :
          ∀ {n} {x y : Successor.Entry P n}
        → x ≈⁺ y
        → (n , x) ≈ (n , y)

    _<_ : X → X → Set ℓ
    _<_ =
      dependent-lexicographic
        (Successor.Entry P)
        _<ℕᶜ_
        (λ n → Successor._<_ P n)

    ≈-refl :
        (x : X)
      → x ≈ x
    ≈-refl (n , x) =
      same (Successor.≈-refl P n x)

    ≈-sym :
        ∀ {x y}
      → x ≈ y
      → y ≈ x
    ≈-sym (same x≈y) =
      same (Successor.≈-sym P _ x≈y)

    ≈-trans :
        ∀ {x y z}
      → x ≈ y
      → y ≈ z
      → x ≈ z
    ≈-trans (same x≈y) (same y≈z) =
      same (Successor.≈-trans P _ x≈y y≈z)

    <-trans :
        ∀ {x y z}
      → x < y
      → y < z
      → x < z
    <-trans =
      dependent-lexicographic-is-transitive
        (Successor.Entry P)
        _<ℕᶜ_
        (λ n → Successor._<_ P n)
        (λ {a} {b} {c} a<b b<c →
          <ℕᶜ-trans a b c a<b b<c)
        (Successor.<-trans P)

    <-respˡ-≈ :
        ∀ {x x′ y}
      → x ≈ x′
      → x < y
      → x′ < y
    <-respˡ-≈ (same x≈x′) (earlier m<n) =
      earlier m<n
    <-respˡ-≈ (same x≈x′) (within n x<y) =
      within n (Successor.<-respˡ-≈ P n x≈x′ x<y)

    <-respʳ-≈ :
        ∀ {x y y′}
      → y ≈ y′
      → x < y
      → x < y′
    <-respʳ-≈ (same y≈y′) (earlier m<n) =
      earlier m<n
    <-respʳ-≈ (same y≈y′) (within n x<y) =
      within n (Successor.<-respʳ-≈ P n y≈y′ x<y)

    compare :
        (x y : X)
      → Trichotomy _≈_ _<_ x y
    compare (m , x) (n , y)
        with cmpℕᶜ m n
    ... | inl m<n =
      inl (earlier m<n)
    ... | inr (inl refl) =
      lift-same (Successor.compare P m x y)
      where
        lift-same :
            Trichotomy _≈⁺_ _<⁺_ x y
          → Trichotomy _≈_ _<_ (m , x) (m , y)
        lift-same (inl x<y) =
          inl (within m x<y)
        lift-same (inr (inl x≈y)) =
          inr (inl (same x≈y))
        lift-same (inr (inr y<x)) =
          inr (inr (within m y<x))
    ... | inr (inr n<m) =
      inr (inr (earlier n<m))

    <-wf : is-well-founded _<_
    <-wf =
      dependent-lexicographic-is-well-founded
        (Successor.Entry P)
        _<ℕᶜ_
        (λ n → Successor._<_ P n)
        wfℕᶜ
        (Successor.<-wf P)

    enum : ℕ → Maybe X
    enum code
        with ℕ-unpair code
    ... | n , zero =
      just (n , Successor.top)
    ... | n , suc i
        with CountableOrdinal𝒫.enum (P n) i
    ... | nothing =
      nothing
    ... | just x =
      just (n , Successor.point x)

    enum-top :
        (n : ℕ)
      → enum (ℕ-pair n zero)
        ＝ just (n , Successor.top)
    enum-top n
        rewrite ℕ-unpair-pair n zero =
      refl

    module _ (n i : ℕ) where

      private
        module Pₙ = CountableOrdinal𝒫 (P n)

      enum-point :
          (x : Pₙ.X)
        → Pₙ.enum i ＝ just x
        → enum (ℕ-pair n (suc i))
          ＝ just (n , Successor.point x)
      enum-point x selected
          rewrite ℕ-unpair-pair n (suc i)
                | selected =
        refl

    covers :
        (x : X)
      → Σ ℕ λ code →
          Σ X λ r →
            (enum code ＝ just r)
            × (r ≈ x)
    covers (n , Successor.top) =
      ℕ-pair n zero
      , (n , Successor.top)
      , enum-top n
      , same Successor.top≈
    covers (n , Successor.point x)
        with CountableOrdinal𝒫.covers (P n) x
    ... | i , r , selected , r≈x =
      ℕ-pair n (suc i)
      , (n , Successor.point r)
      , enum-point n i r selected
      , same (Successor.point≈ r≈x)

    -- The diagonal presentation Σₙ (P(n) + 1).

    𝒫 : CountableOrdinal𝒫 ℓ
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

      private
        module Pₙ = CountableOrdinal𝒫 (P n)

      reflects :
          ∀ {x y : Pₙ.X}
        → (n , Successor.point x) < (n , Successor.point y)
        → x Pₙ.< y
      reflects {x} {y} embedded
          with Pₙ.compare x y
      ... | inl x<y =
        x<y
      ... | inr (inl x≈y) =
        𝟘-elim
          (Presentation.≈↛< 𝒫
            (same (Successor.point≈ x≈y))
            embedded)
      ... | inr (inr y<x) =
        𝟘-elim
          (Presentation.<-asym 𝒫
            embedded
            (within n (Successor.point< y<x)))

      member :
        P n ≺𝒫 𝒫
      member = record
        { to = λ x →
            n , Successor.point x
        ; to-≈ = λ x≈y →
            same (Successor.point≈ x≈y)
        ; to-< = λ x<y →
            within n (Successor.point< x<y)
        ; reflects-< = reflects
        ; ceiling =
            n , Successor.top
        ; below = λ x →
            within n Successor.point<top
        }

    -- A presentation above every member of the family.  The diagonal is one,
    -- built without any choice.

    Upper : Set (lsuc ℓ)
    Upper =
      Σ (CountableOrdinal𝒫 ℓ) λ Q →
        (n : ℕ) → P n ≺𝒫 Q

    upper : Upper
    upper =
      𝒫 , member

------------------------------------------------------------------------
-- Composition and well-foundedness of ≺𝒫

module Embedding where

  open _≺𝒫_ public

  -- The composite takes the image of the inner ceiling as its ceiling.

  trans :
      ∀ {ℓ}
        {P Q R : CountableOrdinal𝒫 ℓ}
    → P ≺𝒫 Q
    → Q ≺𝒫 R
    → P ≺𝒫 R
  trans e₁ e₂ = record
    { to = λ x →
        to e₂ (to e₁ x)
    ; to-≈ = λ x≈y →
        to-≈ e₂ (to-≈ e₁ x≈y)
    ; to-< = λ x<y →
        to-< e₂ (to-< e₁ x<y)
    ; reflects-< = λ tox<toy →
        reflects-< e₁ (reflects-< e₂ tox<toy)
    ; ceiling =
        to e₂ (ceiling e₁)
    ; below = λ x →
        to-< e₂ (below e₁ x)
    }

  private
    accFromCeiling :
        ∀ {ℓ}
          {P Q : CountableOrdinal𝒫 ℓ}
          (e : P ≺𝒫 Q)
      → is-accessible (CountableOrdinal𝒫._<_ Q) (ceiling e)
      → is-accessible _≺𝒫_ P
    accFromCeiling e (acc smaller) =
      acc λ R R≺P →
        accFromCeiling
          (trans R≺P e)
          (smaller
            (to e (ceiling R≺P))
            (below e (ceiling R≺P)))

  -- ≺𝒫 is well founded: a predecessor of Q has its ceiling in Q, and
  -- composite ceilings decrease in Q.

  wf :
      ∀ {ℓ}
    → is-well-founded (_≺𝒫_ {ℓ})
  wf Q =
    acc λ P P≺Q →
      accFromCeiling P≺Q
        (CountableOrdinal𝒫.<-wf Q (ceiling P≺Q))

  module _
      {ℓ : Level}
      {P : CountableOrdinal𝒫 ℓ}
    where

    private
      module P′ = CountableOrdinal𝒫 P

    self↛descending :
        (e : P ≺𝒫 P)
        (x : P′.X)
      → ¬ (to e x P′.< x)
    self↛descending e x =
      accessible-induction
        (λ y →
          ¬ (to e y P′.< y))
        (λ y smaller toy<y →
          smaller
            (to e y)
            toy<y
            (to-< e toy<y))
        x
        (P′.<-wf x)

  irrefl :
      ∀ {ℓ}
        (P : CountableOrdinal𝒫 ℓ)
    → ¬ P ≺𝒫 P
  irrefl P e =
    self↛descending
      e
      (ceiling e)
      (below e (ceiling e))

------------------------------------------------------------------------
-- Equivalence of presentations

-- Equivalence of presentations: order-preserving maps both ways whose
-- composites are the identity modulo ≈,
--
--   P ≃𝒫 Q ≃ Σ(f : |P| → |Q|). Σ(g : |Q| → |P|).
--              Preserves≈(f) × Preserves<(f) × Preserves≈(g) × Preserves<(g)
--            × (Π x. g(f(x)) ≈ x) × (Π y. f(g(y)) ≈ y).
--
-- Two presentations of the same order need not be equal as records.

infix 5 _≃𝒫_

record _≃𝒫_
    {ℓ : Level}
    (P Q : CountableOrdinal𝒫 ℓ)
    : Set ℓ where

  private
    module P′ = CountableOrdinal𝒫 P
    module Q′ = CountableOrdinal𝒫 Q

  field

    to :
      P′.X → Q′.X

    from :
      Q′.X → P′.X

    to-≈ :
      ∀ {x y}
      → x P′.≈ y
      → to x Q′.≈ to y

    from-≈ :
      ∀ {x y}
      → x Q′.≈ y
      → from x P′.≈ from y

    to-< :
      ∀ {x y}
      → x P′.< y
      → to x Q′.< to y

    from-< :
      ∀ {x y}
      → x Q′.< y
      → from x P′.< from y

    from-to-≈ :
      (x : P′.X)
      → from (to x) P′.≈ x

    to-from-≈ :
      (y : Q′.X)
      → to (from y) Q′.≈ y

open _≃𝒫_ public

≃𝒫-refl :
    ∀ {ℓ}
      (P : CountableOrdinal𝒫 ℓ)
  → P ≃𝒫 P
≃𝒫-refl P = record
  { to = λ x → x
  ; from = λ x → x
  ; to-≈ =
      λ x≈y → x≈y
  ; from-≈ =
      λ x≈y → x≈y
  ; to-< =
      λ x<y → x<y
  ; from-< =
      λ x<y → x<y
  ; from-to-≈ =
      CountableOrdinal𝒫.≈-refl P
  ; to-from-≈ =
      CountableOrdinal𝒫.≈-refl P
  }

≃𝒫-sym :
    ∀ {ℓ}
      {P Q : CountableOrdinal𝒫 ℓ}
  → P ≃𝒫 Q
  → Q ≃𝒫 P
≃𝒫-sym e = record
  { to        = from e
  ; from      = to e
  ; to-≈      = from-≈ e
  ; from-≈    = to-≈ e
  ; to-<      = from-< e
  ; from-<    = to-< e
  ; from-to-≈ = to-from-≈ e
  ; to-from-≈ = from-to-≈ e
  }

≃𝒫-trans :

    ∀ {ℓ}
      {P Q R : CountableOrdinal𝒫 ℓ}

  → P ≃𝒫 Q
  → Q ≃𝒫 R
  → P ≃𝒫 R

≃𝒫-trans
    {P = P} {R = R}
    e₁ e₂ = record

  { to = λ x →
      to e₂ (to e₁ x)

  ; from = λ x →
      from e₁ (from e₂ x)

  ; to-≈ = λ x≈y →
      to-≈ e₂ (to-≈ e₁ x≈y)

  ; from-≈ = λ x≈y →
      from-≈ e₁ (from-≈ e₂ x≈y)

  ; to-< = λ x<y →
      to-< e₂ (to-< e₁ x<y)

  ; from-< = λ x<y →
      from-< e₁ (from-< e₂ x<y)

  ; from-to-≈ = λ x →
      CountableOrdinal𝒫.≈-trans P

        (from-≈ e₁
          (from-to-≈ e₂ (to e₁ x)))

        (from-to-≈ e₁ x)

  ; to-from-≈ = λ y →
      CountableOrdinal𝒫.≈-trans R

        (to-≈ e₂
          (to-from-≈ e₁ (from e₂ y)))

        (to-from-≈ e₂ y)
  }

module _
    {ℓ : Level}
    {P Q : CountableOrdinal𝒫 ℓ}
  where

  private
    module P′ = CountableOrdinal𝒫 P
    module Q′ = CountableOrdinal𝒫 Q

  ≃𝒫-to-reflects-< :
      (e : P ≃𝒫 Q)
      {x y : P′.X}
    → to e x Q′.< to e y
    → x P′.< y
  ≃𝒫-to-reflects-< e {x} {y} tox<toy =
    P′.<-respʳ-≈
      (from-to-≈ e y)
      (P′.<-respˡ-≈
        (from-to-≈ e x)
        (from-< e tox<toy))

  ≃𝒫-from-reflects-< :
      (e : P ≃𝒫 Q)
      {x y : Q′.X}
    → from e x P′.< from e y
    → x Q′.< y
  ≃𝒫-from-reflects-< e {x} {y} fromx<fromy =
    Q′.<-respʳ-≈
      (to-from-≈ e y)
      (Q′.<-respˡ-≈
        (to-from-≈ e x)
        (to-< e fromx<fromy))

-- An equivalence P ≃𝒫 Q and a bounded embedding P ≺𝒫 Q give a bounded
-- self-embedding of Q, which is impossible (`≃𝒫↛≺𝒫`).

≃𝒫→self≺𝒫 :
    ∀ {ℓ}
      {P Q : CountableOrdinal𝒫 ℓ}
  → P ≃𝒫 Q
  → P ≺𝒫 Q
  → Q ≺𝒫 Q
≃𝒫→self≺𝒫 e bounded = record
  { to = λ x →
      Embedding.to bounded (from e x)
  ; to-≈ = λ x≈y →
      Embedding.to-≈ bounded (from-≈ e x≈y)
  ; to-< = λ x<y →
      Embedding.to-< bounded (from-< e x<y)
  ; reflects-< = λ tox<toy →
      ≃𝒫-from-reflects-< e
        (Embedding.reflects-< bounded tox<toy)
  ; ceiling =
      Embedding.ceiling bounded
  ; below = λ x →
      Embedding.below bounded (from e x)
  }

≃𝒫↛≺𝒫 :
    ∀ {ℓ}
      {P Q : CountableOrdinal𝒫 ℓ}
  → P ≃𝒫 Q
  → P ≺𝒫 Q
  → 𝟘
≃𝒫↛≺𝒫 {Q = Q} e bounded =
  Embedding.irrefl Q
    (≃𝒫→self≺𝒫 e bounded)

-- No family enumerates all presentations up to equality of records.

module Exact where

  Covers :
      ∀ {ℓ}
    → (ℕ → CountableOrdinal𝒫 ℓ)
    → Set (lsuc ℓ)
  Covers {ℓ} F =
    (P : CountableOrdinal𝒫 ℓ) →
      Σ ℕ λ n → F n ＝ P

  noEnumeration :
      ∀ {ℓ}
    → (Σ (ℕ → CountableOrdinal𝒫 ℓ) Covers)
    → 𝟘
  noEnumeration (F , covers)
      with Diagonal.upper F
  ... | Q , F≺Q
      with covers Q
  ... | n , Fₙ≡Q =
    Embedding.irrefl Q
      (transport
        (λ P → P ≺𝒫 Q)
        Fₙ≡Q
        (F≺Q n))

------------------------------------------------------------------------
-- Enumerations up to equivalence

-- Nor up to ≃𝒫: each time the family meets its own diagonal.

module Equivalent where

  Covers :
      ∀ {ℓ}
    → (ℕ → CountableOrdinal𝒫 ℓ)
    → Set (lsuc ℓ)
  Covers {ℓ} F =
    (P : CountableOrdinal𝒫 ℓ) →
      Σ ℕ λ n → F n ≃𝒫 P

  noEnumeration :
      ∀ {ℓ}
    → (Σ (ℕ → CountableOrdinal𝒫 ℓ) Covers)
    → 𝟘
  noEnumeration (F , covers)
      with Diagonal.upper F
  ... | Q , F≺Q
      with covers Q
  ... | n , Fₙ≃Q =
    ≃𝒫↛≺𝒫 Fₙ≃Q (F≺Q n)

------------------------------------------------------------------------
-- Cofinal families

infix 30 _≼𝒫_

_≼𝒫_ :
    ∀ {ℓ}
  → CountableOrdinal𝒫 ℓ
  → CountableOrdinal𝒫 ℓ
  → Set (lsuc ℓ)
P ≼𝒫 Q =
  (P ＝ Q) ⊎ P ≺𝒫 Q

-- Nor is any family cofinal for P ≼𝒫 Q = (P = Q) + (P ≺𝒫 Q).

module Cofinality where

  Covers :
      ∀ {ℓ}
    → (ℕ → CountableOrdinal𝒫 ℓ)
    → Set (lsuc ℓ)
  Covers {ℓ} F =
    (P : CountableOrdinal𝒫 ℓ) →
      Σ ℕ λ n → P ≼𝒫 F n

  noFamily :
      ∀ {ℓ}
    → (Σ (ℕ → CountableOrdinal𝒫 ℓ) Covers)
    → 𝟘
  noFamily (F , cofinal)
      with Diagonal.upper F
  ... | Q , F≺Q
      with cofinal Q
  ... | n , inl Q≡Fₙ =
    Embedding.irrefl Q
      (transport
        (λ P → P ≺𝒫 Q)
        (Q≡Fₙ ⁻¹)
        (F≺Q n))
  ... | n , inr Q≺Fₙ =
    Embedding.irrefl Q
      (Embedding.trans Q≺Fₙ (F≺Q n))

------------------------------------------------------------------------
-- One point above all presentations

-- The presentations at level ℓ with one further point above them:
--
--   Point(ℓ) = CountableOrdinal𝒫(ℓ) + 1,   embed(P) < boundary.
--
-- The relation does not compare presentations as ordinals: its only
-- instances are embed(P) < boundary, so the strict predecessors of
-- `boundary` are exactly the points embed(P) (`spectrum`).

module Boundary where

  data Point (ℓ : Level) : Set (lsuc ℓ) where
    embed : CountableOrdinal𝒫 ℓ → Point ℓ
    boundary : Point ℓ

  data Strict {ℓ : Level} : Point ℓ → Point ℓ → Set (lsuc ℓ) where
    below : (P : CountableOrdinal𝒫 ℓ) → Strict (embed P) boundary

  spectrum :
      ∀ {ℓ} {predecessor : Point ℓ}
    → Strict predecessor boundary
    → Σ (CountableOrdinal𝒫 ℓ) λ P →
        predecessor ＝ embed P
  spectrum (below P) =
    P , refl

  -- A point above every embedded presentation; `upper` is `boundary`.

  Upper :
      (ℓ : Level)
    → Set (lsuc ℓ)
  Upper ℓ =
    Σ (Point ℓ) λ upper →
      (P : CountableOrdinal𝒫 ℓ) →
        Strict
          (embed P)
          upper

  upper :
      ∀ {ℓ}
    → Upper ℓ
  upper =
    boundary
    , below

------------------------------------------------------------------------
-- The ω₁ geometry

-- An ω₁ geometry at level ℓ: a point above every presentation, whose
-- strict predecessors are exactly the embedded presentations, together
-- with the diagonal and the impossibility of enumerating presentations:
--
--   𝒫ω₁𝒢(ℓ) = Boundary.Upper(ℓ)
--            × Π(x < upper). Σ P. x ＝ embed(P)
--            × Π(f : ℕ → CountableOrdinal𝒫(ℓ)). Diagonal.Upper(f)
--            × ¬ Σ f. Equivalent.Covers(f).
--
-- `ω₁.Geometry.canonical` inhabits it.  It is data, not a
-- well-order; the order is built from its positions in the Cubical
-- reflection.

record 𝒫ω₁𝒢 (ℓ : Level) : Set (lsuc ℓ) where
  field
    upper : Boundary.Upper ℓ

    spectrum :
        ∀ {predecessor}
      → Boundary.Strict predecessor (pr₁ upper)
      → Σ (CountableOrdinal𝒫 ℓ) λ P →
          predecessor ＝ Boundary.embed P

    diagonal :
      (F : ℕ → CountableOrdinal𝒫 ℓ)
      → Diagonal.Upper F

    noCover :
      (Σ (ℕ → CountableOrdinal𝒫 ℓ) Equivalent.Covers)
      → 𝟘

module ω₁ where

  module Geometry where

    canonical : ∀ {ℓ} → 𝒫ω₁𝒢 ℓ
    canonical = record
      { upper = Boundary.upper
      ; spectrum = Boundary.spectrum
      ; diagonal = Diagonal.upper
      ; noCover = Equivalent.noEnumeration
      }

    -- The strict predecessors of the upper point are exactly the embedded
    -- presentations, in both directions.

    spectrum :
        ∀ {ℓ}
        → (geometry : 𝒫ω₁𝒢 ℓ)
        → (predecessor : Boundary.Point ℓ)
        → ( Boundary.Strict
              predecessor
              (pr₁ (𝒫ω₁𝒢.upper geometry))
            → Σ (CountableOrdinal𝒫 ℓ) λ P →
                predecessor ＝ Boundary.embed P
          )
          ×
          ( (Σ (CountableOrdinal𝒫 ℓ) λ P →
                predecessor ＝ Boundary.embed P)
            → Boundary.Strict
                predecessor
                (pr₁ (𝒫ω₁𝒢.upper geometry))
          )
    spectrum geometry predecessor =
      𝒫ω₁𝒢.spectrum geometry
      , λ where
          (P , predecessor-computes) →
            transport
              (λ source →
                Boundary.Strict
                  source
                  (pr₁ (𝒫ω₁𝒢.upper geometry)))
              (predecessor-computes ⁻¹)
              (pr₂ (𝒫ω₁𝒢.upper geometry) P)

    ----------------------------------------------------------------------
    -- Positions

    upper : ∀ {ℓ} → 𝒫ω₁𝒢 ℓ → Boundary.Point ℓ
    upper geometry = pr₁ (𝒫ω₁𝒢.upper geometry)

    -- A position is a presentation with its route below the upper point,
    --
    --   Position(G) = Σ(P : CountableOrdinal𝒫(ℓ)). embed(P) < upper(G).

    Position : ∀ {ℓ} → 𝒫ω₁𝒢 ℓ → Set (lsuc ℓ)
    Position {ℓ} geometry =
      Σ (CountableOrdinal𝒫 ℓ) λ P →
        Boundary.Strict
          (Boundary.embed P)
          (upper geometry)

    position :
        ∀ {ℓ}
        → (geometry : 𝒫ω₁𝒢 ℓ)
        → (P : CountableOrdinal𝒫 ℓ)
        → Position geometry
    position geometry P =
      P
      , pr₂ (𝒫ω₁𝒢.upper geometry) P

    -- Every strict predecessor of the upper point is the embedding of a
    -- position.

    covers :
        ∀ {ℓ}
        → (geometry : 𝒫ω₁𝒢 ℓ)
        → {predecessor : Boundary.Point ℓ}
        → Boundary.Strict
            predecessor
            (upper geometry)
        → Σ (Position geometry) λ position →
            predecessor ＝ Boundary.embed (pr₁ position)
    covers geometry predecessor<upper
        with 𝒫ω₁𝒢.spectrum geometry predecessor<upper
    ... | P , predecessor-computes =
      ( P
      , transport
          (λ source →
            Boundary.Strict source (upper geometry))
          predecessor-computes
          predecessor<upper
      )
      , predecessor-computes
