{-# OPTIONS --safe --without-K #-}

module SPT.Foundation.Limits.Sequential where

-- Sequential limits that keep every stage and every restriction between
-- adjacent stages as data. For stages Stage n and a relation R n from each
-- stage to the one below, a point of the limit chooses every stage with a
-- witness of R at every step (`Sequential-Limit`):
--
--   Σ (a : Π n. Stage n). Π n. R n (a (n + 1)) (a n).
--
-- No restriction is replaced by an identification of separately chosen
-- stages. A functional limit has R n x y = (r n x ＝ y) for maps r n
-- (`Functional-Limit`); a based limit adds a witness over its zero stage
-- (`Based-Sequential-Limit`). A limit is the sum of its stage families and
-- their witnesses, by record η (`limits-are-sums`).
--
-- A cone over X keeps a stage family and its witnesses at every point of X
-- (`Sequential-Cone`). Maps into the limit and cones determine each other
-- pointwise, every round trip by refl (`cone-of-map`, `mediating-map`, the
-- β and η laws, `limits-are-pointwise-universal`); with extensionality for
-- the maps into the limit, also as maps (`mediating-map-of-cone-of-map`).
-- Two identifications move a restriction witness (`transport-restriction`).

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.Isomorphisms using (_≅_)

------------------------------------------------------------------------
-- Sequential limits

-- Mathematical shape: Σ (a : Π n. Stage n). Π n. R n (a (n + 1)) (a n).
record Sequential-Limit {ℓ κ : Level} (Stage : ℕ → Set ℓ)
  (Restriction : (n : ℕ) → Stage (suc n) → Stage n → Set κ) :
  Set (ℓ ⊔ κ) where
  constructor limit
  field
    stage : (n : ℕ) → Stage n
    adjacent : (n : ℕ) → Restriction n (stage (suc n)) (stage n)

open Sequential-Limit public

-- The limit of a functional diagram: each witness identifies the image of
-- the stage above with the stage below.
Functional-Limit : {ℓ : Level} (Stage : ℕ → Set ℓ) →
  ((n : ℕ) → Stage (suc n) → Stage n) → Set ℓ
Functional-Limit Stage r =
  Sequential-Limit Stage (λ n higher lower → r n higher ＝ lower)

-- Mathematical shape: Σ (L : Sequential-Limit Stage R). Root (stage L 0).
Based-Sequential-Limit : {ℓ κ μ : Level} (Stage : ℕ → Set ℓ) →
  (Stage zero → Set μ) →
  ((n : ℕ) → Stage (suc n) → Stage n → Set κ) → Set (ℓ ⊔ κ ⊔ μ)
Based-Sequential-Limit Stage Root Restriction =
  Σ (Sequential-Limit Stage Restriction) (λ L → Root (stage L zero))

-- A limit is the sum of its stage families and their witnesses.
limits-are-sums : {ℓ κ : Level} {Stage : ℕ → Set ℓ}
  (Restriction : (n : ℕ) → Stage (suc n) → Stage n → Set κ) →
  Sequential-Limit Stage Restriction
    ≅ Σ ((n : ℕ) → Stage n) (λ a →
        (n : ℕ) → Restriction n (a (suc n)) (a n))
limits-are-sums Restriction = record
  { forward = λ L → stage L , adjacent L
  ; backward = λ t → limit (pr₁ t) (pr₂ t)
  ; backward-forward = λ L → refl
  ; forward-backward = λ t → refl
  }

-- Moving a restriction witness along identifications of its endpoints.
transport-restriction : {ℓ κ : Level} {Stage : ℕ → Set ℓ}
  (Restriction : (n : ℕ) → Stage (suc n) → Stage n → Set κ) {n : ℕ}
  {higher higher′ : Stage (suc n)} {lower lower′ : Stage n} →
  higher ＝ higher′ → lower ＝ lower′ →
  Restriction n higher lower → Restriction n higher′ lower′
transport-restriction Restriction refl refl w = w

------------------------------------------------------------------------
-- Cones

-- Mathematical shape:
--   Σ (a : X → Π n. Stage n). Π x n. R n (a x (n + 1)) (a x n).
record Sequential-Cone {ℓ κ μ : Level} (Stage : ℕ → Set ℓ)
  (Restriction : (n : ℕ) → Stage (suc n) → Stage n → Set κ) (X : Set μ) :
  Set (ℓ ⊔ κ ⊔ μ) where
  constructor cone
  field
    leg : X → (n : ℕ) → Stage n
    route : (x : X) (n : ℕ) → Restriction n (leg x (suc n)) (leg x n)

open Sequential-Cone public

-- Mathematical shape: maps X → limit and cones over X determine each
-- other, the map at each point and both cone fields at each point and
-- stage.
record Pointwise-Universal {ℓ κ μ : Level} (Stage : ℕ → Set ℓ)
  (Restriction : (n : ℕ) → Stage (suc n) → Stage n → Set κ) (X : Set μ) :
  Set (ℓ ⊔ κ ⊔ μ) where
  field
    cone-at :
      (X → Sequential-Limit Stage Restriction) →
      Sequential-Cone Stage Restriction X
    mediator :
      Sequential-Cone Stage Restriction X → X →
      Sequential-Limit Stage Restriction
    map-β : (m : X → Sequential-Limit Stage Restriction) (x : X) →
      mediator (cone-at m) x ＝ m x
    leg-β : (c : Sequential-Cone Stage Restriction X) (x : X) (n : ℕ) →
      leg (cone-at (mediator c)) x n ＝ leg c x n
    route-β : (c : Sequential-Cone Stage Restriction X) (x : X) (n : ℕ) →
      transport-restriction Restriction (leg-β c x (suc n)) (leg-β c x n)
        (route (cone-at (mediator c)) x n)
        ＝ route c x n

module _ {ℓ κ : Level} {Stage : ℕ → Set ℓ}
  {Restriction : (n : ℕ) → Stage (suc n) → Stage n → Set κ} where

  cone-of-map : {μ : Level} {X : Set μ} →
    (X → Sequential-Limit Stage Restriction) →
    Sequential-Cone Stage Restriction X
  cone-of-map m = cone (λ x n → stage (m x) n) (λ x n → adjacent (m x) n)

  limit-cone :
    Sequential-Cone Stage Restriction (Sequential-Limit Stage Restriction)
  limit-cone = cone-of-map (λ L → L)

  mediating-map : {μ : Level} {X : Set μ} →
    Sequential-Cone Stage Restriction X → X →
    Sequential-Limit Stage Restriction
  mediating-map c x = limit (leg c x) (route c x)

  mediating-map-stage-β : {μ : Level} {X : Set μ}
    (c : Sequential-Cone Stage Restriction X) (x : X) (n : ℕ) →
    stage (mediating-map c x) n ＝ leg c x n
  mediating-map-stage-β c x n = refl

  mediating-map-adjacent-β : {μ : Level} {X : Set μ}
    (c : Sequential-Cone Stage Restriction X) (x : X) (n : ℕ) →
    adjacent (mediating-map c x) n ＝ route c x n
  mediating-map-adjacent-β c x n = refl

  limit-η : (L : Sequential-Limit Stage Restriction) →
    limit (stage L) (adjacent L) ＝ L
  limit-η L = refl

  map-round-trip : {μ : Level} {X : Set μ}
    (m : X → Sequential-Limit Stage Restriction) (x : X) →
    mediating-map (cone-of-map m) x ＝ m x
  map-round-trip m x = limit-η (m x)

  cone-leg-round-trip : {μ : Level} {X : Set μ}
    (c : Sequential-Cone Stage Restriction X) (x : X) (n : ℕ) →
    leg (cone-of-map (mediating-map c)) x n ＝ leg c x n
  cone-leg-round-trip c x n = refl

  cone-route-round-trip : {μ : Level} {X : Set μ}
    (c : Sequential-Cone Stage Restriction X) (x : X) (n : ℕ) →
    route (cone-of-map (mediating-map c)) x n ＝ route c x n
  cone-route-round-trip c x n = refl

  limits-are-pointwise-universal : {μ : Level} {X : Set μ} →
    Pointwise-Universal Stage Restriction X
  limits-are-pointwise-universal = record
    { cone-at = cone-of-map
    ; mediator = mediating-map
    ; map-β = map-round-trip
    ; leg-β = cone-leg-round-trip
    ; route-β = λ c x n → refl
    }

  -- Under extensionality for the maps into the limit, the map round trip
  -- is an identification of maps.
  mediating-map-of-cone-of-map : {μ : Level} {X : Set μ} →
    FunExt X (λ x → Sequential-Limit Stage Restriction) →
    (m : X → Sequential-Limit Stage Restriction) →
    mediating-map (cone-of-map m) ＝ m
  mediating-map-of-cone-of-map extensionality m =
    extensionality (mediating-map (cone-of-map m)) m (map-round-trip m)
