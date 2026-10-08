{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Arithmetic.Classification.Local where

-- Local shapes in the von Neumann presentation. Below a point x of W, in
-- its domain ∂x, there is nothing, a greatest point, or an ascending
-- sequence with every point below x under one of its terms; the global
-- shape of W is the same datum for all of its points. A local shape
-- classifies ∂x, so a shaped presentation is pointwise classified. Shapes
-- pass to the images of initial maps, along equivalences, and to
-- completions; the formers of readings build them: ∅, P + 1, P + Q,
-- domains ∂x, sums Σ_{i ∈ I} F i of inhabited blocks over a shaped index,
-- the ω-multiple, and the indices of points and of points below a point.

open import Agda.Primitive using (Level; lzero)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
import Data.Nat as Nat
import Data.Nat.Properties as NatProperties
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; sym; trans; subst)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
import SPT.Cubical.OrdinalGeometry.Presentation.Map as Maps
import SPT.Cubical.OrdinalGeometry.Presentation.Successor as Adjoin
open import SPT.Cubical.OrdinalGeometry.Presentation.Sum using (_+_; ∂; left)
import SPT.Cubical.OrdinalGeometry.Presentation.Sum.Indexed as Indexed
import SPT.Cubical.OrdinalGeometry.Presentation.Limit as Limit
import SPT.Cubical.OrdinalGeometry.Presentation.Normalization as Normal
import SPT.Cubical.OrdinalGeometry.Presentation.Normalization.Presentation
  as Exact
import SPT.Cubical.OrdinalGeometry.Presentation.Normalization.Ordinal as Points
import SPT.Cubical.OrdinalGeometry.ExactOrder.Base as Order
import SPT.Cubical.OrdinalGeometry.Operation.Base as Operation
import SPT.Cubical.OrdinalGeometry.ExactOrder.OrderedSum as Index
open Index using (Ordinal; Carrier)
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Characterization using
  (bijection; pointless)
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Ambient using (_≤_)
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Classification using
  (Classified; respect)
import SPT.Cubical.OrdinalGeometry.Arithmetic.Classification as Classification
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Classification.Pointwise
  using (Pointwise)

private
  variable
    ℓ : Level
    P Q : 𝒫 ℓ

------------------------------------------------------------------------
-- Shapes

-- Mathematical shape: among the points z with B z, none, a greatest one,
-- or an ascending sequence with every such z below one of its terms.
data Shape {ℓ : Level} (W : 𝒫 ℓ) (B : 𝒫.X W → Set ℓ) : Set ℓ where
  none : ((z : 𝒫.X W) → B z → ⊥) → Shape W B
  greatest : (y : 𝒫.X W) → B y → ((z : 𝒫.X W) → B z → _≤_ W z y)
    → Shape W B
  ascending : (c : ℕ → 𝒫.X W) → ((n : ℕ) → 𝒫._<_ W (c n) (c (suc n)))
    → ((n : ℕ) → B (c n))
    → ((z : 𝒫.X W) → B z → Σ ℕ (λ n → 𝒫._<_ W z (c n)))
    → Shape W B

-- The shape of the domain of x.
Local : (W : 𝒫 ℓ) → 𝒫.X W → Set ℓ
Local W x = Shape W (λ z → 𝒫._<_ W z x)

-- The shape of all of W.
Global : 𝒫 ℓ → Set ℓ
Global W = Shape W (λ _ → ⊤)

-- A presentation with a shape at every point and a global shape.
record Shaped (W : 𝒫 ℓ) : Set ℓ where
  field
    local : (x : 𝒫.X W) → Local W x
    global : Global W

-- The same shape for an equivalent predicate.
reshape : {W : 𝒫 ℓ} {B B′ : 𝒫.X W → Set ℓ}
  → ((z : 𝒫.X W) → B′ z → B z) → ((z : 𝒫.X W) → B z → B′ z)
  → Shape W B → Shape W B′
reshape back forth (none n) = none λ z b → n z (back z b)
reshape back forth (greatest y b g) =
  greatest y (forth y b) λ z b′ → g z (back z b′)
reshape back forth (ascending c up b every) =
  ascending c up (λ n → forth (c n) (b n)) λ z b′ → every z (back z b′)

-- Equivalent points have the same local shape.
moved : (W : 𝒫 ℓ) {x x′ : 𝒫.X W} → 𝒫._≈_ W x x′ → Local W x → Local W x′
moved W e = reshape (λ z q → 𝒫.<-respʳ-≈ W (𝒫.≈-sym W e) q)
  (λ z q → 𝒫.<-respʳ-≈ W e q)

------------------------------------------------------------------------
-- A local shape classifies the domain

private
  -- With y the greatest point below x, ∂x ≃ ∂y + 1.
  topped : (W : 𝒫 ℓ) {x y : 𝒫.X W} → 𝒫._<_ W y x
    → ((z : 𝒫.X W) → 𝒫._<_ W z x → _≤_ W z y)
    → Maps.Successor.next (∂ W y) Presented.≃𝒫 ∂ W x
  topped W {x} {y} p g = bijection embedding covers
    where
    module Entry = Presented.Diagonal.Successor
      (Adjoin.constant (∂ W y)) zero

    map : Entry.Entry → 𝒫.X (∂ W x)
    map (Entry.point (z , q)) = z , 𝒫.<-trans W q p
    map Entry.top = y , p

    resp : ∀ {u v} → u Entry.≈ v → 𝒫._≈_ (∂ W x) (map u) (map v)
    resp (Entry.point≈ e) = e
    resp Entry.top≈ = 𝒫.≈-refl W y

    strict : ∀ {u v} → u Entry.< v → 𝒫._<_ (∂ W x) (map u) (map v)
    strict (Entry.point< q) = q
    strict (Entry.point<top {x = z , q}) = q

    embedding : Maps.Embedding (Maps.Successor.next (∂ W y)) (∂ W x)
    embedding = record
      { map = map
      ; resp = λ {u} {v} → resp {u} {v}
      ; strict = λ {u} {v} → strict {u} {v}
      }

    covers : (w : 𝒫.X (∂ W x))
      → Σ Entry.Entry (λ u → 𝒫._≈_ (∂ W x) (map u) w)
    covers (z , q) with g z q
    ... | inj₁ r = Entry.point (z , r) , 𝒫.≈-refl W z
    ... | inj₂ e = Entry.top , 𝒫.≈-sym W e

-- Nothing below: zero; a greatest point y: the strong successor of ∂y;
-- an ascending cofinal sequence: the limit of its domains.
classify : (W : 𝒫 ℓ) (x : 𝒫.X W) → Local W x → Classified (∂ W x)
classify W x (none n) =
  Classification.zero (pointless λ u → n (proj₁ u) (proj₂ u))
classify W x (greatest y p g) =
  respect (topped W p g) (Classification.next (∂ W y))
classify W x (ascending c up b every) =
  Classification.limit (proj₁ limit) (proj₂ limit)
  where
  limit = Classification.cofinal (∂ W x) (λ n → c n , b n) up
    (λ u → every (proj₁ u) (proj₂ u))

-- A shaped presentation is pointwise classified.
pointwise : (W : 𝒫 ℓ) → Shaped W → Pointwise W
pointwise W s x = classify W x (Shaped.local s x)

------------------------------------------------------------------------
-- Initial maps, equivalences and completions

-- An initial map carries the shape of x to the shape of its image.
image : (f : Maps.Initial P Q) (x : 𝒫.X P) → Local P x
  → Local Q (Maps.Initial.map f x)
image {P = P} {Q = Q} f x shape = carry shape
  where
  module F = Maps.Initial f

  -- A point below f x comes from a point below x.
  back : (z : 𝒫.X Q) → 𝒫._<_ Q z (F.map x)
    → Σ (𝒫.X P) (λ w → 𝒫._<_ P w x × 𝒫._≈_ Q (F.map w) z)
  back z q with F.lower x z q
  ... | w , e = w , F.reflect (𝒫.<-respˡ-≈ Q (𝒫.≈-sym Q e) q) , e

  raise : {w y : 𝒫.X P} {z : 𝒫.X Q} → _≤_ P w y → 𝒫._≈_ Q (F.map w) z
    → _≤_ Q z (F.map y)
  raise (inj₁ r) e = inj₁ (𝒫.<-respˡ-≈ Q e (F.strict r))
  raise (inj₂ r) e = inj₂ (𝒫.≈-trans Q (𝒫.≈-sym Q e) (F.resp r))

  carry : Local P x → Local Q (F.map x)
  carry (none n) = none λ z q →
    let w , r , _ = back z q in n w r
  carry (greatest y p g) = greatest (F.map y) (F.strict p) λ z q →
    let w , r , e = back z q in raise (g w r) e
  carry (ascending c up b every) =
    ascending (λ n → F.map (c n)) (λ n → F.strict (up n))
      (λ n → F.strict (b n)) λ z q →
        let w , r , e = back z q ; n , s = every w r in
        n , 𝒫.<-respˡ-≈ Q e (F.strict s)

-- Shapes pass along an equivalence.
transport : P Presented.≃𝒫 Q → Shaped P → Shaped Q
transport {P = P} {Q = Q} e s = record
  { local = λ y → moved Q (E.to-from-≈ y)
      (image (Maps.equivalence e) (E.from y) (Shaped.local s (E.from y)))
  ; global = carry (Shaped.global s)
  }
  where
  module E = Presented._≃𝒫_ e

  carry : Global P → Global Q
  carry (none n) = none λ z _ → n (E.from z) tt
  carry (greatest y _ g) = greatest (E.to y) tt λ z _ → raise (g (E.from z) tt)
    where
    raise : {z : 𝒫.X Q} → _≤_ P (E.from z) y → _≤_ Q z (E.to y)
    raise {z} (inj₁ r) = inj₁ (𝒫.<-respˡ-≈ Q (E.to-from-≈ z) (E.to-< r))
    raise {z} (inj₂ r) =
      inj₂ (𝒫.≈-trans Q (𝒫.≈-sym Q (E.to-from-≈ z)) (E.to-≈ r))
  carry (ascending c up _ every) =
    ascending (λ n → E.to (c n)) (λ n → E.to-< (up n)) (λ _ → tt) λ z _ →
      let n , r = every (E.from z) tt in
      n , 𝒫.<-respˡ-≈ Q (E.to-from-≈ z) (E.to-< r)

-- A completion has the shapes of its stages, through coverage.
completion : (C : Limit.Chain ℓ)
  → ((n : ℕ) (x : 𝒫.X (Limit.Chain.stage C n))
      → Local (Limit.Chain.stage C n) x)
  → (y : 𝒫.X (Limit.completion C)) → Local (Limit.completion C) y
completion C l y with Limit.coverage C y
... | k , x , p =
  subst (Local (Limit.completion C)) p (image (Limit.stage C k) x (l k x))

------------------------------------------------------------------------
-- ∅, domains, P + 1 and P + Q

vacant : Shaped (Operation.empty {ℓ})
vacant = record
  { local = λ x → ⊥-elim (lower x)
  ; global = none λ z _ → lower z
  }

-- The domain of x is shaped when the points of W are, with the shape of
-- x as its global shape.
domain : (W : 𝒫 ℓ) → ((z : 𝒫.X W) → Local W z) → (x : 𝒫.X W)
  → Shaped (∂ W x)
domain W l x = record { local = local ; global = global (l x) }
  where
  local : (u : 𝒫.X (∂ W x)) → Local (∂ W x) u
  local (z , q) with l z
  ... | none n = none λ w s → n (proj₁ w) s
  ... | greatest y p g =
    greatest (y , 𝒫.<-trans W p q) p λ w s → g (proj₁ w) s
  ... | ascending c up b every =
    ascending (λ n → c n , 𝒫.<-trans W (b n) q) up b
      λ w s → every (proj₁ w) s

  global : Local W x → Global (∂ W x)
  global (none n) = none λ w _ → n (proj₁ w) (proj₂ w)
  global (greatest y p g) = greatest (y , p) tt λ w _ → g (proj₁ w) (proj₂ w)
  global (ascending c up b every) =
    ascending (λ n → c n , b n) up (λ _ → tt)
      λ w _ → every (proj₁ w) (proj₂ w)

-- P + 1: old points keep their shapes; the top has the shape of P, and
-- it is the greatest point.
successor : Shaped P → Shaped (Maps.Successor.next P)
successor {P = P} s = record { local = local ; global = global }
  where
  module Entry = Presented.Diagonal.Successor
    (Adjoin.constant P) zero

  lifted : {w y : 𝒫.X P} → _≤_ P w y
    → _≤_ (Maps.Successor.next P) (Entry.point w) (Entry.point y)
  lifted (inj₁ r) = inj₁ (Entry.point< r)
  lifted (inj₂ r) = inj₂ (Entry.point≈ r)

  atTop : Global P → Local (Maps.Successor.next P) Entry.top
  atTop (none n) = none λ where
    (Entry.point w) Entry.point<top → n w tt
  atTop (greatest y _ g) = greatest (Entry.point y) Entry.point<top λ where
    (Entry.point w) Entry.point<top → lifted (g w tt)
  atTop (ascending c up _ every) =
    ascending (λ n → Entry.point (c n)) (λ n → Entry.point< (up n))
      (λ _ → Entry.point<top) λ where
        (Entry.point w) Entry.point<top →
          let n , r = every w tt in n , Entry.point< r

  local : (x : 𝒫.X (Maps.Successor.next P))
    → Local (Maps.Successor.next P) x
  local (Entry.point x) =
    image (Maps.Successor.initial P) x (Shaped.local s x)
  local Entry.top = atTop (Shaped.global s)

  global : Global (Maps.Successor.next P)
  global = greatest Entry.top tt λ where
    (Entry.point w) _ → inj₁ Entry.point<top
    Entry.top _ → inj₂ Entry.top≈

-- P + Q: left points keep their shapes; a right point keeps its shape in
-- Q, and has the shape of P when it is least in Q.
plus : Shaped P → Shaped Q → Shaped (P + Q)
plus {P = P} {Q = Q} sP sQ = record { local = local ; global = global }
  where
  -- Below a least right point, or in all of P + Q when Q is empty, lies
  -- exactly P.
  lefts : {B : 𝒫.X (P + Q) → Set _} → ((w : 𝒫.X P) → B (inj₁ w))
    → ((w : 𝒫.X Q) → B (inj₂ w) → ⊥) → Global P → Shape (P + Q) B
  lefts {B} all right (none n) = none λ where
    (inj₁ w) _ → n w tt
    (inj₂ w) b → right w b
  lefts {B} all right (greatest y _ g) = greatest (inj₁ y) (all y) λ where
    (inj₁ w) _ → g w tt
    (inj₂ w) b → ⊥-elim (right w b)
  lefts {B} all right (ascending c up _ every) =
    ascending (λ n → inj₁ (c n)) up (λ n → all (c n)) λ where
      (inj₁ w) _ → every w tt
      (inj₂ w) b → ⊥-elim (right w b)

  rights : (y : 𝒫.X Q) → Local Q y → Local (P + Q) (inj₂ y)
  rights y (none n) = lefts (λ w → tt) n (Shaped.global sP)
  rights y (greatest y′ p g) = greatest (inj₂ y′) p λ where
    (inj₁ w) _ → inj₁ tt
    (inj₂ w) q → g w q
  rights y (ascending c up b every) = ascending (λ n → inj₂ (c n)) up b
    λ where
      (inj₁ w) _ → zero , tt
      (inj₂ w) q → every w q

  local : (x : 𝒫.X (P + Q)) → Local (P + Q) x
  local (inj₁ x) = image (left P Q) x (Shaped.local sP x)
  local (inj₂ y) = rights y (Shaped.local sQ y)

  global′ : Global Q → Global (P + Q)
  global′ (none n) = lefts (λ _ → tt) (λ w _ → n w tt) (Shaped.global sP)
  global′ (greatest y _ g) = greatest (inj₂ y) tt λ where
    (inj₁ w) _ → inj₁ tt
    (inj₂ w) _ → g w tt
  global′ (ascending c up _ every) = ascending (λ n → inj₂ (c n)) up
    (λ _ → tt) λ where
      (inj₁ w) _ → zero , tt
      (inj₂ w) _ → every w tt

  global : Global (P + Q)
  global = global′ (Shaped.global sQ)

------------------------------------------------------------------------
-- Sums over shaped indices

-- An exact index, as a presentation.
index : Ordinal lzero → 𝒫 lzero
index I = Exact.presentation (Index.order I)

-- Σ_{i ∈ I} F i over a shaped index, with shaped and inhabited blocks. A
-- point (i, a) has the shape of a in its block; when a is least in its
-- block, it has the shape of i in the index, carried through the earlier
-- blocks: nothing, the shape of the block at the greatest index below i,
-- or one point in each block at an ascending sequence of indices.
sum : (I : Ordinal lzero) (F : Carrier I → 𝒫 ℓ) → Shaped (index I)
  → ((i : Carrier I) → Shaped (F i)) → ((i : Carrier I) → 𝒫.X (F i))
  → Shaped (Indexed.sum I F)
sum {ℓ} I F sI sF inhabited = record { local = local ; global = global }
  where
  module B = Order.Sum (Index.order I) (λ i → Normal.order (F i))

  Total : 𝒫 ℓ
  Total = Indexed.sum I F

  rep : (i : Carrier I) → Normal.Point (F i) → 𝒫.X (F i)
  rep i = Normal.representative (F i)

  cls : (i : Carrier I) → 𝒫.X (F i) → Normal.Point (F i)
  cls i = Normal.class (F i)

  -- Normalized points against points of a block.
  up : (i : Carrier I) {b a : Normal.Point (F i)} → Normal.Strict (F i) b a
    → 𝒫._<_ (F i) (rep i b) (rep i a)
  up i {b} {a} = Normal.representative-strict (F i) {a = b} {b = a}

  down : (i : Carrier I) {y : 𝒫.X (F i)} {a : Normal.Point (F i)}
    → 𝒫._<_ (F i) y (rep i a) → Normal.Strict (F i) (cls i y) a
  down i {y} {a} p = subst (Normal.Strict (F i) (cls i y))
    (Normal.class-representative (F i) a)
    (Normal.class-strict (F i) {x = y} {y = rep i a} p)

  toward : (i : Carrier I) {b : Normal.Point (F i)} {y : 𝒫.X (F i)}
    → 𝒫._<_ (F i) (rep i b) y → Normal.Strict (F i) b (cls i y)
  toward i {b} {y} p = subst (λ c → Normal.Strict (F i) c (cls i y))
    (Normal.class-representative (F i) b)
    (Normal.class-strict (F i) {x = rep i b} {y = y} p)

  ascend : (i : Carrier I) {y y′ : 𝒫.X (F i)} → 𝒫._<_ (F i) y y′
    → 𝒫._<_ Total (lift (i , cls i y)) (lift (i , cls i y′))
  ascend i {y} {y′} p =
    lift (B.within i (Normal.class-strict (F i) {x = y} {y = y′} p))

  settle : (i : Carrier I) {b : Normal.Point (F i)} {y : 𝒫.X (F i)}
    → _≤_ (F i) (rep i b) y → _≤_ Total (lift (i , b)) (lift (i , cls i y))
  settle i {b} {y} (inj₁ r) = inj₁ (lift (B.within i (toward i {b} {y} r)))
  settle i {b} (inj₂ r) = inj₂ (lift (cong (i ,_)
    (trans (sym (Normal.class-representative (F i) b))
      (Normal.class-resp (F i) r))))

  -- The points z with Bz lie in the blocks up to k, and the block at k
  -- lies inside Bz: the shape is that of the block at k.
  upTo : {Bz : 𝒫.X Total → Set ℓ} (k : Carrier I)
    → ((x : Normal.Point (F k)) → Bz (lift (k , x)))
    → ((j : Carrier I) (b : Normal.Point (F j)) → Bz (lift (j , b))
        → _≤_ (index I) (lift j) (lift k))
    → Global (F k) → Shape Total Bz
  upTo k inside bound (none nk) = ⊥-elim (nk (inhabited k) tt)
  upTo {Bz} k inside bound (greatest y _ g) =
    greatest (lift (k , cls k y)) (inside (cls k y)) λ where
      (lift (j , b)) q → atMost j b (bound j b q)
    where
    sameBlock : (j : Carrier I) (b : Normal.Point (F j)) → j ≡ k
      → _≤_ Total (lift (j , b)) (lift (k , cls k y))
    sameBlock .k b refl = settle k (g (rep k b) tt)

    atMost : (j : Carrier I) (b : Normal.Point (F j))
      → _≤_ (index I) (lift j) (lift k)
      → _≤_ Total (lift (j , b)) (lift (k , cls k y))
    atMost j b (inj₁ (lift s)) = inj₁ (lift (B.earlier s))
    atMost j b (inj₂ (lift e)) = sameBlock j b e
  upTo {Bz} k inside bound (ascending c inc _ every) =
    ascending (λ m → lift (k , cls k (c m))) (λ m → ascend k (inc m))
      (λ m → inside (cls k (c m))) λ where
        (lift (j , b)) q → reach j b (bound j b q)
    where
    sameBlock : (j : Carrier I) (b : Normal.Point (F j)) → j ≡ k
      → Σ ℕ (λ m → 𝒫._<_ Total (lift (j , b)) (lift (k , cls k (c m))))
    sameBlock .k b refl =
      let m , s = every (rep k b) tt in
      m , lift (B.within k (toward k {b} {c m} s))

    reach : (j : Carrier I) (b : Normal.Point (F j))
      → _≤_ (index I) (lift j) (lift k)
      → Σ ℕ (λ m → 𝒫._<_ Total (lift (j , b)) (lift (k , cls k (c m))))
    reach j b (inj₁ (lift s)) = zero , lift (B.earlier s)
    reach j b (inj₂ (lift e)) = sameBlock j b e

  -- a is least in its block: below (i, a) lie exactly the earlier blocks.
  least : (i : Carrier I) (a : Normal.Point (F i))
    → ((z : 𝒫.X (F i)) → 𝒫._<_ (F i) z (rep i a) → ⊥)
    → Local (index I) (lift i) → Local Total (lift (i , a))
  least i a n (none m) = none λ where
    (lift (j , b)) (lift (B.earlier r)) → m (lift j) (lift r)
    (lift (.i , b)) (lift (B.within .i r)) → n (rep i b) (up i {b} {a} r)
  least i a n (greatest (lift k) (lift kᵢ) gk) =
    upTo k (λ x → lift (B.earlier kᵢ)) bound (Shaped.global (sF k))
    where
    bound : (j : Carrier I) (b : Normal.Point (F j))
      → 𝒫._<_ Total (lift (j , b)) (lift (i , a))
      → _≤_ (index I) (lift j) (lift k)
    bound j b (lift (B.earlier r)) = gk (lift j) (lift r)
    bound .i b (lift (B.within .i r)) =
      ⊥-elim (n (rep i b) (up i {b} {a} r))
  least i a n (ascending c inc b every) =
    ascending (λ m → lift (lower (c m) , cls (lower (c m))
        (inhabited (lower (c m)))))
      (λ m → lift (B.earlier (lower (inc m))))
      (λ m → lift (B.earlier (lower (b m)))) λ where
        (lift (j , b′)) (lift (B.earlier r)) →
          let m , s = every (lift j) (lift r) in m , lift (B.earlier (lower s))
        (lift (.i , b′)) (lift (B.within .i r)) →
          ⊥-elim (n (rep i b′) (up i {b′} {a} r))

  atPoint : (i : Carrier I) (a : Normal.Point (F i))
    → Local (F i) (rep i a) → Local Total (lift (i , a))
  atPoint i a (none n) = least i a n (Shaped.local sI (lift i))
  atPoint i a (greatest y p g) =
    greatest (lift (i , cls i y)) (lift (B.within i (down i {y} {a} p))) λ where
      (lift (j , b)) (lift (B.earlier r)) → inj₁ (lift (B.earlier r))
      (lift (.i , b)) (lift (B.within .i r)) →
        settle i (g (rep i b) (up i {b} {a} r))
  atPoint i a (ascending c inc b every) =
    ascending (λ n → lift (i , cls i (c n))) (λ n → ascend i (inc n))
      (λ n → lift (B.within i (down i {c n} {a} (b n)))) λ where
        (lift (j , b′)) (lift (B.earlier r)) → zero , lift (B.earlier r)
        (lift (.i , b′)) (lift (B.within .i r)) →
          let n , s = every (rep i b′) (up i {b′} {a} r) in
          n , lift (B.within i (toward i {b′} {c n} s))

  local : (x : 𝒫.X Total) → Local Total x
  local (lift (i , a)) = atPoint i a (Shaped.local (sF i) (rep i a))

  global′ : Global (index I) → Global Total
  global′ (none m) = none λ z _ → m (lift (proj₁ (lower z))) tt
  global′ (greatest (lift k) _ gk) = upTo k (λ _ → tt)
    (λ j b _ → gk (lift j) tt) (Shaped.global (sF k))
  global′ (ascending c inc _ every) =
    ascending (λ m → lift (lower (c m) , cls (lower (c m))
        (inhabited (lower (c m)))))
      (λ m → lift (B.earlier (lower (inc m)))) (λ _ → tt) λ z _ →
        let m , s = every (lift (proj₁ (lower z))) tt in
        m , lift (B.earlier (lower s))

  global : Global Total
  global = global′ (Shaped.global sI)

------------------------------------------------------------------------
-- Indices

-- The empty index.
nothing : Shaped (index (Index.empty {lzero}))
nothing = record
  { local = λ z → ⊥-elim (lower (lower z))
  ; global = none λ z _ → lower (lower z)
  }

-- The one-point index.
single : Shaped (index (Index.unit {lzero}))
single = record
  { local = λ _ → none λ _ q → lower (lower q)
  ; global = greatest (lift tt) tt λ _ _ → inj₂ (lift refl)
  }

-- The natural numbers: 0 is least, n is the greatest point below n + 1,
-- and the numbers ascend through all of them.
naturals : Shaped (index (Index.natural {lzero}))
naturals = record { local = local ; global = global }
  where
  N : 𝒫 lzero
  N = index Index.natural

  numeral : ℕ → 𝒫.X N
  numeral n = lift (lift n)

  next< : (n : ℕ) → 𝒫._<_ N (numeral n) (numeral (suc n))
  next< n = lift (lift (NatProperties.n<1+n n))

  atMost : {m n : ℕ} → m Nat.≤ n → _≤_ N (numeral m) (numeral n)
  atMost q with NatProperties.m≤n⇒m<n∨m≡n q
  ... | inj₁ r = inj₁ (lift (lift r))
  ... | inj₂ e = inj₂ (lift (cong lift e))

  local : (x : 𝒫.X N) → Local N x
  local (lift (lift zero)) = none λ where
    (lift (lift m)) (lift (lift ()))
  local (lift (lift (suc n))) = greatest (numeral n) (next< n) λ where
    (lift (lift m)) (lift (lift q)) → atMost (NatProperties.≤-pred q)

  global : Global N
  global = ascending numeral next< (λ _ → tt) λ where
    (lift (lift m)) _ → suc m , next< m

-- The ω-multiple S·ω: empty when S is, and otherwise the sum over the
-- natural numbers of the inhabited block S.
times : (S : 𝒫 ℓ) → Shaped S → Shaped (Indexed.times S)
times S s with Shaped.global s
... | none n = record
  { local = λ z → ⊥-elim (n (Normal.representative S (proj₂ (lower z))) tt)
  ; global = none λ z _ → n (Normal.representative S (proj₂ (lower z))) tt
  }
... | greatest y _ _ =
  sum Index.natural (λ _ → S) naturals (λ _ → s) (λ _ → y)
... | ascending c _ _ _ =
  sum Index.natural (λ _ → S) naturals (λ _ → s) (λ _ → c zero)

-- The normalized points of a shaped L: L ≃ its normalization.
points : (L : 𝒫 lzero) → Shaped L → Shaped (index (Points.points L))
points L = transport (Maps.antisymmetry (Exact.quotient L) (Exact.section L))

-- The normalized points below c: the domain of c in the normalization.
below : (L : 𝒫 lzero) → Shaped L → (c : Normal.Point L)
  → Shaped (index (Points.below L c))
below L s c = transport cone (domain (index (Points.points L))
  (Shaped.local (points L s)) (lift c))
  where
  N : 𝒫 lzero
  N = index (Points.points L)

  pair : {b b′ : Normal.Point L} (p : Normal.Strict L b c)
    (p′ : Normal.Strict L b′ c) → b ≡ b′ → (b , p) ≡ (b′ , p′)
  pair {b} p p′ refl =
    cong (b ,_) (Normal.strict-unique L {a = b} {b = c} p p′)

  cone : ∂ N (lift c) Presented.≃𝒫 index (Points.below L c)
  cone = record
    { to = λ u → lift (lower (proj₁ u) , lower (proj₂ u))
    ; from = λ v → lift (proj₁ (lower v)) , lift (proj₂ (lower v))
    ; to-≈ = λ {u} {v} e → lift (pair (lower (proj₂ u)) (lower (proj₂ v))
        (lower e))
    ; from-≈ = λ e → lift (cong proj₁ (lower e))
    ; to-< = λ q → q
    ; from-< = λ q → q
    ; from-to-≈ = λ u → lift refl
    ; to-from-≈ = λ v → lift refl
    }
