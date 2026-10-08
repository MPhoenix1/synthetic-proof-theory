{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Presentation.Limit where

-- The least boundary of a countable chain of initial maps. Comparison takes
-- place in a common later stage; normalization identifies repeated points.
-- Initial maps into any presented bound extend uniquely to the boundary;
-- compatible stage embeddings extend to an embedding of the boundary.

open import Agda.Primitive using (Level; lsuc)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using
  (ℕ; zero; suc; _≤_; _≤′_; ≤′-refl; ≤′-step; _⊔_)
import Data.Nat.Properties as Nat
open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality using
  (_≡_; cong)

open import SPT.Cubical.Core.WellFounded using (Acc; acc)
import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
import SPT.Cubical.OrdinalGeometry.Presentation.Map as Maps
import SPT.Cubical.OrdinalGeometry.Presentation.Normalization as Normal
import SPT.Cubical.OrdinalGeometry.Presentation.Normalization.Presentation
  as Exact
import SPT.Cubical.OrdinalGeometry.ExactOrder.Base as Order

private
  variable
    ℓ : Level

record Chain (ℓ : Level) : Set (lsuc ℓ) where
  field
    stage : ℕ → 𝒫 ℓ
    edge : (n : ℕ) → Maps.Initial (stage n) (stage (suc n))

private
  iterate : (C : Chain ℓ) {m n : ℕ} → m ≤′ n
    → Maps.Initial (Chain.stage C m) (Chain.stage C n)
  iterate C {m} ≤′-refl = Maps.identity (Chain.stage C m)
  iterate C (≤′-step {n = n} p) =
    Maps.compose (iterate C p) (Chain.edge C n)

advance : (C : Chain ℓ) {m n : ℕ} → m ≤ n
  → Maps.Initial (Chain.stage C m) (Chain.stage C n)
advance C p = iterate C (Nat.≤⇒≤′ p)

-- Stage embeddings into Q that commute with the edges, up to ≈. Unlike
-- initial maps, embeddings are not unique, so this is a separate datum.
Compatible : (C : Chain ℓ) (Q : 𝒫 ℓ)
  → ((n : ℕ) → Maps.Embedding (Chain.stage C n) Q) → Set ℓ
Compatible C Q f = (n : ℕ) (x : 𝒫.X (Chain.stage C n))
  → 𝒫._≈_ Q
      (Maps.Embedding.map (f (suc n)) (Maps.Initial.map (Chain.edge C n) x))
      (Maps.Embedding.map (f n) x)

private
  Occurrence : Chain ℓ → Set ℓ
  Occurrence C = Σ ℕ (λ n → 𝒫.X (Chain.stage C n))

  image : (C : Chain ℓ) (x : Occurrence C) {k : ℕ}
    → proj₁ x ≤ k → 𝒫.X (Chain.stage C k)
  image C (n , x) p = Maps.Initial.map (advance C p) x

  aligned : (C : Chain ℓ) (x : Occurrence C) {k : ℕ}
    → (p q : proj₁ x ≤ k)
    → 𝒫._≈_ (Chain.stage C k) (image C x p) (image C x q)
  aligned C (n , x) p q =
    Maps.Uniqueness.pointwise (advance C p) (advance C q) x

  followed : (C : Chain ℓ) (x : Occurrence C) {k l : ℕ}
    → (p : proj₁ x ≤ k) (q : k ≤ l)
    → 𝒫._≈_ (Chain.stage C l)
        (Maps.Initial.map (advance C q) (image C x p))
        (image C x (Nat.≤-trans p q))
  followed C (n , x) p q = Maps.Uniqueness.pointwise
    (Maps.compose (advance C p) (advance C q))
    (advance C (Nat.≤-trans p q)) x

  Witness : (C : Chain ℓ)
    → ((n : ℕ) → 𝒫.X (Chain.stage C n) → 𝒫.X (Chain.stage C n) → Set ℓ)
    → Occurrence C → Occurrence C → Set ℓ
  Witness C R x y = Σ ℕ λ k → Σ (proj₁ x ≤ k) λ p →
    Σ (proj₁ y ≤ k) λ q → R k (image C x p) (image C y q)

  Equivalent Strict : (C : Chain ℓ) → Occurrence C → Occurrence C → Set ℓ
  Equivalent C = Witness C (λ n → 𝒫._≈_ (Chain.stage C n))
  Strict C = Witness C (λ n → 𝒫._<_ (Chain.stage C n))

  raise-≈ : (C : Chain ℓ) {x y : Occurrence C} {k l : ℕ}
    → (p : proj₁ x ≤ k) (q : proj₁ y ≤ k) (r : k ≤ l)
    → 𝒫._≈_ (Chain.stage C k) (image C x p) (image C y q)
    → 𝒫._≈_ (Chain.stage C l)
        (image C x (Nat.≤-trans p r)) (image C y (Nat.≤-trans q r))
  raise-≈ C {x} {y} {l = l} p q r h =
    𝒫.≈-trans (Chain.stage C l)
      (𝒫.≈-sym (Chain.stage C l) (followed C x p r))
      (𝒫.≈-trans (Chain.stage C l)
        (Maps.Initial.resp (advance C r) h) (followed C y q r))

  raise-< : (C : Chain ℓ) {x y : Occurrence C} {k l : ℕ}
    → (p : proj₁ x ≤ k) (q : proj₁ y ≤ k) (r : k ≤ l)
    → 𝒫._<_ (Chain.stage C k) (image C x p) (image C y q)
    → 𝒫._<_ (Chain.stage C l)
        (image C x (Nat.≤-trans p r)) (image C y (Nat.≤-trans q r))
  raise-< C {x} {y} {l = l} p q r h =
    𝒫.<-respˡ-≈ (Chain.stage C l) (followed C x p r)
      (𝒫.<-respʳ-≈ (Chain.stage C l) (followed C y q r)
        (Maps.Initial.strict (advance C r) h))

  reflexive : (C : Chain ℓ) (x : Occurrence C) → Equivalent C x x
  reflexive C (n , x) = n , Nat.≤-refl , Nat.≤-refl ,
    𝒫.≈-refl (Chain.stage C n) (image C (n , x) Nat.≤-refl)

  symmetric : (C : Chain ℓ) {x y : Occurrence C}
    → Equivalent C x y → Equivalent C y x
  symmetric C (k , p , q , r) =
    k , q , p , 𝒫.≈-sym (Chain.stage C k) r

  transitive : (C : Chain ℓ) {x y z : Occurrence C}
    → Equivalent C x y → Equivalent C y z → Equivalent C x z
  transitive C {x} {y} {z} (k , p , q , r) (l , s , t , u) =
    (k ⊔ l) , Nat.≤-trans p a , Nat.≤-trans t b ,
    𝒫.≈-trans Q (raise-≈ C {x} {y} p q a r)
      (𝒫.≈-trans Q
        (aligned C y (Nat.≤-trans q a) (Nat.≤-trans s b))
        (raise-≈ C {y} {z} s t b u))
    where
    a = Nat.m≤m⊔n k l
    b = Nat.m≤n⊔m k l
    Q = Chain.stage C (k ⊔ l)

  strict-transitive : (C : Chain ℓ) {x y z : Occurrence C}
    → Strict C x y → Strict C y z → Strict C x z
  strict-transitive C {x} {y} {z} (k , p , q , r) (l , s , t , u) =
    (k ⊔ l) , Nat.≤-trans p a , Nat.≤-trans t b ,
    𝒫.<-trans Q
      (𝒫.<-respʳ-≈ Q
        (aligned C y (Nat.≤-trans q a) (Nat.≤-trans s b))
        (raise-< C {x} {y} p q a r))
      (raise-< C {y} {z} s t b u)
    where
    a = Nat.m≤m⊔n k l
    b = Nat.m≤n⊔m k l
    Q = Chain.stage C (k ⊔ l)

  respˡ : (C : Chain ℓ) {x x′ y : Occurrence C}
    → Equivalent C x x′ → Strict C x y → Strict C x′ y
  respˡ C {x} {x′} {y} (k , p , q , r) (l , s , t , u) =
    (k ⊔ l) , Nat.≤-trans q a , Nat.≤-trans t b ,
    𝒫.<-respˡ-≈ Q
      (𝒫.≈-trans Q
        (aligned C x (Nat.≤-trans s b) (Nat.≤-trans p a))
        (raise-≈ C {x} {x′} p q a r))
      (raise-< C {x} {y} s t b u)
    where
    a = Nat.m≤m⊔n k l
    b = Nat.m≤n⊔m k l
    Q = Chain.stage C (k ⊔ l)

  respʳ : (C : Chain ℓ) {x y y′ : Occurrence C}
    → Equivalent C y y′ → Strict C x y → Strict C x y′
  respʳ C {x} {y} {y′} (k , p , q , r) (l , s , t , u) =
    (k ⊔ l) , Nat.≤-trans s b , Nat.≤-trans q a ,
    𝒫.<-respʳ-≈ Q
      (𝒫.≈-trans Q
        (aligned C y (Nat.≤-trans t b) (Nat.≤-trans p a))
        (raise-≈ C {y} {y′} p q a r))
      (raise-< C {x} {y} s t b u)
    where
    a = Nat.m≤m⊔n k l
    b = Nat.m≤n⊔m k l
    Q = Chain.stage C (k ⊔ l)

  preserve-≈ : (C : Chain ℓ) (n : ℕ) {x y : 𝒫.X (Chain.stage C n)}
    → 𝒫._≈_ (Chain.stage C n) x y → Equivalent C (n , x) (n , y)
  preserve-≈ C n p = n , Nat.≤-refl , Nat.≤-refl ,
    Maps.Initial.resp (advance C Nat.≤-refl) p

  preserve-< : (C : Chain ℓ) (n : ℕ) {x y : 𝒫.X (Chain.stage C n)}
    → 𝒫._<_ (Chain.stage C n) x y → Strict C (n , x) (n , y)
  preserve-< C n p = n , Nat.≤-refl , Nat.≤-refl ,
    Maps.Initial.strict (advance C Nat.≤-refl) p

  reflect : (C : Chain ℓ) (n : ℕ) {x y : 𝒫.X (Chain.stage C n)}
    → Strict C (n , x) (n , y) → 𝒫._<_ (Chain.stage C n) x y
  reflect C n {x} {y} (k , p , q , r) =
    Maps.Initial.reflect (advance C p)
      (𝒫.<-respʳ-≈ (Chain.stage C k) (aligned C (n , y) q p) r)

  cover : (C : Chain ℓ) (n : ℕ) (x : 𝒫.X (Chain.stage C n))
    → (y : Occurrence C) → Strict C y (n , x)
    → Σ (𝒫.X (Chain.stage C n)) (λ z → Equivalent C (n , z) y)
  cover C n x y (k , p , q , r)
    with Maps.Initial.lower (advance C q) x (image C y p) r
  ... | z , h = z , k , q , p , h

  accessible : (C : Chain ℓ) (n : ℕ) (x : 𝒫.X (Chain.stage C n))
    → Acc (𝒫._<_ (Chain.stage C n)) x
    → (y : Occurrence C) → Equivalent C y (n , x) → Acc (Strict C) y
  accessible C n x (acc smaller) y q = acc λ z p →
    let
      r = respʳ C q p
      a , h = cover C n x z r
      a<x = reflect C n (respˡ C (symmetric C h) r)
    in accessible C n a (smaller a a<x) z (symmetric C h)

  compare : (C : Chain ℓ) (x y : Occurrence C)
    → Strict C x y ⊎ (Equivalent C x y ⊎ Strict C y x)
  compare C x y with 𝒫.compare (Chain.stage C (proj₁ x ⊔ proj₁ y))
    (image C x (Nat.m≤m⊔n (proj₁ x) (proj₁ y)))
    (image C y (Nat.m≤n⊔m (proj₁ x) (proj₁ y)))
  ... | inj₁ p = inj₁ ((proj₁ x ⊔ proj₁ y) ,
    Nat.m≤m⊔n (proj₁ x) (proj₁ y) , Nat.m≤n⊔m (proj₁ x) (proj₁ y) , p)
  ... | inj₂ (inj₁ p) = inj₂ (inj₁ ((proj₁ x ⊔ proj₁ y) ,
    Nat.m≤m⊔n (proj₁ x) (proj₁ y) , Nat.m≤n⊔m (proj₁ x) (proj₁ y) , p))
  ... | inj₂ (inj₂ p) = inj₂ (inj₂ ((proj₁ x ⊔ proj₁ y) ,
    Nat.m≤n⊔m (proj₁ x) (proj₁ y) , Nat.m≤m⊔n (proj₁ x) (proj₁ y) , p))

  strip : (C : Chain ℓ) → Maybe (Presented.Diagonal.X (Chain.stage C))
    → Maybe (Occurrence C)
  strip C nothing = nothing
  strip C (just (n , Presented.Diagonal.Successor.point x)) = just (n , x)
  strip C (just (n , Presented.Diagonal.Successor.top)) = nothing

  enumeration : (C : Chain ℓ) → ℕ → Maybe (Occurrence C)
  enumeration C n = strip C (Presented.Diagonal.enum (Chain.stage C) n)

  enumerated : (C : Chain ℓ) (x : Occurrence C)
    → Σ ℕ (λ n → Σ (Occurrence C)
        (λ y → (enumeration C n ≡ just y) × Equivalent C y x))
  enumerated C (n , x) with Presented.Diagonal.covers (Chain.stage C)
    (n , Presented.Diagonal.Successor.point x)
  ... | m , (.n , Presented.Diagonal.Successor.point y) , p ,
      Presented.Diagonal.same (Presented.Diagonal.Successor.point≈ q) =
    m , (n , y) , cong (strip C) p , preserve-≈ C n q

  abstract
    well-founded : (C : Chain ℓ) (x : Occurrence C) → Acc (Strict C) x
    well-founded C (n , x) = accessible C n x
      (𝒫.<-wf (Chain.stage C n) x) (n , x) (reflexive C (n , x))

  raw : Chain ℓ → 𝒫 ℓ
  raw C = record
    { X = Occurrence C ; _≈_ = Equivalent C ; _<_ = Strict C
    ; ≈-refl = reflexive C ; ≈-sym = symmetric C ; ≈-trans = transitive C
    ; <-trans = strict-transitive C ; <-respˡ-≈ = respˡ C ; <-respʳ-≈ = respʳ C
    ; <-wf = well-founded C
    ; compare = compare C ; enum = enumeration C ; covers = enumerated C
    }

  raw-stage : (C : Chain ℓ) (n : ℕ) → Maps.Initial (Chain.stage C n) (raw C)
  raw-stage C n = record
    { map = n ,_ ; resp = preserve-≈ C n ; strict = preserve-< C n
    ; lower = cover C n }

-- Seal the normalized carrier; its stage equations and coverage below
-- support subsequent comparisons without unfolding the search construction.
abstract
  Point : Chain ℓ → Set
  Point C = Normal.Point (raw C)

  order : (C : Chain ℓ) → Order.Order (Point C)
  order C = Normal.order (raw C)

  completion : Chain ℓ → 𝒫 ℓ
  completion C = Exact.normalized (raw C)

  equal : (C : Chain ℓ) {x y : 𝒫.X (completion C)}
    → 𝒫._≈_ (completion C) x y → x ≡ y
  equal C p = cong lift (lower p)

  strict-unique : (C : Chain ℓ) {x y : 𝒫.X (completion C)}
    → (p q : 𝒫._<_ (completion C) x y) → p ≡ q
  strict-unique C {x} {y} p q = cong lift
    (Normal.strict-unique (raw C) {a = lower x} {b = lower y}
      (lower p) (lower q))

  stage : (C : Chain ℓ) (n : ℕ)
    → Maps.Initial (Chain.stage C n) (completion C)
  stage C n = Maps.compose (raw-stage C n) (Exact.quotient (raw C))

  coverage : (C : Chain ℓ) (y : 𝒫.X (completion C))
    → Σ ℕ (λ n → Σ (𝒫.X (Chain.stage C n))
        (λ x → Maps.Initial.map (stage C n) x ≡ y))
  coverage C y with Normal.representative (raw C) (lower y)
    | Normal.class-representative (raw C) (lower y)
  ... | n , x | p = n , x , cong lift p

  compatible : (C : Chain ℓ) (n : ℕ) (x : 𝒫.X (Chain.stage C n))
    → Maps.Initial.map (stage C (suc n)) (Maps.Initial.map (Chain.edge C n) x)
      ≡ Maps.Initial.map (stage C n) x
  compatible C n x = equal C (Maps.Uniqueness.pointwise
    (Maps.compose (Chain.edge C n) (stage C (suc n))) (stage C n) x)

  private
    coherent : (C : Chain ℓ) (Q : 𝒫 ℓ)
      → (f : (n : ℕ) → Maps.Initial (Chain.stage C n) Q)
      → {m n : ℕ} (p : m ≤ n) (x : 𝒫.X (Chain.stage C m))
      → 𝒫._≈_ Q (Maps.Initial.map (f n) (Maps.Initial.map (advance C p) x))
          (Maps.Initial.map (f m) x)
    coherent C Q f {m} {n} p =
      Maps.Uniqueness.pointwise (Maps.compose (advance C p) (f n)) (f m)

    fold : (C : Chain ℓ) (Q : 𝒫 ℓ)
      → ((n : ℕ) → Maps.Initial (Chain.stage C n) Q)
      → Maps.Initial (raw C) Q
    fold C Q f = record
      { map = λ { (n , x) → Maps.Initial.map (f n) x }
      ; resp = λ { {n , x} {m , y} (k , p , q , r) →
          𝒫.≈-trans Q (𝒫.≈-sym Q (coherent C Q f p x))
            (𝒫.≈-trans Q (Maps.Initial.resp (f k) r) (coherent C Q f q y)) }
      ; strict = λ { {n , x} {m , y} (k , p , q , r) →
          𝒫.<-respˡ-≈ Q (coherent C Q f p x)
            (𝒫.<-respʳ-≈ Q (coherent C Q f q y)
              (Maps.Initial.strict (f k) r)) }
      ; lower = λ { (n , x) y p →
          let z , q = Maps.Initial.lower (f n) x y p in (n , z) , q }
      }

  least : (C : Chain ℓ) (Q : 𝒫 ℓ)
    → ((n : ℕ) → Maps.Initial (Chain.stage C n) Q)
    → Maps.Initial (completion C) Q
  least C Q f = Maps.compose (Exact.section (raw C)) (fold C Q f)

  least-β : (C : Chain ℓ) (Q : 𝒫 ℓ)
    → (f : (n : ℕ) → Maps.Initial (Chain.stage C n) Q)
    → (n : ℕ) (x : 𝒫.X (Chain.stage C n))
    → 𝒫._≈_ Q
        (Maps.Initial.map (least C Q f) (Maps.Initial.map (stage C n) x))
        (Maps.Initial.map (f n) x)
  least-β C Q f n = Maps.Uniqueness.pointwise
    (Maps.compose (stage C n) (least C Q f)) (f n)

  unique : (C : Chain ℓ) (Q : 𝒫 ℓ)
    → (f g : Maps.Initial (completion C) Q) → (x : 𝒫.X (completion C))
    → 𝒫._≈_ Q (Maps.Initial.map f x) (Maps.Initial.map g x)
  unique C Q = Maps.Uniqueness.pointwise

  exhaustion : (C : Chain ℓ) (Q : 𝒫 ℓ)
    → (f : (n : ℕ) → Maps.Initial (Chain.stage C n) Q)
    → ((y : 𝒫.X Q) → Σ ℕ (λ n → Σ (𝒫.X (Chain.stage C n))
        (λ x → 𝒫._≈_ Q (Maps.Initial.map (f n) x) y)))
    → completion C Presented.≃𝒫 Q
  exhaustion C Q f covers = Maps.onto (least C Q f) λ y →
    let n , x , p = covers y in Maps.Initial.map (stage C n) x ,
      𝒫.≈-trans Q (least-β C Q f n x) p

  private
    -- Compatible stage embeddings agree along every iterate of the edges.
    steady : (C : Chain ℓ) (Q : 𝒫 ℓ)
      → (f : (n : ℕ) → Maps.Embedding (Chain.stage C n) Q)
      → Compatible C Q f
      → {m n : ℕ} (p : m ≤′ n) (x : 𝒫.X (Chain.stage C m))
      → 𝒫._≈_ Q
          (Maps.Embedding.map (f n) (Maps.Initial.map (iterate C p) x))
          (Maps.Embedding.map (f m) x)
    steady C Q f h ≤′-refl x = 𝒫.≈-refl Q _
    steady C Q f h (≤′-step {n = n} p) x = 𝒫.≈-trans Q
      (h n (Maps.Initial.map (iterate C p) x)) (steady C Q f h p x)

    -- The stage embeddings on the raw union of all stages.
    gather : (C : Chain ℓ) (Q : 𝒫 ℓ)
      → (f : (n : ℕ) → Maps.Embedding (Chain.stage C n) Q)
      → Compatible C Q f → Maps.Embedding (raw C) Q
    gather C Q f h = record
      { map = λ { (n , x) → Maps.Embedding.map (f n) x }
      ; resp = λ { {n , x} {m , y} (k , p , q , r) →
          𝒫.≈-trans Q (𝒫.≈-sym Q (steady C Q f h (Nat.≤⇒≤′ p) x))
            (𝒫.≈-trans Q (Maps.Embedding.resp (f k) r)
              (steady C Q f h (Nat.≤⇒≤′ q) y)) }
      ; strict = λ { {n , x} {m , y} (k , p , q , r) →
          𝒫.<-respˡ-≈ Q (steady C Q f h (Nat.≤⇒≤′ p) x)
            (𝒫.<-respʳ-≈ Q (steady C Q f h (Nat.≤⇒≤′ q) y)
              (Maps.Embedding.strict (f k) r)) }
      }

  -- Mathematical shape: embeddings fₙ : Cₙ → Q with fₙ₊₁ ∘ eₙ ≈ fₙ give an
  -- embedding sup C → Q through every stage. No leastness is claimed.
  embed : (C : Chain ℓ) (Q : 𝒫 ℓ)
    → (f : (n : ℕ) → Maps.Embedding (Chain.stage C n) Q)
    → Compatible C Q f → Maps.Embedding (completion C) Q
  embed C Q f h = Maps.composite
    (Maps.Initial.embedding (Exact.section (raw C))) (gather C Q f h)

  embed-β : (C : Chain ℓ) (Q : 𝒫 ℓ)
    → (f : (n : ℕ) → Maps.Embedding (Chain.stage C n) Q)
    → (h : Compatible C Q f) (n : ℕ) (x : 𝒫.X (Chain.stage C n))
    → 𝒫._≈_ Q
        (Maps.Embedding.map (embed C Q f h) (Maps.Initial.map (stage C n) x))
        (Maps.Embedding.map (f n) x)
  embed-β C Q f h n x = Maps.Embedding.resp (gather C Q f h)
    (Maps.Uniqueness.pointwise
      (Maps.compose (stage C n) (Exact.section (raw C))) (raw-stage C n) x)

constant : 𝒫 ℓ → Chain ℓ
constant P = record { stage = λ _ → P ; edge = λ _ → Maps.identity P }

stationary : (P : 𝒫 ℓ) → completion (constant P) Presented.≃𝒫 P
stationary P = exhaustion (constant P) P (λ _ → Maps.identity P)
  (λ x → zero , x , 𝒫.≈-refl P x)

principal : (P : ℕ → 𝒫 ℓ)
  → ((n : ℕ) → Maps.Segment (P n) (P (suc n))) → Chain ℓ
principal P s = record { stage = P ; edge = λ n → Maps.inclusion (s n) }

segment : (P : ℕ → 𝒫 ℓ)
  → (s : (n : ℕ) → Maps.Segment (P n) (P (suc n)))
  → (n : ℕ) → Maps.Segment (P n) (completion (principal P s))
segment P s n = Maps.along (s n) (stage (principal P s) (suc n))

equivalence : (C D : Chain ℓ)
  → ((n : ℕ) → Chain.stage C n Presented.≃𝒫 Chain.stage D n)
  → completion C Presented.≃𝒫 completion D
equivalence C D e = Maps.antisymmetry
  (least C (completion D) (λ n →
    Maps.compose (Maps.equivalence (e n)) (stage D n)))
  (least D (completion C) (λ n →
    Maps.compose (Maps.equivalence (Presented.≃𝒫-sym (e n))) (stage C n)))

subsequence : (C : Chain ℓ) (σ : ℕ → ℕ)
  → ((n : ℕ) → σ n ≤ σ (suc n)) → Chain ℓ
subsequence C σ ascending = record
  { stage = λ n → Chain.stage C (σ n)
  ; edge = λ n → advance C (ascending n)
  }

cofinal : (C : Chain ℓ) (σ : ℕ → ℕ)
  → (ascending : (n : ℕ) → σ n ≤ σ (suc n))
  → ((n : ℕ) → Σ ℕ (λ m → n ≤ σ m))
  → completion (subsequence C σ ascending) Presented.≃𝒫 completion C
cofinal C σ ascending covers =
  Maps.antisymmetry {P = completion D} {Q = completion C} forward backward
  where
  D : Chain _
  D = subsequence C σ ascending

  forward : Maps.Initial (completion D) (completion C)
  forward = least D (completion C) (λ n → stage C (σ n))

  members : (n : ℕ) → Maps.Initial (Chain.stage C n) (completion D)
  members n with covers n
  ... | m , p = Maps.compose {P = Chain.stage C n}
    {Q = Chain.stage C (σ m)} {R = completion D}
    (advance C {m = n} {n = σ m} p) (stage D m)

  backward : Maps.Initial (completion C) (completion D)
  backward = least C (completion D) members
