{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Arithmetic.Subtraction where

-- Left subtraction along an initial map f : P → Q. Its datum is a decision
-- at every point of Q between a preimage under f and lying above the
-- whole image. From it, the remainder Q − f is the presentation of the
-- points above the image, and P + (Q − f) ≃ Q with P entering along f.
-- Conversely, an equivalence P + R ≃ Q that agrees with f on P decides
-- the image of f, so the decision is exactly the datum subtraction needs,
-- and R is then equivalent to the remainder.
-- A proper segment decides its image by comparison with its ceiling, and
-- an equivalence reaches every point; so a split ≤, a proper segment or an
-- equivalence, has a subtraction.

open import Agda.Primitive using (Level)
open import Data.Empty using (⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (tt)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; trans; subst)

open import SPT.Cubical.Core.WellFounded.Pullback using (pullback-wf)
import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
import SPT.Cubical.OrdinalGeometry.Presentation.Map as Maps
open import SPT.Cubical.OrdinalGeometry.Presentation.Sum using (_+_; left)
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Characterization using
  (bijection)

private
  variable
    ℓ : Level
    P Q : 𝒫 ℓ

-- The points of Q above the whole image of f.
Above : {P Q : 𝒫 ℓ} → Maps.Initial P Q → 𝒫.X Q → Set ℓ
Above {P = P} {Q = Q} f y =
  (x : 𝒫.X P) → 𝒫._<_ Q (Maps.Initial.map f x) y

-- Mathematical shape: Π y : Q. (Σ x. f x ≈ y) ⊎ (Π x. f x < y).
Decided : {P Q : 𝒫 ℓ} → Maps.Initial P Q → Set ℓ
Decided {P = P} {Q = Q} f = (y : 𝒫.X Q)
  → Σ (𝒫.X P) (λ x → 𝒫._≈_ Q (Maps.Initial.map f x) y) ⊎ Above f y

------------------------------------------------------------------------
-- The remainder

-- Mathematical shape: Q − f = {y ∈ Q | Π x. f x < y}, ordered as in Q.
-- Its enumeration keeps the enumerated points of Q that lie above.
remainder : {P Q : 𝒫 ℓ} (f : Maps.Initial P Q) → Decided f → 𝒫 ℓ
remainder {ℓ} {P} {Q} f d = record
  { X = Point
  ; _≈_ = λ u v → proj₁ u Q.≈ proj₁ v
  ; _<_ = λ u v → proj₁ u Q.< proj₁ v
  ; ≈-refl = λ u → Q.≈-refl (proj₁ u)
  ; ≈-sym = Q.≈-sym
  ; ≈-trans = Q.≈-trans
  ; <-trans = Q.<-trans
  ; <-respˡ-≈ = Q.<-respˡ-≈
  ; <-respʳ-≈ = Q.<-respʳ-≈
  ; <-wf = pullback-wf {rank = proj₁} Q.<-wf
  ; compare = λ u v → Q.compare (proj₁ u) (proj₁ v)
  ; enum = λ n → keep (Q.enum n)
  ; covers = covers
  }
  where
  module Q = 𝒫 Q

  Point : Set ℓ
  Point = Σ Q.X (Above f)

  choose : (y : Q.X)
    → Σ (𝒫.X P) (λ x → Maps.Initial.map f x Q.≈ y) ⊎ Above f y
    → Maybe Point
  choose y (inj₁ _) = nothing
  choose y (inj₂ a) = just (y , a)

  keep : Maybe Q.X → Maybe Point
  keep nothing = nothing
  keep (just y) = choose y (d y)

  -- An enumerated representative of a point above the image is above it.
  covers : (u : Point) → Σ ℕ (λ n → Σ Point (λ r →
    (keep (Q.enum n) ≡ just r) × (proj₁ r Q.≈ proj₁ u)))
  covers (y , a) with Q.covers y
  ... | n , r , e , r≈y with d r in dr
  ...   | inj₁ (x , q) = ⊥-elim
    (Presented.Presentation.≈↛< Q (Q.≈-trans q r≈y) (a x))
  ...   | inj₂ a′ =
    n , (r , a′) , trans (cong keep e) (cong (choose r) dr) , r≈y

private
  -- P along f, then the remainder, inside Q.
  join : (f : Maps.Initial P Q) (d : Decided f)
    → 𝒫.X (P + remainder f d) → 𝒫.X Q
  join f d (inj₁ x) = Maps.Initial.map f x
  join f d (inj₂ (y , a)) = y

  cover : (f : Maps.Initial P Q) (d : Decided f) (y : 𝒫.X Q)
    → Σ (𝒫.X (P + remainder f d)) (λ u → 𝒫._≈_ Q (join f d u) y)
  cover {Q = Q} f d y with d y
  ... | inj₁ (x , e) = inj₁ x , e
  ... | inj₂ a = inj₂ (y , a) , 𝒫.≈-refl Q y

  rejoin : (f : Maps.Initial P Q) (d : Decided f)
    → Maps.Initial (P + remainder f d) Q
  rejoin f d = record
    { map = join f d
    ; resp = λ where
        {inj₁ _} {inj₁ _} p → Maps.Initial.resp f p
        {inj₁ _} {inj₂ _} ()
        {inj₂ _} {inj₁ _} ()
        {inj₂ _} {inj₂ _} p → p
    ; strict = λ where
        {inj₁ _} {inj₁ _} p → Maps.Initial.strict f p
        {inj₁ x} {inj₂ (y , a)} _ → a x
        {inj₂ _} {inj₁ _} ()
        {inj₂ _} {inj₂ _} p → p
    ; lower = λ _ y _ → cover f d y
    }

-- Mathematical shape: P + (Q − f) ≃ Q.
equation : (f : Maps.Initial P Q) (d : Decided f)
  → (P + remainder f d) Presented.≃𝒫 Q
equation f d = Maps.onto (rejoin f d) (cover f d)

-- P enters the equivalence along f.
equation-left : (f : Maps.Initial P Q) (d : Decided f) (x : 𝒫.X P)
  → 𝒫._≈_ Q (Presented._≃𝒫_.to (equation f d) (inj₁ x))
      (Maps.Initial.map f x)
equation-left f d x = Maps.onto-β (rejoin f d) (cover f d) (inj₁ x)

------------------------------------------------------------------------
-- Exactness of the datum

-- An equivalence P + R ≃ Q agreeing with f on P decides the image of f:
-- a point comes from the left summand or from R, which lies above P.
decided : {P Q : 𝒫 ℓ} (f : Maps.Initial P Q) (R : 𝒫 ℓ)
  (e : (P + R) Presented.≃𝒫 Q)
  → ((x : 𝒫.X P) → 𝒫._≈_ Q (Presented._≃𝒫_.to e (inj₁ x))
      (Maps.Initial.map f x))
  → Decided f
decided {P = P} {Q = Q} f R e agree y = answer (E.from y) refl
  where
  module E = Presented._≃𝒫_ e

  back : (u : 𝒫.X (P + R)) → E.from y ≡ u → 𝒫._≈_ Q (E.to u) y
  back u r = subst (λ w → 𝒫._≈_ Q (E.to w) y) r (E.to-from-≈ y)

  answer : (u : 𝒫.X (P + R)) → E.from y ≡ u
    → Σ (𝒫.X P) (λ x → 𝒫._≈_ Q (Maps.Initial.map f x) y) ⊎ Above f y
  answer (inj₁ x) r =
    inj₁ (x , 𝒫.≈-trans Q (𝒫.≈-sym Q (agree x)) (back (inj₁ x) r))
  answer (inj₂ z) r = inj₂ λ x → 𝒫.<-respˡ-≈ Q (agree x)
    (𝒫.<-respʳ-≈ Q (back (inj₂ z) r) (E.to-< {inj₁ x} {inj₂ z} tt))

-- The left summand of an equivalence P + R ≃ Q, as an initial map, and
-- the decision of its image.
summand : {P R Q : 𝒫 ℓ} → (P + R) Presented.≃𝒫 Q → Maps.Initial P Q
summand {P = P} {R} e = Maps.compose (left P R) (Maps.equivalence e)

split : {P R Q : 𝒫 ℓ} (e : (P + R) Presented.≃𝒫 Q) → Decided (summand e)
split {R = R} {Q} e = decided (summand e) R e (λ x → 𝒫.≈-refl Q _)

-- The remainder is unique: R is the remainder along the left summand.
complement : {P R Q : 𝒫 ℓ} (e : (P + R) Presented.≃𝒫 Q)
  → R Presented.≃𝒫 remainder (summand e) (split e)
complement {P = P} {R} {Q} e = bijection embedding covers
  where
  module E = Presented._≃𝒫_ e

  embedding : Maps.Embedding R (remainder (summand e) (split e))
  embedding = record
    { map = λ r → E.to (inj₂ r) , λ x → E.to-< {inj₁ x} {inj₂ r} tt
    ; resp = λ {r} {r′} p → E.to-≈ {inj₂ r} {inj₂ r′} p
    ; strict = λ {r} {r′} p → E.to-< {inj₂ r} {inj₂ r′} p
    }

  covers : (u : 𝒫.X (remainder (summand e) (split e)))
    → Σ (𝒫.X R) (λ r → 𝒫._≈_ Q (E.to (inj₂ r)) (proj₁ u))
  covers (y , a) = answer (E.from y) refl
    where
    back : (w : 𝒫.X (P + R)) → E.from y ≡ w → 𝒫._≈_ Q (E.to w) y
    back w r = subst (λ v → 𝒫._≈_ Q (E.to v) y) r (E.to-from-≈ y)

    answer : (w : 𝒫.X (P + R)) → E.from y ≡ w
      → Σ (𝒫.X R) (λ r → 𝒫._≈_ Q (E.to (inj₂ r)) y)
    answer (inj₂ r) eq = r , back (inj₂ r) eq
    answer (inj₁ x) eq =
      ⊥-elim (Presented.Presentation.≈↛< Q (back (inj₁ x) eq) (a x))

-- Initial maps with the same points above them have equivalent
-- remainders.
respect : {P P′ Q : 𝒫 ℓ} (f : Maps.Initial P Q) (g : Maps.Initial P′ Q)
  (d : Decided f) (d′ : Decided g)
  → ((y : 𝒫.X Q) → Above f y → Above g y)
  → ((y : 𝒫.X Q) → Above g y → Above f y)
  → remainder f d Presented.≃𝒫 remainder g d′
respect {Q = Q} f g d d′ fg gf = record
  { to = λ u → proj₁ u , fg (proj₁ u) (proj₂ u)
  ; from = λ v → proj₁ v , gf (proj₁ v) (proj₂ v)
  ; to-≈ = λ p → p
  ; from-≈ = λ p → p
  ; to-< = λ p → p
  ; from-< = λ p → p
  ; from-to-≈ = λ u → 𝒫.≈-refl Q (proj₁ u)
  ; to-from-≈ = λ v → 𝒫.≈-refl Q (proj₁ v)
  }

------------------------------------------------------------------------
-- Split ≤

-- A proper segment decides its image by comparison with its ceiling.
segment : (s : Maps.Segment P Q) → Decided (Maps.inclusion s)
segment {P = P} {Q = Q} s y = side (𝒫.compare Q y Bound.ceiling)
  where
  module Bound = Presented._≺𝒫_ (Maps.Segment.bound s)

  side : 𝒫._<_ Q y Bound.ceiling
    ⊎ (𝒫._≈_ Q y Bound.ceiling ⊎ 𝒫._<_ Q Bound.ceiling y)
    → Σ (𝒫.X P) (λ x → 𝒫._≈_ Q (Bound.to x) y)
      ⊎ Above (Maps.inclusion s) y
  side (inj₁ p) = inj₁ (Maps.Segment.covers s y p)
  side (inj₂ (inj₁ p)) = inj₂ λ x →
    𝒫.<-respʳ-≈ Q (𝒫.≈-sym Q p) (Bound.below x)
  side (inj₂ (inj₂ p)) = inj₂ λ x → 𝒫.<-trans Q (Bound.below x) p

-- An equivalence reaches every point.
equivalence : (e : P Presented.≃𝒫 Q) → Decided (Maps.equivalence e)
equivalence e y =
  inj₁ (Presented._≃𝒫_.from e y , Presented._≃𝒫_.to-from-≈ e y)

-- Mathematical shape: P < Q or P ≃ Q gives R with P + R ≃ Q.
subtract : {P Q : 𝒫 ℓ} → Maps.Segment P Q ⊎ P Presented.≃𝒫 Q
  → Σ (𝒫 ℓ) (λ R → (P + R) Presented.≃𝒫 Q)
subtract (inj₁ s) = remainder (Maps.inclusion s) (segment s) ,
  equation (Maps.inclusion s) (segment s)
subtract (inj₂ e) = remainder (Maps.equivalence e) (equivalence e) ,
  equation (Maps.equivalence e) (equivalence e)
