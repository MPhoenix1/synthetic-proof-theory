{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Arithmetic.Comparison where

-- Comparison of presentations under LPO, the converse of the ambient
-- discriminators (Arithmetic.Ambient.Discriminator). Normalization presents
-- each P by an exact order on its least enumeration indices, where LPO
-- makes any two comparable (ExactOrder.Comparison); quotient and section
-- carry the comparison back: P ≤ Q ⊎ Q < P (comparable). Hence, for all
-- presentations, under LPO:
-- - rows 16–18: Dec (P < Q) (decidable), every ≤ splits into < or ≃
--   (split), trichotomy;
-- - row 2: ≤ followed by < is < (along); row 15: Dec (P < ω) (finite);
-- - Dec (P ≤ Q) (initial) and Dec (P ≃ Q) (equivalent);
-- - row 5: the successor is monotone for ≤ and for <;
-- - row 13: every initial map has a decided image, so P ≤ Q gives
--   P + R ≃ Q (decided, subtract);
-- - rows 6 and 8: every ℕ-family has a supremum, the completion of the
--   chain of its running maxima (Running, supremum, join), and a strict
--   upper bound, its successor (bound).
-- With the discriminators each of these is equivalent to LPO
-- (Comparison.Strength).

open import Agda.Primitive using (Level)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing; maybe′)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
import SPT.Cubical.OrdinalGeometry.Presentation.Map as Maps
open import SPT.Cubical.OrdinalGeometry.Presentation.Sum using (_+_)
import SPT.Cubical.OrdinalGeometry.Presentation.Limit as Limit
import SPT.Cubical.OrdinalGeometry.Presentation.Limit.Discriminator as Stream
import SPT.Cubical.OrdinalGeometry.Presentation.Normalization as Normalization
import SPT.Cubical.OrdinalGeometry.Presentation.Normalization.Presentation
  as Normalized
import SPT.Cubical.OrdinalGeometry.ExactOrder.Comparison as Exact
open import SPT.Cubical.OrdinalGeometry.Operation.Normal using (precompose)
import SPT.Cubical.OrdinalGeometry.Arithmetic.Characterization
  as Characterization
open Characterization using (Supremum)
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Ambient using (pair)
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Exponential using (omega)
import SPT.Cubical.OrdinalGeometry.Arithmetic.Successor as Successor
import SPT.Cubical.OrdinalGeometry.Arithmetic.Subtraction as Subtraction

private
  variable
    ℓ : Level

  true≢false : true ≡ false → ⊥
  true≢false ()

-- Mathematical shape: P < Q → Q ≤ P → ⊥.
proper : {P Q : 𝒫 ℓ} → Maps.Segment P Q → Maps.Initial Q P → ⊥
proper {P = P} s f =
  Presented.Embedding.irrefl P (Maps.bounded (Maps.Segment.bound s) f)

private
  -- Mathematical shape: x ≈ y, as a Boolean, by comparison in Q.
  same : (Q : 𝒫 ℓ) → 𝒫.X Q → 𝒫.X Q → Bool
  same Q x y =
    [ (λ _ → false) , [ (λ _ → true) , (λ _ → false) ]′ ]′ (𝒫.compare Q x y)

  same-sound : (Q : 𝒫 ℓ) (x y : 𝒫.X Q) → same Q x y ≡ true → 𝒫._≈_ Q x y
  same-sound Q x y = at (𝒫.compare Q x y)
    where
    at : (d : 𝒫._<_ Q x y ⊎ (𝒫._≈_ Q x y ⊎ 𝒫._<_ Q y x))
      → [ (λ _ → false) , [ (λ _ → true) , (λ _ → false) ]′ ]′ d ≡ true
      → 𝒫._≈_ Q x y
    at (inj₁ _) ()
    at (inj₂ (inj₁ e)) _ = e
    at (inj₂ (inj₂ _)) ()

  same-complete : (Q : 𝒫 ℓ) (x y : 𝒫.X Q) → 𝒫._≈_ Q x y
    → same Q x y ≡ true
  same-complete Q x y e = at (𝒫.compare Q x y)
    where
    at : (d : 𝒫._<_ Q x y ⊎ (𝒫._≈_ Q x y ⊎ 𝒫._<_ Q y x))
      → [ (λ _ → false) , [ (λ _ → true) , (λ _ → false) ]′ ]′ d ≡ true
    at (inj₁ p) = ⊥-elim (Presented.Presentation.≈↛< Q e p)
    at (inj₂ (inj₁ _)) = refl
    at (inj₂ (inj₂ p)) =
      ⊥-elim (Presented.Presentation.≈↛< Q (𝒫.≈-sym Q e) p)

module _ (lpo : Stream.LPO) where

  -- Mathematical shape: P ≤ Q ⊎ Q < P.
  comparable : (P Q : 𝒫 ℓ) → Maps.Initial P Q ⊎ Maps.Segment Q P
  comparable P Q =
    [ (λ f → inj₁ (Maps.compose (Normalized.quotient P)
        (Maps.compose (Normalized.initial f) (Normalized.section Q))))
    , (λ s → inj₂ (precompose
        (Maps.antisymmetry (Normalized.quotient Q) (Normalized.section Q))
        (Maps.along (Normalized.segment s) (Normalized.section P))))
    ]′ (Exact.comparable lpo (Normalization.order P) (Normalization.order Q))

  -- Mathematical shape: P < Q ⊎ P ≃ Q ⊎ Q < P (row 18).
  trichotomy : (P Q : 𝒫 ℓ)
    → Maps.Segment P Q ⊎ (P Presented.≃𝒫 Q ⊎ Maps.Segment Q P)
  trichotomy P Q =
    [ (λ f → [ (λ g → inj₂ (inj₁ (Maps.antisymmetry f g))) , inj₁ ]′
        (comparable Q P))
    , (λ s → inj₂ (inj₂ s))
    ]′ (comparable P Q)

  -- Mathematical shape: Dec (P < Q) (row 16).
  decidable : (P Q : 𝒫 ℓ) → Dec (Maps.Segment P Q)
  decidable P Q =
    [ yes
    , [ (λ e → no λ s → proper s (Maps.equivalence (Presented.≃𝒫-sym e)))
      , (λ s′ → no λ s → proper s (Maps.inclusion s′))
      ]′
    ]′ (trichotomy P Q)

  -- Mathematical shape: Dec (P ≤ Q).
  initial : (P Q : 𝒫 ℓ) → Dec (Maps.Initial P Q)
  initial P Q = [ yes , (λ s → no λ f → proper s f) ]′ (comparable P Q)

  -- Mathematical shape: Dec (P ≃ Q).
  equivalent : (P Q : 𝒫 ℓ) → Dec (P Presented.≃𝒫 Q)
  equivalent P Q =
    [ (λ s → no λ e → proper s (Maps.equivalence (Presented.≃𝒫-sym e)))
    , [ yes , (λ s → no λ e → proper s (Maps.equivalence e)) ]′
    ]′ (trichotomy P Q)

  -- Mathematical shape: P ≤ Q → P < Q ⊎ P ≃ Q (row 17).
  split : {P Q : 𝒫 ℓ} → Maps.Initial P Q
    → Maps.Segment P Q ⊎ P Presented.≃𝒫 Q
  split {P = P} {Q = Q} f =
    [ inj₁ , [ inj₂ , (λ s → ⊥-elim (proper s f)) ]′ ]′ (trichotomy P Q)

  -- Mathematical shape: P ≤ Q → Q < R → P < R (row 2).
  along : {P Q R : 𝒫 ℓ} → Maps.Initial P Q → Maps.Segment Q R
    → Maps.Segment P R
  along f s = Characterization.segment (split f) s

  -- Mathematical shape: Dec (P < ω) (row 15).
  finite : (P : 𝒫 ℓ) → Dec (Maps.Segment P omega)
  finite P = decidable P omega

  -- Mathematical shape: P ≤ Q → P + 1 ≤ Q + 1 (row 5).
  successor-initial : {P Q : 𝒫 ℓ} → Maps.Initial P Q
    → Maps.Initial (Maps.Successor.next P) (Maps.Successor.next Q)
  successor-initial {Q = Q} f =
    [ (λ s → Maps.compose (Maps.Segment.closed s)
        (Maps.Successor.initial Q))
    , (λ e → Maps.equivalence (Successor.respect e))
    ]′ (split f)

  -- Mathematical shape: P < Q → P + 1 < Q + 1 (row 5).
  successor-segment : {P Q : 𝒫 ℓ} → Maps.Segment P Q
    → Maps.Segment (Maps.Successor.next P) (Maps.Successor.next Q)
  successor-segment {Q = Q} s =
    along (Maps.Segment.closed s) (Maps.successor Q)

  -- Mathematical shape: Π y : Q. (Σ x. f x ≈ y) ⊎ (Π x. f x < y).
  decided : {P Q : 𝒫 ℓ} (f : Maps.Initial P Q) → Subtraction.Decided f
  decided {P = P} {Q = Q} f y =
    [ (λ h → inj₁ (found (𝒫.enum P (proj₁ h)) (proj₂ h)))
    , (λ none → inj₂ (above none))
    ]′ (lpo hit)
    where
    test : 𝒫.X P → Bool
    test x = same Q (Maps.Initial.map f x) y

    hit : ℕ → Bool
    hit n = maybe′ test false (𝒫.enum P n)

    found : (m : Maybe (𝒫.X P)) → maybe′ test false m ≡ true
      → Σ (𝒫.X P) (λ x → 𝒫._≈_ Q (Maps.Initial.map f x) y)
    found (just x) p = x , same-sound Q (Maps.Initial.map f x) y p
    found nothing ()

    missing : ((n : ℕ) → hit n ≡ false) → (z : 𝒫.X P)
      → 𝒫._≈_ Q (Maps.Initial.map f z) y → ⊥
    missing none z e =
      let n , r , selected , r≈z = 𝒫.covers P z
      in true≢false (trans
           (sym (same-complete Q (Maps.Initial.map f r) y
             (𝒫.≈-trans Q (Maps.Initial.resp f r≈z) e)))
           (trans (sym (cong (maybe′ test false) selected)) (none n)))

    above : ((n : ℕ) → hit n ≡ false) → Subtraction.Above f y
    above none x = place (𝒫.compare Q (Maps.Initial.map f x) y)
      where
      place : 𝒫._<_ Q (Maps.Initial.map f x) y
          ⊎ (𝒫._≈_ Q (Maps.Initial.map f x) y
            ⊎ 𝒫._<_ Q y (Maps.Initial.map f x))
        → 𝒫._<_ Q (Maps.Initial.map f x) y
      place (inj₁ p) = p
      place (inj₂ (inj₁ e)) = ⊥-elim (missing none x e)
      place (inj₂ (inj₂ p)) =
        let z , e = Maps.Initial.lower f x y p
        in ⊥-elim (missing none z e)

  -- Mathematical shape: P ≤ Q → Σ R. P + R ≃ Q (row 13).
  subtract : {P Q : 𝒫 ℓ} → Maps.Initial P Q
    → Σ (𝒫 ℓ) (λ R → (P + R) Presented.≃𝒫 Q)
  subtract f =
    Subtraction.remainder f (decided f) , Subtraction.equation f (decided f)

  -- The running maxima of a sequence F: a chain through members of F.
  module Running (F : ℕ → 𝒫 ℓ) where

    -- The maximum after the member k when F (suc n) arrives, with both
    -- members below it.
    next : (k n : ℕ) → Σ ℕ (λ m →
      Maps.Initial (F k) (F m) × Maps.Initial (F (suc n)) (F m))
    next k n =
      [ (λ f → k , Maps.identity (F k) , f)
      , (λ s → suc n , Maps.inclusion s , Maps.identity (F (suc n)))
      ]′ (comparable (F (suc n)) (F k))

    -- index n: the member that is the maximum of F 0, …, F n.
    index : ℕ → ℕ
    index zero = zero
    index (suc n) = proj₁ (next (index n) n)

    chain : Limit.Chain ℓ
    chain = record
      { stage = λ n → F (index n)
      ; edge = λ n → proj₁ (proj₂ (next (index n) n))
      }

    above : (n : ℕ) → Maps.Initial (F n) (F (index n))
    above zero = Maps.identity (F zero)
    above (suc n) = proj₂ (proj₂ (next (index n) n))

    -- Mathematical shape: sup F = completion of the running maxima.
    supremum : Supremum F (Limit.completion chain)
    supremum = record
      { member = λ n → Maps.compose (above n) (Limit.stage chain n)
      ; least = λ Q f → Limit.least chain Q (λ n → f (index n))
      }

  -- Mathematical shape: Π F : ℕ → 𝒫. Σ S. S = sup F (row 8).
  supremum : (F : ℕ → 𝒫 ℓ) → Σ (𝒫 ℓ) (Supremum F)
  supremum F = Limit.completion (Running.chain F) , Running.supremum F

  -- Mathematical shape: Π P Q. Σ S. S = sup (P, Q, Q, …) (row 6).
  join : (P Q : 𝒫 ℓ) → Σ (𝒫 ℓ) (Supremum (pair P Q))
  join P Q = supremum (pair P Q)

  -- Mathematical shape: Π F : ℕ → 𝒫. Σ S. Π n. F n < S, with S the
  -- successor of the supremum.
  bound : (F : ℕ → 𝒫 ℓ)
    → Σ (𝒫 ℓ) (λ S → (n : ℕ) → Maps.Segment (F n) S)
  bound F =
    Maps.Successor.next (proj₁ (supremum F))
    , λ n → along (Supremum.member (proj₂ (supremum F)) n)
        (Maps.successor (proj₁ (supremum F)))
