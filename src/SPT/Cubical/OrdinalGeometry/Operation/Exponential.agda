{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Operation.Exponential where

-- ω^P for every presented countable ordinal P and every ω₁ position. The
-- predecessor domain of ω^P consists of the finite decreasing supports over
-- the normalized points of P. Exponentiation acts on initial maps, that is
-- on inclusions of predecessor domains, hence on countable chains of them.
-- Every predecessor of ω^ at a chain's completion is captured by the
-- exponential of one stage, so ω^ commutes with completion. The empty
-- support is the least point of every ω^P, so ∅ ⊂ ω^P properly. ω^ also
-- acts on every order embedding, exponent by exponent: the exponents of a
-- point are its finite support, they move with the embedding, and they
-- determine the point.

open import Agda.Primitive using (Level)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_)
import Data.List as List
open import Data.List.Relation.Unary.All using (All)
open import Data.Nat using (ℕ; zero; suc)
import Data.Nat.Properties as Nat
open import Data.Product using (Σ; _,_; proj₁)
open import Data.Unit using (tt)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; trans)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
import SPT.Cubical.OrdinalGeometry.Presentation.Map as Maps
import SPT.Cubical.OrdinalGeometry.Presentation.Limit as Limit
import SPT.Cubical.OrdinalGeometry.Presentation.Normalization as Normal
import SPT.Cubical.OrdinalGeometry.Presentation.Normalization.Maps
  as NormalMaps
import SPT.Cubical.OrdinalGeometry.Presentation.Normalization.Presentation
  as Exact
import SPT.Cubical.OrdinalGeometry.ExactOrder.Maps as Orders
import SPT.Cubical.OrdinalGeometry.ExactOrder.Exponential.Support as Support
import SPT.Cubical.OrdinalGeometry.ExactOrder.Exponential.Order as Exponential
import SPT.Cubical.OrdinalGeometry.ExactOrder.Exponential.Initial
  as ExponentialInitial
import SPT.Cubical.OrdinalGeometry.Operation.Base as Operation
import SPT.Cubical.OrdinalGeometry.Operation.Normal as Normal
import SPT.Cubical.OrdinalGeometry.ExactOrder.Exponential.Embedding
  as ExponentialEmbedding

private
  variable
    ℓ : Level
    P Q : 𝒫 ℓ

  module Geometry = Presented.ω₁.Geometry

-- ω^ is sealed, so that comparing ω^P with ω^Q compares P with Q rather
-- than unfolding the normalized support order; its theorems below unfold
-- it locally.
opaque
  exp : 𝒫 ℓ → 𝒫 ℓ
  exp P = Exact.presentation (Exponential.Power.order (Normal.order P))

  -- An inclusion of predecessor domains P ⊆ Q gives ω^P ⊆ ω^Q. Each support
  -- maps exponentwise through the normalized map; no ceiling is required.
  initial : Maps.Initial P Q → Maps.Initial (exp P) (exp Q)
  initial f =
    Exact.initial (ExponentialInitial.initial (NormalMaps.initial f))

-- The new presentation enters the geometry through its own route.
position : (geometry : Presented.𝒫ω₁𝒢 ℓ)
  → Geometry.Position geometry → Geometry.Position geometry
position geometry p = Geometry.position geometry (exp (proj₁ p))

chain : Limit.Chain ℓ → Limit.Chain ℓ
chain C = record
  { stage = λ n → exp (Limit.Chain.stage C n)
  ; edge = λ n → initial (Limit.Chain.edge C n)
  }

private
  -- A normalized point of the completion is the image of a normalized point
  -- of one stage.
  exponent : (C : Limit.Chain ℓ) (a : Normal.Point (Limit.completion C))
    → Σ ℕ (λ n → Σ (Normal.Point (Limit.Chain.stage C n)) (λ u →
        NormalMaps.map (Limit.stage C n) u ≡ a))
  exponent C a
    with Limit.coverage C (Normal.representative (Limit.completion C) a)
  ... | n , x , p = n , Normal.class (Limit.Chain.stage C n) x ,
    trans (NormalMaps.map-β (Limit.stage C n) x)
      (trans (cong (Normal.class (Limit.completion C)) p)
        (Normal.class-representative (Limit.completion C) a))

opaque
  unfolding exp initial

  -- Mathematical shape: ω^(sup Pₙ) ≃ sup ω^Pₙ, with the stage maps of the
  -- right-hand completion sent to ω^ of the stage maps of the left.
  continuous : (C : Limit.Chain ℓ)
    → Limit.completion (chain C) Presented.≃𝒫 exp (Limit.completion C)
  continuous C = Limit.exhaustion (chain C) (exp (Limit.completion C))
    (λ n → initial (Limit.stage C n)) captured
    where
    -- The leading exponent fixes a stage; the support lies below the image
    -- of that exponent with one more copy, and returns through ω^ of the
    -- stage.
    captured : (y : 𝒫.X (exp (Limit.completion C)))
      → Σ ℕ (λ n → Σ (𝒫.X (exp (Limit.Chain.stage C n))) (λ x →
          𝒫._≈_ (exp (Limit.completion C))
            (Maps.Initial.map (initial (Limit.stage C n)) x) y))
    captured (lift ([] , tt)) = zero , lift ([] , tt) , lift refl
    captured (lift (((a , c) ∷ xs) , v)) with exponent C a
    ... | n , u , refl =
      n , Maps.Initial.lower (initial (Limit.stage C n))
        (lift (Stage.single u (suc c))) (lift (((b , c) ∷ xs) , v))
        (lift (Target.head (Target.Pair.within b (Nat.n<1+n c))))
      where
      module Stage = Support.Power (Normal.order (Limit.Chain.stage C n))
      module Target = Support.Power (Normal.order (Limit.completion C))

      b : Normal.Point (Limit.completion C)
      b = NormalMaps.map (Limit.stage C n) u

  -- A proper segment P ⊂ Q gives ω^P ⊂ ω^Q with ceiling ω^c at the old cut.
  segment : Maps.Segment P Q → Maps.Segment (exp P) (exp Q)
  segment s = Exact.segment
    (ExponentialEmbedding.Along.segment (NormalMaps.segment s))

  -- ∅ ⊂ ω^P properly, with ceiling the empty support ω^0: no support lies
  -- below it.
  positive : (P : 𝒫 ℓ) → Maps.Segment Operation.empty (exp P)
  positive P = record
    { bound = record
        { to = λ x → ⊥-elim (lower x)
        ; to-≈ = λ {x} → ⊥-elim (lower x)
        ; to-< = λ {x} → ⊥-elim (lower x)
        ; reflects-< = λ {x} → ⊥-elim (lower x)
        ; ceiling = lift ([] , tt)
        ; below = λ x → ⊥-elim (lower x)
        }
    ; covers = λ _ → λ { (lift ()) }
    }

  ----------------------------------------------------------------------
  -- Order embeddings and supports

  -- An order embedding f : P → Q gives ω^f : ω^P → ω^Q, exponent by
  -- exponent through the normalized points.
  embedding : Maps.Embedding P Q → Maps.Embedding (exp P) (exp Q)
  embedding f = Exact.embedding
    (ExponentialInitial.embedding (NormalMaps.embedding f))

  -- The exponents of a point of ω^P: its finite support in P.
  exponents : (P : 𝒫 ℓ) → 𝒫.X (exp P) → List (Normal.Point P)
  exponents P x = Support.Power.exponents (Normal.order P) (lower x)

  exponents-resp : (P : 𝒫 ℓ) {x y : 𝒫.X (exp P)}
    → 𝒫._≈_ (exp P) x y → exponents P x ≡ exponents P y
  exponents-resp P p =
    cong (Support.Power.exponents (Normal.order P)) (lower p)

  -- The exponents of ω^f(x) are the images of the exponents of x …
  exponents-natural : {P Q : 𝒫 ℓ} (f : Maps.Embedding P Q) (x : 𝒫.X (exp P))
    → exponents Q (Maps.Embedding.map (embedding f) x)
      ≡ List.map (Orders.Embedding.map (NormalMaps.embedding f))
          (exponents P x)
  exponents-natural f x =
    ExponentialInitial.exponents (NormalMaps.embedding f) (lower x)

  -- … and a point whose exponents all lie in the image comes from ω^P.
  restrict : (f : Maps.Embedding P Q) (y : 𝒫.X (exp Q))
    → All (λ b → Σ (Normal.Point P)
        (λ a → Orders.Embedding.map (NormalMaps.embedding f) a ≡ b))
        (exponents Q y)
    → Σ (𝒫.X (exp P))
        (λ x → 𝒫._≈_ (exp Q) (Maps.Embedding.map (embedding f) x) y)
  restrict f y ps with ExponentialInitial.restrict
    (NormalMaps.embedding f) (lower y) ps
  ... | x , p = lift x , lift p

  -- A triangle of embeddings, up to ≈, gives a triangle of exponentials.
  embedding-compose : {R : 𝒫 ℓ} (f : Maps.Embedding P Q)
    (g : Maps.Embedding Q R) (h : Maps.Embedding P R)
    → ((x : 𝒫.X P) → 𝒫._≈_ R (Maps.Embedding.map h x)
        (Maps.Embedding.map g (Maps.Embedding.map f x)))
    → (x : 𝒫.X (exp P))
    → 𝒫._≈_ (exp R) (Maps.Embedding.map (embedding h) x)
        (Maps.Embedding.map (embedding g) (Maps.Embedding.map (embedding f) x))
  embedding-compose {P = P} {Q} {R = R} f g h e x = lift
    (ExponentialInitial.compose (NormalMaps.embedding f)
      (NormalMaps.embedding g) (NormalMaps.embedding h) pointwise (lower x))
    where
    pointwise : (a : Normal.Point P)
      → Orders.Embedding.map (NormalMaps.embedding h) a
        ≡ Orders.Embedding.map (NormalMaps.embedding g)
            (Orders.Embedding.map (NormalMaps.embedding f) a)
    pointwise a = Normal.class-resp R (𝒫.≈-trans R
      (e (Normal.representative P a))
      (Maps.Embedding.resp g (𝒫.≈-sym Q (Normal.representative-class Q
        (Maps.Embedding.map f (Normal.representative P a))))))

  -- An embedding pointwise ≈ to the identity fixes ω^P.
  embedding-identity : (h : Maps.Embedding P P)
    → ((x : 𝒫.X P) → 𝒫._≈_ P (Maps.Embedding.map h x) x)
    → (x : 𝒫.X (exp P))
    → 𝒫._≈_ (exp P) (Maps.Embedding.map (embedding h) x) x
  embedding-identity {P = P} h e x = lift
    (ExponentialInitial.identity (NormalMaps.embedding h) pointwise (lower x))
    where
    pointwise : (a : Normal.Point P)
      → Orders.Embedding.map (NormalMaps.embedding h) a ≡ a
    pointwise a = trans (Normal.class-resp P (e (Normal.representative P a)))
      (Normal.class-representative P a)

  -- On an initial map the embedding action is the initial-map action.
  embedding-initial : (f : Maps.Initial P Q) (x : 𝒫.X (exp P))
    → 𝒫._≈_ (exp Q)
        (Maps.Embedding.map (embedding (Maps.Initial.embedding f)) x)
        (Maps.Initial.map (initial f) x)
  embedding-initial {Q = Q} f x = 𝒫.≈-refl (exp Q) _

  -- An embedding of successors that keeps the top on top carries the
  -- ceiling of ω^P ⊂ ω^(P+1), the support ω^top, to that of ω^Q ⊂ ω^(Q+1).
  ceiling : (P Q : 𝒫 ℓ)
    (g : Maps.Embedding (Maps.Successor.next P) (Maps.Successor.next Q))
    → 𝒫._≈_ (Maps.Successor.next Q)
        (Maps.Embedding.map g
          (Presented._≺𝒫_.ceiling (Maps.Segment.bound (Maps.successor P))))
        (Presented._≺𝒫_.ceiling (Maps.Segment.bound (Maps.successor Q)))
    → 𝒫._≈_ (exp (Maps.Successor.next Q))
        (Maps.Embedding.map (embedding g)
          (Presented._≺𝒫_.ceiling
            (Maps.Segment.bound (segment (Maps.successor P)))))
        (Presented._≺𝒫_.ceiling
          (Maps.Segment.bound (segment (Maps.successor Q))))
  ceiling P Q g top = lift (Support.Power.equal
    (Normal.order (Maps.Successor.next Q))
    (cong (λ b → (b , zero) ∷ []) (Normal.class-resp (Maps.Successor.next Q)
      (𝒫.≈-trans (Maps.Successor.next Q)
        (Maps.Embedding.resp g
          (Normal.representative-class (Maps.Successor.next P) topP))
        top))))
    where
    topP : 𝒫.X (Maps.Successor.next P)
    topP = Presented._≺𝒫_.ceiling (Maps.Segment.bound (Maps.successor P))

-- ω^ as an operation on initial maps, and its continuity in that form.
operation : Operation.Operation ℓ
operation = record { apply = exp ; act = initial }

operation-continuous : Operation.Continuous (operation {ℓ})
operation-continuous = continuous

normal : Normal.Normal ℓ
normal = record
  { operation = operation
  ; continuous = operation-continuous
  ; segment = segment
  }
