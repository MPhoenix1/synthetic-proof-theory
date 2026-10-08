{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Arithmetic.Classification.Induction where

-- Classifiability induction (Kraus, Nordvall Forsberg and Xu, Definition
-- 9 and Theorem 11) for presentations classified hereditarily.
--
-- Classified P classifies P alone. Hereditary P classifies P, the
-- predecessor of its successor case and every stage of its limit case,
-- and so on below; its eliminator is classifiability induction, for any
-- family of types. Theorem 11: a class of presentations whose members are
-- classified, with the predecessors named by each classification again in
-- the class, is hereditary, by well-founded recursion on ≺𝒫.
-- Hereditary are: ∅, P + 1 and limits of hereditary presentations, P + Q
-- for hereditary P and Q, the finite ordinals and ω.

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Data.Nat using (ℕ; zero; suc)
import Data.Nat.Properties as NatProperties
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤)
open import Level using (lift)

open import SPT.Cubical.Core.WellFounded using (Acc; acc)
import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
import SPT.Cubical.OrdinalGeometry.Presentation.Map as Maps
import SPT.Cubical.OrdinalGeometry.Presentation.Successor as Adjoin
open import SPT.Cubical.OrdinalGeometry.Presentation.Sum using (_+_; ∂)
import SPT.Cubical.OrdinalGeometry.Operation.Base as Operation
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Characterization using
  ( bijection; Zero; pointless; Successor; Strong; module Successors
  ; Supremum; Increasing
  ) renaming (nothing to vacant)
import SPT.Cubical.OrdinalGeometry.Arithmetic.Addition as Addition
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Exponential using (omega)
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Classification using
  (Classified; naturals; zero-respect; strong-respect; supremum-respect)

private
  variable
    ℓ κ : Level
    P P′ Q : 𝒫 ℓ

------------------------------------------------------------------------
-- Hereditary classification

-- Mathematical shape: the least family closed under
--   Zero P → H P,
--   Strong Q P → H Q → H P,
--   Supremum (stage s) P → (Π n. H (stage s n)) → H P.
data Hereditary {ℓ : Level} : 𝒫 ℓ → Set (lsuc ℓ) where
  zero : Zero P → Hereditary P
  successor : (Q : 𝒫 ℓ) → Strong Q P → Hereditary Q → Hereditary P
  limit : (s : Increasing ℓ) → Supremum (Increasing.stage s) P
    → ((n : ℕ) → Hereditary (Increasing.stage s n)) → Hereditary P

-- A hereditary classification classifies.
classified : Hereditary P → Classified P
classified (zero z) = Classified.zero z
classified (successor Q st _) = Classified.successor Q st
classified (limit s sup _) = Classified.limit s sup

------------------------------------------------------------------------
-- Classifiability induction

-- The clauses of Definition 9, for a family Φ of types.
record Clauses {ℓ κ : Level} (Φ : 𝒫 ℓ → Set κ) : Set (lsuc ℓ ⊔ κ) where
  field
    zero-case : {P : 𝒫 ℓ} → Zero P → Φ P
    successor-case : {P Q : 𝒫 ℓ} → Strong Q P → Φ Q → Φ P
    limit-case : {P : 𝒫 ℓ} (s : Increasing ℓ)
      → Supremum (Increasing.stage s) P
      → ((n : ℕ) → Φ (Increasing.stage s n)) → Φ P

induction : (Φ : 𝒫 ℓ → Set κ) → Clauses Φ → {P : 𝒫 ℓ} → Hereditary P
  → Φ P
induction Φ c (zero z) = Clauses.zero-case c z
induction Φ c (successor Q st h) =
  Clauses.successor-case c st (induction Φ c h)
induction Φ c (limit s sup h) =
  Clauses.limit-case c s sup λ n → induction Φ c (h n)

------------------------------------------------------------------------
-- Invariance under equivalence

respect : P Presented.≃𝒫 P′ → Hereditary P → Hereditary P′
respect e (zero z) = zero (zero-respect e z)
respect e (successor Q st h) = successor Q (strong-respect e st) h
respect e (limit s sup h) = limit s (supremum-respect e sup) h

------------------------------------------------------------------------
-- Theorem 11: classified classes closed under predecessors

-- The predecessors named by a classification lie in C.
Within : (C : 𝒫 ℓ → Set κ) {P : 𝒫 ℓ} → Classified P → Set κ
Within C (Classified.zero _) = ⊤
Within C (Classified.successor Q _) = C Q
Within C (Classified.limit s _) = (n : ℕ) → C (Increasing.stage s n)

-- Mathematical shape: (Π P. C P → Σ c : Classified P. Within C c)
--   → Π P. C P → Hereditary P.
-- The recursion is on ≺𝒫: the predecessor of a strong successor and the
-- stages of a limit lie strictly below it.
hereditary : (C : 𝒫 ℓ → Set κ)
  → ((P : 𝒫 ℓ) → C P → Σ (Classified P) (Within C))
  → (P : 𝒫 ℓ) → C P → Hereditary P
hereditary {ℓ = ℓ} C closed P = go P (Presented.Embedding.wf P)
  where
  go : (P : 𝒫 ℓ) → Acc Presented._≺𝒫_ P → C P → Hereditary P
  go P (acc smaller) c with closed P c
  ... | Classified.zero z , _ = zero z
  ... | Classified.successor Q st , cQ =
    successor Q st
      (go Q (smaller Q (Maps.Segment.bound
        (Successor.above (Strong.successor st)))) cQ)
  ... | Classified.limit s sup , cs =
    limit s sup λ n →
      go (Increasing.stage s n)
        (smaller (Increasing.stage s n)
          (Maps.bounded (Maps.Segment.bound (Increasing.step s n))
            (Supremum.member sup (suc n))))
        (cs n)

------------------------------------------------------------------------
-- Hereditary presentations

vacant-hereditary : Hereditary (Operation.empty {ℓ})
vacant-hereditary = zero vacant

next : Hereditary P → Hereditary (Maps.Successor.next P)
next {P = P} h = successor P (Successors.next P) h

completed : (s : Increasing ℓ)
  → ((n : ℕ) → Hereditary (Increasing.stage s n))
  → Hereditary (Increasing.limit s)
completed s h = limit s (Increasing.supremum s) h

-- Mathematical shape: H P → H Q → H (P + Q), by induction on Q.
sum : Hereditary P → Hereditary Q → Hereditary (P + Q)
sum {P = P} hP = induction (λ Q → Hereditary (P + Q)) record
  { zero-case = λ {Q} z →
      respect (Presented.≃𝒫-sym (Addition.zero-law {P = P} Q z)) hP
  ; successor-case = λ {Q} {R} st hR →
      respect
        (Presented.≃𝒫-sym (Addition.successor-law {P = P}
          (Strong.successor st) (Strong.successor (Successors.next (P + R)))))
        (next hR)
  ; limit-case = λ s sup hs →
      respect
        (Presented.≃𝒫-sym
          (Addition.limit-law {P = P} s sup (Increasing.supremum (shift s))))
        (completed (shift s) hs)
  }
  where
  shift : Increasing _ → Increasing _
  shift s = record
    { stage = λ n → P + Increasing.stage s n
    ; step = λ n → Addition.segment P (Increasing.step s n)
    }

------------------------------------------------------------------------
-- Finite ordinals and ω

-- In an ambient W, if x < y and nothing lies strictly between, the cone
-- at y is the strong successor of the cone at x.
immediate : (W : 𝒫 ℓ) {x y : 𝒫.X W} → 𝒫._<_ W x y
  → ((z : 𝒫.X W) → 𝒫._<_ W z y → 𝒫._<_ W z x ⊎ 𝒫._≈_ W z x)
  → Strong (∂ W x) (∂ W y)
immediate {ℓ} W {x} {y} x<y between =
  strong-respect equivalent (Successors.next (∂ W x))
  where
  module W = 𝒫 W
  module E = Presented.Diagonal.Successor
    (Adjoin.constant (∂ W x)) zero

  map : E.Entry → 𝒫.X (∂ W y)
  map (E.point u) = proj₁ u , W.<-trans (proj₂ u) x<y
  map E.top = x , x<y

  embedding : Maps.Embedding (Maps.Successor.next (∂ W x)) (∂ W y)
  embedding = record
    { map = map
    ; resp = λ { (E.point≈ p) → p ; E.top≈ → W.≈-refl x }
    ; strict = λ { (E.point< p) → p ; (E.point<top {u}) → proj₂ u }
    }

  equivalent : Maps.Successor.next (∂ W x) Presented.≃𝒫 ∂ W y
  equivalent =
    bijection embedding λ v → covered v (between (proj₁ v) (proj₂ v))
    where
    covered : (v : 𝒫.X (∂ W y))
      → 𝒫._<_ W (proj₁ v) x ⊎ 𝒫._≈_ W (proj₁ v) x
      → Σ E.Entry (λ u → 𝒫._≈_ (∂ W y) (map u) v)
    covered v (inj₁ v<x) = E.point (proj₁ v , v<x) , W.≈-refl (proj₁ v)
    covered v (inj₂ v≈x) = E.top , W.≈-sym v≈x

-- The cones of ω at its points are the finite ordinals.
finite : (n : ℕ) → Hereditary (∂ (omega {ℓ}) (lift n))
finite zero = zero (pointless λ { (_ , lift ()) })
finite {ℓ} (suc n) =
  successor (∂ omega (lift n))
    (immediate omega {lift n} {lift (suc n)}
      (lift (NatProperties.n<1+n n)) between)
    (finite n)
  where
  between : (z : 𝒫.X (omega {ℓ})) → 𝒫._<_ omega z (lift (suc n))
    → 𝒫._<_ omega z (lift n) ⊎ 𝒫._≈_ omega z (lift n)
  between z (lift p) with NatProperties.m<1+n⇒m<n∨m≡n p
  ... | inj₁ q = inj₁ (lift q)
  ... | inj₂ q = inj₂ (lift q)

-- ω is the limit of its finite cones.
omega-hereditary : Hereditary (omega {ℓ})
omega-hereditary =
  limit (proj₁ naturals) (proj₂ naturals) λ n → finite n
