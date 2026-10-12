{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Arithmetic.Comparison.Representatives where

-- The strengths of Comparison.Strength and Characterization.Strength,
-- asked of a class of representatives instead of all presentations. A
-- class of representatives is a type with a presentation for each member
-- and, for every presentation, a member presenting it up to ≃𝒫
-- (Representatives). Every row moves across ≃𝒫 (initial-across,
-- segment-across, equivalence-across, supremum-across, zero-across), so
-- each row asked of the class is equivalent to the same principle as the
-- row asked of all presentations. The positive direction is the old one
-- at the presented members. The other direction carries a decision for
-- the class to all presentations along the chosen equivalences, and
-- applies the discriminator of the row.
--
-- Two classes: the Boolean orders, decidable sets of numbers with a
-- decidable order (boolean-orders), and the propositional presentations,
-- with at most one witness of ≈ and of < between two points
-- (propositional-presentations). So none of these strengths depends on
-- relations with several witnesses: the data the rows use are comparison,
-- enumeration and the maps.
--
-- Rows 9 (classification) and 14 (division) give LPO without their data,
-- with no converse (Classification.Discriminator, Division.Discriminator).
-- They give LPO asked of a class of representatives too (inhabited,
-- classified, shaped, division): classifications, local shapes and
-- divisions also move across ≃𝒫 (Classification.respect, Local.image and
-- moved, division-across, through Multiplication.Left).

open import Agda.Primitive using (Level; lzero; lsuc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁)
open import Data.Sum using (_⊎_) renaming (map to ⊎-map)
open import Function.Bundles using (_⇔_; mk⇔)
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (map′)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
import SPT.Cubical.OrdinalGeometry.Presentation.Map as Maps
open import SPT.Cubical.OrdinalGeometry.Presentation.Sum using (_+_)
import SPT.Cubical.OrdinalGeometry.Presentation.Limit.Discriminator as Stream
import SPT.Cubical.OrdinalGeometry.Presentation.Normalization.Boolean
  as Boolean
open import SPT.Cubical.OrdinalGeometry.Presentation.Propositional using
  (Propositional; boolean; boolean-propositional)
open import SPT.Cubical.OrdinalGeometry.ExactOrder.Boolean using
  (BooleanOrder)
open import SPT.Cubical.OrdinalGeometry.Operation.Normal using (precompose)
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Characterization using
  (Supremum; Zero)
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Ambient using (pair)
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Exponential using (omega)
import SPT.Cubical.OrdinalGeometry.Arithmetic.Successor as Successor
import SPT.Cubical.OrdinalGeometry.Arithmetic.Classification as Classification
open Classification using (Classified)
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Classification.Local using
  (Local; image; moved)
import SPT.Cubical.OrdinalGeometry.Arithmetic.Classification.Discriminator
  as ClassificationDiscriminator
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Division using (Division)
import SPT.Cubical.OrdinalGeometry.Arithmetic.Division.Discriminator
  as DivisionDiscriminator
import SPT.Cubical.OrdinalGeometry.Arithmetic.Multiplication.Left
  as LeftMultiplication
import SPT.Cubical.OrdinalGeometry.Arithmetic.Addition as Addition
import SPT.Cubical.OrdinalGeometry.Arithmetic.Comparison as Comparison
import SPT.Cubical.OrdinalGeometry.Arithmetic.Comparison.Discriminator
  as ComparisonDiscriminator
import SPT.Cubical.OrdinalGeometry.Arithmetic.Ambient.Discriminator
  as AmbientDiscriminator
import SPT.Cubical.OrdinalGeometry.Arithmetic.Successor.Discriminator
  as SuccessorDiscriminator
import SPT.Cubical.OrdinalGeometry.Arithmetic.Subtraction.Discriminator
  as SubtractionDiscriminator
open import
  SPT.Cubical.OrdinalGeometry.Arithmetic.Characterization.Discriminator
  using (WLPO)
import SPT.Cubical.OrdinalGeometry.Arithmetic.Characterization.Discriminator
  as CharacterizationDiscriminator
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Characterization.Strength
  using (decide-zero; omega-lpo)

private
  variable
    ℓ : Level
    P P′ Q Q′ S S′ D D′ : 𝒫 ℓ

------------------------------------------------------------------------
-- The rows move across equivalences

-- Mathematical shape: P ≃ P′ → Q ≃ Q′ → P ≤ Q → P′ ≤ Q′.
initial-across : P Presented.≃𝒫 P′ → Q Presented.≃𝒫 Q′
  → Maps.Initial P Q → Maps.Initial P′ Q′
initial-across e e′ f = Maps.compose (Maps.equivalence (Presented.≃𝒫-sym e))
  (Maps.compose f (Maps.equivalence e′))

-- Mathematical shape: P ≃ P′ → Q ≃ Q′ → P < Q → P′ < Q′.
segment-across : P Presented.≃𝒫 P′ → Q Presented.≃𝒫 Q′
  → Maps.Segment P Q → Maps.Segment P′ Q′
segment-across e e′ s =
  Maps.along (precompose (Presented.≃𝒫-sym e) s) (Maps.equivalence e′)

-- Mathematical shape: P ≃ P′ → Q ≃ Q′ → P ≃ Q → P′ ≃ Q′.
equivalence-across : P Presented.≃𝒫 P′ → Q Presented.≃𝒫 Q′
  → P Presented.≃𝒫 Q → P′ Presented.≃𝒫 Q′
equivalence-across e e′ d =
  Presented.≃𝒫-trans (Presented.≃𝒫-sym e) (Presented.≃𝒫-trans d e′)

-- Mathematical shape: (Π n. F n ≃ G n) → S ≃ S′ → S = sup F → S′ = sup G.
supremum-across : {F G : ℕ → 𝒫 ℓ} → ((n : ℕ) → F n Presented.≃𝒫 G n)
  → S Presented.≃𝒫 S′ → Supremum F S → Supremum G S′
supremum-across e e′ s = record
  { member = λ n → initial-across (e n) e′ (Supremum.member s n)
  ; least = λ Q h → Maps.compose (Maps.equivalence (Presented.≃𝒫-sym e′))
      (Supremum.least s Q λ n → Maps.compose (Maps.equivalence (e n)) (h n))
  }

-- Mathematical shape: P ≃ P′ → Zero P → Zero P′.
zero-across : P Presented.≃𝒫 P′ → Zero P → Zero P′
zero-across e z Q = Maps.compose (Maps.equivalence (Presented.≃𝒫-sym e)) (z Q)

-- Mathematical shape: P ≃ P′ → D ≃ D′ → Division P D → Division P′ D′,
-- with the same quotient and remainder.
division-across : P Presented.≃𝒫 P′ → D Presented.≃𝒫 D′
  → Division P D → Division P′ D′
division-across e e′ d = record
  { quotient = Division.quotient d
  ; remainder = Division.remainder d
  ; equation = Presented.≃𝒫-trans
      (Addition.equivalence
        (LeftMultiplication.equivalence (Presented.≃𝒫-sym e′)
          (Division.quotient d))
        (Presented.≃𝒫-refl (Division.remainder d)))
      (Presented.≃𝒫-trans (Division.equation d) e)
  ; below = segment-across (Presented.≃𝒫-refl (Division.remainder d)) e′
      (Division.below d)
  }

-- The family P, Q, Q, … moves across equivalences of P and of Q.
pair-across : P Presented.≃𝒫 P′ → Q Presented.≃𝒫 Q′
  → (n : ℕ) → pair P Q n Presented.≃𝒫 pair P′ Q′ n
pair-across e e′ zero = e
pair-across e e′ (suc n) = e′

------------------------------------------------------------------------
-- Classes of representatives

-- Mathematical shape: a type A with present : A → 𝒫 and, for every P, a
-- member choose P with present (choose P) ≃ P.
record Representatives (κ : Level) : Set (lsuc κ) where
  field
    Representative : Set κ
    present : Representative → 𝒫 lzero
    choose : 𝒫 lzero → Representative
    presents : (P : 𝒫 lzero) → present (choose P) Presented.≃𝒫 P

------------------------------------------------------------------------
-- The strengths, asked of a class of representatives

module _ {κ : Level} (R : Representatives κ) where

  open Representatives R

  private
    toward : (P : 𝒫 lzero) → P Presented.≃𝒫 present (choose P)
    toward P = Presented.≃𝒫-sym (presents P)

  -- Mathematical shape: LPO ⇔ Π P Q. P ≤ Q ⊎ Q < P.
  comparable : Stream.LPO
    ⇔ ((P Q : Representative)
        → Maps.Initial (present P) (present Q)
          ⊎ Maps.Segment (present Q) (present P))
  comparable = mk⇔
    (λ lpo P Q → Comparison.comparable lpo (present P) (present Q))
    (λ row → ComparisonDiscriminator.comparable λ P Q →
      ⊎-map (initial-across (presents P) (presents Q))
        (segment-across (presents Q) (presents P))
        (row (choose P) (choose Q)))

  -- Mathematical shape: LPO ⇔ Π P Q. Dec (P ≤ Q).
  initial : Stream.LPO
    ⇔ ((P Q : Representative) → Dec (Maps.Initial (present P) (present Q)))
  initial = mk⇔
    (λ lpo P Q → Comparison.initial lpo (present P) (present Q))
    (λ row → ComparisonDiscriminator.initial λ P Q →
      map′ (initial-across (presents P) (presents Q))
        (initial-across (toward P) (toward Q))
        (row (choose P) (choose Q)))

  -- Mathematical shape: LPO ⇔ Π P Q. Dec (P ≃ Q).
  equivalent : Stream.LPO
    ⇔ ((P Q : Representative)
        → Dec (present P Presented.≃𝒫 present Q))
  equivalent = mk⇔
    (λ lpo P Q → Comparison.equivalent lpo (present P) (present Q))
    (λ row → ComparisonDiscriminator.equivalent λ P Q →
      map′ (equivalence-across (presents P) (presents Q))
        (equivalence-across (toward P) (toward Q))
        (row (choose P) (choose Q)))

  -- Mathematical shape: LPO ⇔ Π F : ℕ → A. Σ S. Π n. F n < S.
  bound : Stream.LPO
    ⇔ ((F : ℕ → Representative)
        → Σ Representative λ S →
            (n : ℕ) → Maps.Segment (present (F n)) (present S))
  bound = mk⇔
    (λ lpo F →
      let S , s = Comparison.bound lpo (λ n → present (F n))
      in choose S , λ n →
        segment-across (Presented.≃𝒫-refl (present (F n))) (toward S) (s n))
    (λ row → ComparisonDiscriminator.bound λ F →
      let S , s = row (λ n → choose (F n))
      in present S , λ n →
        segment-across (presents (F n)) (Presented.≃𝒫-refl (present S))
          (s n))

  -- Row 2. Mathematical shape: LPO ⇔ Π P Q S. P ≤ Q → Q < S → P < S.
  along : Stream.LPO
    ⇔ ((P Q S : Representative)
        → Maps.Initial (present P) (present Q)
        → Maps.Segment (present Q) (present S)
        → Maps.Segment (present P) (present S))
  along = mk⇔
    (λ lpo P Q S → Comparison.along lpo)
    (λ row → AmbientDiscriminator.along λ P Q S f s →
      segment-across (presents P) (presents S)
        (row (choose P) (choose Q) (choose S)
          (initial-across (toward P) (toward Q) f)
          (segment-across (toward Q) (toward S) s)))

  -- Row 5. Mathematical shape: LPO ⇔ Π P Q. P ≤ Q → P + 1 ≤ Q + 1.
  successor-initial : Stream.LPO
    ⇔ ((P Q : Representative)
        → Maps.Initial (present P) (present Q)
        → Maps.Initial (Maps.Successor.next (present P))
            (Maps.Successor.next (present Q)))
  successor-initial = mk⇔
    (λ lpo P Q → Comparison.successor-initial lpo)
    (λ row → SuccessorDiscriminator.initial λ P Q f →
      initial-across (Successor.respect (presents P))
        (Successor.respect (presents Q))
        (row (choose P) (choose Q) (initial-across (toward P) (toward Q) f)))

  -- Row 5. Mathematical shape: LPO ⇔ Π P Q. P < Q → P + 1 < Q + 1.
  successor-segment : Stream.LPO
    ⇔ ((P Q : Representative)
        → Maps.Segment (present P) (present Q)
        → Maps.Segment (Maps.Successor.next (present P))
            (Maps.Successor.next (present Q)))
  successor-segment = mk⇔
    (λ lpo P Q → Comparison.successor-segment lpo)
    (λ row → SuccessorDiscriminator.segment λ P Q s →
      segment-across (Successor.respect (presents P))
        (Successor.respect (presents Q))
        (row (choose P) (choose Q) (segment-across (toward P) (toward Q) s)))

  -- Row 6. Mathematical shape: LPO ⇔ Π P Q. Σ S. S = sup (P, Q, Q, …).
  join : Stream.LPO
    ⇔ ((P Q : Representative)
        → Σ Representative λ S →
            Supremum (pair (present P) (present Q)) (present S))
  join = mk⇔
    (λ lpo P Q →
      let S , s = Comparison.join lpo (present P) (present Q)
      in choose S , supremum-across
        (λ n → Presented.≃𝒫-refl (pair (present P) (present Q) n))
        (toward S) s)
    (λ row → AmbientDiscriminator.join λ P Q →
      let S , s = row (choose P) (choose Q)
      in present S , supremum-across (pair-across (presents P) (presents Q))
        (Presented.≃𝒫-refl (present S)) s)

  -- Row 8. Mathematical shape: LPO ⇔ Π F : ℕ → A. Σ S. S = sup F.
  supremum : Stream.LPO
    ⇔ ((F : ℕ → Representative)
        → Σ Representative λ S →
            Supremum (λ n → present (F n)) (present S))
  supremum = mk⇔
    (λ lpo F →
      let S , s = Comparison.supremum lpo (λ n → present (F n))
      in choose S , supremum-across
        (λ n → Presented.≃𝒫-refl (present (F n))) (toward S) s)
    (λ row → AmbientDiscriminator.supremum λ F →
      let S , s = row (λ n → choose (F n))
      in present S , supremum-across (λ n → presents (F n))
        (Presented.≃𝒫-refl (present S)) s)

  -- Row 13. Mathematical shape: LPO ⇔ Π P Q. P ≤ Q → Σ S. P + S ≃ Q.
  remainder : Stream.LPO
    ⇔ ((P Q : Representative)
        → Maps.Initial (present P) (present Q)
        → Σ Representative λ S →
            (present P + present S) Presented.≃𝒫 present Q)
  remainder = mk⇔
    (λ lpo P Q f →
      let S , d = Comparison.subtract lpo f
      in choose S , Presented.≃𝒫-trans
        (Addition.equivalence (Presented.≃𝒫-refl (present P)) (presents S))
        d)
    (λ row → SubtractionDiscriminator.remainder λ P Q f →
      let S , d = row (choose P) (choose Q)
            (initial-across (toward P) (toward Q) f)
      in present S , Presented.≃𝒫-trans
        (Addition.equivalence (toward P) (Presented.≃𝒫-refl (present S)))
        (Presented.≃𝒫-trans d (presents Q)))

  -- Row 15. Mathematical shape: LPO ⇔ Π P. Dec (P < ω).
  finite : Stream.LPO
    ⇔ ((P : Representative) → Dec (Maps.Segment (present P) omega))
  finite = mk⇔
    (λ lpo P → Comparison.finite lpo (present P))
    (λ row → AmbientDiscriminator.finite λ P →
      map′ (segment-across (presents P) (Presented.≃𝒫-refl omega))
        (segment-across (toward P) (Presented.≃𝒫-refl omega))
        (row (choose P)))

  -- Row 16. Mathematical shape: LPO ⇔ Π P Q. Dec (P < Q).
  decidable : Stream.LPO
    ⇔ ((P Q : Representative) → Dec (Maps.Segment (present P) (present Q)))
  decidable = mk⇔
    (λ lpo P Q → Comparison.decidable lpo (present P) (present Q))
    (λ row → AmbientDiscriminator.decidable λ P Q →
      map′ (segment-across (presents P) (presents Q))
        (segment-across (toward P) (toward Q))
        (row (choose P) (choose Q)))

  -- Row 17. Mathematical shape: LPO ⇔ Π P Q. P ≤ Q → P < Q ⊎ P ≃ Q.
  split : Stream.LPO
    ⇔ ((P Q : Representative)
        → Maps.Initial (present P) (present Q)
        → Maps.Segment (present P) (present Q)
          ⊎ present P Presented.≃𝒫 present Q)
  split = mk⇔
    (λ lpo P Q → Comparison.split lpo)
    (λ row → AmbientDiscriminator.split λ P Q f →
      ⊎-map (segment-across (presents P) (presents Q))
        (equivalence-across (presents P) (presents Q))
        (row (choose P) (choose Q) (initial-across (toward P) (toward Q) f)))

  -- Row 18. Mathematical shape: LPO ⇔ Π P Q. P < Q ⊎ P ≃ Q ⊎ Q < P.
  trichotomy : Stream.LPO
    ⇔ ((P Q : Representative)
        → Maps.Segment (present P) (present Q)
          ⊎ (present P Presented.≃𝒫 present Q
            ⊎ Maps.Segment (present Q) (present P)))
  trichotomy = mk⇔
    (λ lpo P Q → Comparison.trichotomy lpo (present P) (present Q))
    (λ row → AmbientDiscriminator.trichotomy λ P Q →
      ⊎-map (segment-across (presents P) (presents Q))
        (⊎-map (equivalence-across (presents P) (presents Q))
          (segment-across (presents Q) (presents P)))
        (row (choose P) (choose Q)))

  -- Mathematical shape: WLPO ⇔ Π P. Dec (Zero P).
  zero-strength : WLPO
    ⇔ ((P : Representative) → Dec (Zero (present P)))
  zero-strength = mk⇔
    (λ wlpo P → decide-zero wlpo (present P))
    (λ row → CharacterizationDiscriminator.zero λ P →
      map′ (zero-across (presents P)) (zero-across (toward P))
        (row (choose P)))

  -- Mathematical shape: LPO ⇔ Π P. Dec (P ≃ ω).
  omega-strength : Stream.LPO
    ⇔ ((P : Representative) → Dec (present P Presented.≃𝒫 omega))
  omega-strength = mk⇔
    (λ lpo P → Comparison.equivalent lpo (present P) omega)
    (λ row → omega-lpo λ P →
      map′ (equivalence-across (presents P) (Presented.≃𝒫-refl omega))
        (equivalence-across (toward P) (Presented.≃𝒫-refl omega))
        (row (choose P)))

  -- Row 9. Mathematical shape: (Π P. X P → Classified P) → LPO.
  inhabited : ((P : Representative) → 𝒫.X (present P)
      → Classified (present P))
    → Stream.LPO
  inhabited row = ClassificationDiscriminator.inhabited λ P x →
    Classification.respect (presents P)
      (row (choose P) (Presented._≃𝒫_.to (toward P) x))

  -- Row 9. Mathematical shape: (Π P. Classified P) → LPO.
  classified : ((P : Representative) → Classified (present P)) → Stream.LPO
  classified row = ClassificationDiscriminator.classified λ P →
    Classification.respect (presents P) (row (choose P))

  -- Row 9, locally. Mathematical shape: (Π W x. Local W x) → LPO.
  shaped : ((W : Representative) (x : 𝒫.X (present W))
      → Local (present W) x)
    → Stream.LPO
  shaped row = ClassificationDiscriminator.shaped λ W x →
    moved W (Presented._≃𝒫_.to-from-≈ (presents W) x)
      (image (Maps.equivalence (presents W))
        (Presented._≃𝒫_.to (toward W) x)
        (row (choose W) (Presented._≃𝒫_.to (toward W) x)))

  -- Row 14. Mathematical shape: (Π P D. X D → Division P D) → LPO.
  division : ((P D : Representative) → 𝒫.X (present D)
      → Division (present P) (present D))
    → Stream.LPO
  division row = DivisionDiscriminator.division λ P D x →
    division-across (presents P) (presents D)
      (row (choose P) (choose D) (Presented._≃𝒫_.to (toward D) x))

------------------------------------------------------------------------
-- Two classes of representatives

-- The Boolean orders: every presentation is equivalent to the
-- presentation of its Boolean order (Normalization.Boolean).
boolean-orders : Representatives lzero
boolean-orders = record
  { Representative = BooleanOrder
  ; present = boolean
  ; choose = Boolean.normal
  ; presents = λ P → Presented.≃𝒫-sym (Boolean.equivalence P)
  }

-- The propositional presentations: the presentation of a Boolean order is
-- one (Propositional.boolean-propositional).
propositional-presentations : Representatives (lsuc lzero)
propositional-presentations = record
  { Representative = Σ (𝒫 lzero) Propositional
  ; present = proj₁
  ; choose = λ P →
      boolean (Boolean.normal P) , boolean-propositional (Boolean.normal P)
  ; presents = λ P → Presented.≃𝒫-sym (Boolean.equivalence P)
  }
