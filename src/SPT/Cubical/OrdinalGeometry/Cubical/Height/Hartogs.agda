{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.Height.Hartogs where

-- The rank λ_R = reflection-rank R of a reflection R, compared with the
-- Hartogs well-order of its child types, as ω₁ is compared with H_ℕ.
-- Under excluded middle λ_R is that Hartogs well-order (cut,
-- equivalence); with choice it is regular, hence inaccessible
-- (inaccessible).

open import Agda.Primitive using (Level)
open import Data.Empty using (⊥-elim)

import Cubical.Data.Bool as Bool
open Bool using (Bool; true; false)
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality.Conversion as EqualityConversion
import Cubical.Data.Sigma.Base as Sigma
import Cubical.Data.Sigma.Properties as SigmaProperties
import Cubical.Data.Sum as Sum
open Sum using (inl; inr)
import Cubical.Data.Unit as Unit
import Cubical.Foundations.Equiv as Equiv
import Cubical.Foundations.HLevels as HLevels
import Cubical.Foundations.Isomorphism as Isomorphism
import Cubical.Foundations.Prelude as Cubical
import Cubical.Functions.Embedding as Embedding
import Cubical.HITs.PropositionalTruncation as Truncation
open Truncation using (∥_∥₁; ∣_∣₁)
import Cubical.Relation.Binary.Order.Woset.Base as Woset
import Cubical.Relation.Binary.Order.Woset.Simulation as Simulation
import Cubical.Relation.Nullary as Nullary
open Nullary using (Dec; yes; no)

open import SPT.Cubical.Core.WellFounded using (Acc; acc)
open import SPT.Cubical.Core.Equality.Isomorphism using () renaming
  (_≅_ to Isomorphic)
import SPT.Cubical.Core.Mahlo.Specification as Mahlo
open import SPT.Cubical.Core.Mahlo.Decoding using
  (W; sup; child-formers; child-decoding)
import SPT.Cubical.Core.Mahlo.Ambient as Ambient
import SPT.Cubical.OrdinalGeometry.Height.Reflection as Reflection
open import SPT.Cubical.OrdinalGeometry.Height.Simulation using
  (_≅_; branching; ≅-refl; ≅-trans)
import SPT.Cubical.OrdinalGeometry.Height.Ordinals as Heights
open import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Ordinals using
  (successor)
import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Supremum.Family
  as Family
open import SPT.Cubical.OrdinalGeometry.Cubical.Height.Rank using
  (rank; child; canonical-height; canonical; well-founded; rank-≅)
open import SPT.Cubical.OrdinalGeometry.Cubical.Height.Reflection using
  (Trees; tree-rank; tree-below; segment; reflection-rank)
open import SPT.Cubical.OrdinalGeometry.Cubical.Hartogs.Countability using
  (ExcludedMiddle)
open import SPT.Cubical.OrdinalGeometry.Cubical.Hartogs.PowerSet using
  (classes)
open import SPT.Cubical.OrdinalGeometry.Cubical.Hartogs.Formers using
  (empty-absurd; two-≃; sum-≃; power; power-≃; subset; subset-≃)
open import SPT.Cubical.OrdinalGeometry.Cubical.Hartogs.Universe using
  (Embeds; Hartogs; Cut; unique)
open import SPT.Cubical.OrdinalGeometry.Cubical.Hartogs.Cardinal using
  (Regular; Inaccessible; Choice)
import SPT.Cubical.OrdinalGeometry.Cubical.Hartogs.Cardinal as Cardinal

private
  variable
    ℓ : Level

  -- An equivalence as an isomorphism with inverse laws in ≡.
  isomorphic : {A B : Set ℓ} → A Equiv.≃ B → Isomorphic A B
  isomorphic e = record
    { forward = Equiv.equivFun e
    ; backward = Equiv.invEq e
    ; backward-forward = λ a → EqualityConversion.pathToEq (Equiv.retEq e a)
    ; forward-backward = λ b → EqualityConversion.pathToEq (Equiv.secEq e b)
    }

  -- Σ (t : B). fiber f t ≃ A, and the same with a predicate on A.
  fibers : {A B : Set ℓ} (f : A → B) → Cubical.Σ B (Equiv.fiber f) Equiv.≃ A
  fibers f =
    Isomorphism.isoToEquiv
      (Isomorphism.iso (λ found → Cubical.fst (Cubical.snd found))
        (λ a → f a Cubical., (a Cubical., Cubical.refl))
        (λ _ → Cubical.refl)
        (λ found i →
          Cubical.snd (Cubical.snd found) i Cubical.,
          (Cubical.fst (Cubical.snd found) Cubical.,
            λ j → Cubical.snd (Cubical.snd found) (i Cubical.∧ j))))

  fibers-below : {A B : Set ℓ} (f : A → B) (S : A → Set ℓ)
    → Cubical.Σ B (λ t →
        Cubical.Σ (Equiv.fiber f t) (λ u → S (Cubical.fst u)))
      Equiv.≃ Cubical.Σ A S
  fibers-below f S =
    Isomorphism.isoToEquiv
      (Isomorphism.iso
        (λ found →
          Cubical.fst (Cubical.fst (Cubical.snd found)) Cubical.,
          Cubical.snd (Cubical.snd found))
        (λ found →
          f (Cubical.fst found) Cubical.,
          ((Cubical.fst found Cubical., Cubical.refl) Cubical.,
            Cubical.snd found))
        (λ _ → Cubical.refl)
        (λ found i →
          Cubical.snd (Cubical.fst (Cubical.snd found)) i Cubical.,
          ((Cubical.fst (Cubical.fst (Cubical.snd found)) Cubical.,
            λ j → Cubical.snd (Cubical.fst (Cubical.snd found)) (i Cubical.∧ j))
            Cubical., Cubical.snd (Cubical.snd found))))

module _ {Ψ : Ambient.Operator ℓ}
  (R : Mahlo.Reflection (Ambient.formers ℓ) Ψ) where

  private
    closure = Mahlo.Reflection.closure R
    Code = Mahlo.Reflection.carrier R
    Decode = Mahlo.Closure.Decode closure
    formers = child-formers closure
    laws = child-decoding (Ambient.laws ℓ) closure
    codes = Reflection.codes (Ambient.laws ℓ) R

  ----------------------------------------------------------------------
  -- Ranks of child trees embed into child types

  -- The code covering the successor of the rank of a child tree:
  --
  --   cover (sup c k) = Σ (y : c). power (cover (k y)) × two.
  cover : Trees codes → Code
  cover (sup c k) =
    Mahlo.Formers.sum formers
      (c Cubical., λ y →
        Mahlo.Formers.sum formers
          (power formers laws (cover (k y)) Cubical.,
            λ _ → Mahlo.Formers.two formers))

  module _ (lem : ExcludedMiddle ℓ) where

    -- Mathematical shape: |rank w| ↪ (Decode (cover w) → 𝟐).  A point of
    -- rank (sup c k) is the image of a point of the successor of the rank
    -- of some k y: its top, or a point embedded at the previous stage.
    embedding : (w : Trees codes)
      → Cubical.fst (tree-rank codes w)
        Embedding.↪ (Decode (cover w) → Bool)
    embedding (sup c k) =
      classes lem
        (Woset.IsWoset.is-set
          (Woset.WosetStr.isWoset (Cubical.snd (tree-rank codes (sup c k)))))
        cover-map onto
      where
        Parts : Set _
        Parts = Cubical.Σ (Decode c) λ y →
          Cubical.Σ (Decode (cover (k y)) → Bool) λ _ → Bool

        parts : Decode (cover (sup c k)) Equiv.≃ Parts
        parts =
          Equiv.compEquiv (sum-≃ formers laws c _)
            (SigmaProperties.Σ-cong-equiv-snd λ y →
              Equiv.compEquiv (sum-≃ formers laws _ _)
                (SigmaProperties.Σ-cong-equiv
                  (power-≃ formers laws (cover (k y)))
                  (λ _ → two-≃ formers laws)))

        Successor : Decode c → Woset.Woset ℓ ℓ
        Successor y = successor (tree-rank codes (k y))

        upper : (y : Decode c)
          → Cubical.fst (Successor y) → Cubical.fst (tree-rank codes (sup c k))
        upper y = Cubical.fst (Family.upper Successor y)

        inner : (y : Decode c) (p : Decode (cover (k y)) → Bool)
          → Dec (Equiv.fiber (Cubical.fst (embedding (k y))) p)
          → Cubical.fst (Successor y)
        inner y p (yes found) = inl (Cubical.fst found)
        inner y p (no _) = inr Unit.tt*

        inner-at : (y : Decode c) (r : Cubical.fst (tree-rank codes (k y)))
          (d : Dec (Equiv.fiber (Cubical.fst (embedding (k y)))
            (Cubical.fst (embedding (k y)) r)))
          → inner y (Cubical.fst (embedding (k y)) r) d Cubical.≡ inl r
        inner-at y r (yes found) =
          Cubical.cong inl
            (Embedding.isEmbedding→Inj (Cubical.snd (embedding (k y)))
              (Cubical.fst found) r (Cubical.snd found))
        inner-at y r (no outside) =
          Empty.rec (outside (r Cubical., Cubical.refl))

        point : (y : Decode c) → (Decode (cover (k y)) → Bool) → Bool
          → Cubical.fst (Successor y)
        point y p false = inr Unit.tt*
        point y p true =
          inner y p
            (lem (Equiv.fiber (Cubical.fst (embedding (k y))) p)
              (Embedding.isEmbedding→hasPropFibers
                (Cubical.snd (embedding (k y))) p))

        cover-map : Decode (cover (sup c k))
          → Cubical.fst (tree-rank codes (sup c k))
        cover-map x =
          upper (Cubical.fst (Equiv.equivFun parts x))
            (point (Cubical.fst (Equiv.equivFun parts x))
              (Cubical.fst (Cubical.snd (Equiv.equivFun parts x)))
              (Cubical.snd (Cubical.snd (Equiv.equivFun parts x))))

        hit : (y : Decode c) (p : Decode (cover (k y)) → Bool) (b : Bool)
          → cover-map (Equiv.invEq parts (y Cubical., (p Cubical., b)))
            Cubical.≡ upper y (point y p b)
        hit y p b =
          Cubical.cong
            (λ part →
              upper (Cubical.fst part)
                (point (Cubical.fst part) (Cubical.fst (Cubical.snd part))
                  (Cubical.snd (Cubical.snd part))))
            (Equiv.secEq parts (y Cubical., (p Cubical., b)))

        onto : (z : Cubical.fst (tree-rank codes (sup c k)))
          → ∥ Equiv.fiber cover-map z ∥₁
        onto z =
          Truncation.map
            (λ found →
              let y = Cubical.fst found
                  s = Cubical.fst (Cubical.snd found)
                  at = Cubical.snd (Cubical.snd found)
              in from-successor y s at)
            (Family.upper-surjective Successor z)
          where
            from-successor : (y : Decode c) (s : Cubical.fst (Successor y))
              → upper y s Cubical.≡ z → Equiv.fiber cover-map z
            from-successor y (inl r) at =
              Equiv.invEq parts
                (y Cubical., (Cubical.fst (embedding (k y)) r Cubical., true))
              Cubical.,
              (hit y (Cubical.fst (embedding (k y)) r) true
              Cubical.∙ Cubical.cong (upper y)
                (inner-at y r
                  (lem (Equiv.fiber (Cubical.fst (embedding (k y)))
                      (Cubical.fst (embedding (k y)) r))
                    (Embedding.isEmbedding→hasPropFibers
                      (Cubical.snd (embedding (k y)))
                      (Cubical.fst (embedding (k y)) r))))
              Cubical.∙ at)
            from-successor y (inr _) at =
              Equiv.invEq parts
                (y Cubical., ((λ _ → false) Cubical., false))
              Cubical., (hit y (λ _ → false) false Cubical.∙ at)

    -- α ≺ λ_R → ‖Σ c. |α| ↪ Decode c‖: α is the rank of a child tree w
    -- (Height.Reflection.segment), which embeds into the power code of
    -- cover w.
    embeds : (α : Woset.Woset ℓ ℓ)
      → Simulation._≺_ α (reflection-rank R) → Embeds Decode (Cubical.fst α)
    embeds α α<λ =
      Truncation.map
        (λ found →
          power formers laws (cover (Cubical.fst found)) Cubical.,
          Embedding.compEmbedding
            (Embedding.Equiv→Embedding
              (Equiv.invEquiv
                (power-≃ formers laws (cover (Cubical.fst found)))))
            (Embedding.compEmbedding (embedding (Cubical.fst found))
              (Embedding.Equiv→Embedding
                (Cubical.fst (Cubical.snd found)))))
        (segment codes α α<λ)

    --------------------------------------------------------------------
    -- Well-orders embedding into child types are ranks of child trees

    module _ (α : Woset.Woset ℓ ℓ) (i : Code)
      (e : Cubical.fst α Embedding.↪ Decode i) where

      private
        _<_ = Woset.WosetStr._≺_ (Cubical.snd α)

        below-prop : (x : Cubical.fst α) (t : Decode i)
          → Cubical.isProp
              (Cubical.Σ (Equiv.fiber (Cubical.fst e) t) λ u →
                Cubical.fst u < x)
        below-prop x t =
          HLevels.isPropΣ
            (Embedding.isEmbedding→hasPropFibers (Cubical.snd e) t)
            λ u →
              Woset.IsWoset.is-prop-valued
                (Woset.WosetStr.isWoset (Cubical.snd α)) (Cubical.fst u) x

        -- The image of e, and the lower set of each point, as subset codes.
        image : Code
        image =
          subset formers laws lem i (Equiv.fiber (Cubical.fst e))
            (Embedding.isEmbedding→hasPropFibers (Cubical.snd e))

        -- Sealed, so that conversion never unfolds the composite.
        abstract
          image-≃ : Decode image Equiv.≃ Cubical.fst α
          image-≃ =
            Equiv.compEquiv
              (subset-≃ formers laws lem i (Equiv.fiber (Cubical.fst e))
                (Embedding.isEmbedding→hasPropFibers (Cubical.snd e)))
              (fibers (Cubical.fst e))

        lower : Cubical.fst α → Code
        lower x =
          subset formers laws lem i
            (λ t → Cubical.Σ (Equiv.fiber (Cubical.fst e) t) λ u →
              Cubical.fst u < x)
            (below-prop x)

        abstract
          lower-≃ : (x : Cubical.fst α)
            → Decode (lower x) Equiv.≃ Cubical.Σ (Cubical.fst α) (λ y → y < x)
          lower-≃ x =
            Equiv.compEquiv
              (subset-≃ formers laws lem i
                (λ t → Cubical.Σ (Equiv.fiber (Cubical.fst e) t) λ u →
                  Cubical.fst u < x)
                (below-prop x))
              (fibers-below (Cubical.fst e) (λ y → y < x))

      -- The canonical tree of α, with labels the lower-set codes.
      tree : (x : Cubical.fst α) → Acc _<_ x → Trees codes
      tree x (acc smaller) =
        sup (lower x) λ q →
          tree (Cubical.fst (Equiv.equivFun (lower-≃ x) q))
            (smaller (Cubical.fst (Equiv.equivFun (lower-≃ x) q))
              (Cubical.snd (Equiv.equivFun (lower-≃ x) q)))

      whole-tree : Trees codes
      whole-tree =
        sup image λ q →
          tree (Equiv.equivFun image-≃ q)
            (well-founded α (Equiv.equivFun image-≃ q))

      private
        embed = Reflection.embed (Ambient.laws ℓ) codes

        tree-≅ : (x : Cubical.fst α) (a : Acc _<_ x)
          → embed (tree x a) ≅ Heights.rankAt _<_ x a
        tree-≅ x (acc smaller) =
          branching (isomorphic (lower-≃ x))
            (λ q →
              tree-≅ (Cubical.fst (Equiv.equivFun (lower-≃ x) q))
                (smaller (Cubical.fst (Equiv.equivFun (lower-≃ x) q))
                  (Cubical.snd (Equiv.equivFun (lower-≃ x) q))))
            (λ b →
              let b′ = Equiv.equivFun (lower-≃ x) (Equiv.invEq (lower-≃ x) b)
                  at : (c : Cubical.Σ (Cubical.fst α) (λ y → y < x))
                    → Heights.Height ℓ
                  at c = Heights.rankAt _<_ (Cubical.fst c)
                    (smaller (Cubical.fst c) (Cubical.snd c))
              in
              ≅-trans
                (tree-≅ (Cubical.fst b′)
                  (smaller (Cubical.fst b′) (Cubical.snd b′)))
                (Cubical.subst (λ c → at b′ ≅ at c)
                  (Equiv.secEq (lower-≃ x) b) (≅-refl (at b′))))

        whole-≅ : embed whole-tree ≅ canonical-height α
        whole-≅ =
          branching (isomorphic image-≃)
            (λ q →
              tree-≅ (Equiv.equivFun image-≃ q)
                (well-founded α (Equiv.equivFun image-≃ q)))
            (λ a →
              let a′ = Equiv.equivFun image-≃ (Equiv.invEq image-≃ a)
                  at : Cubical.fst α → Heights.Height ℓ
                  at c = Heights.rankAt _<_ c (well-founded α c)
              in
              ≅-trans (tree-≅ a′ (well-founded α a′))
                (Cubical.subst (λ c → at a′ ≅ at c)
                  (Equiv.secEq image-≃ a) (≅-refl (at a′))))

      -- Mathematical shape: α ≃ rank whole-tree.
      whole-rank : Woset.WosetEquiv α (tree-rank codes whole-tree)
      whole-rank =
        Woset.invWosetEquiv
          (Woset.compWosetEquiv (rank-≅ whole-≅) (canonical α))

    -- ‖Σ c. |α| ↪ Decode c‖ → α ≺ λ_R.
    strict : (α : Woset.Woset ℓ ℓ)
      → Embeds Decode (Cubical.fst α) → Simulation._≺_ α (reflection-rank R)
    strict α =
      Truncation.rec (Simulation.isPropValued≺ α (reflection-rank R))
        λ found →
          Simulation.≺RespectsEquivL (reflection-rank R)
            (Woset.invWosetEquiv
              (whole-rank α (Cubical.fst found) (Cubical.snd found)))
            (tree-below codes
              (whole-tree α (Cubical.fst found) (Cubical.snd found)))

    ----------------------------------------------------------------------
    -- The cut, and the Hartogs well-order

    -- Mathematical shape: α ≺ λ_R ⇔ ‖Σ c. |α| ↪ Decode c‖.
    cut : Cut Decode (reflection-rank R)
    cut α = embeds α Cubical., strict α

    -- Mathematical shape: λ_R ≃ H(Decode).
    equivalence : Woset.WosetEquiv (reflection-rank R) (Hartogs Decode)
    equivalence = unique Decode (reflection-rank R) cut

    ----------------------------------------------------------------------
    -- Regularity

    -- A family of members of λ_R indexed by a member α: choose child trees
    -- for the members, index them by the child type that |α| embeds into,
    -- and put them under one child tree.
    regular : Choice ℓ → Regular (reflection-rank R)
    regular choice α α<λ F below =
      Truncation.rec2 Truncation.squash₁ bound
        (embeds α α<λ)
        (choice (Cubical.fst α)
          (λ a → Cubical.Σ (Trees codes) λ w →
            Woset.WosetEquiv (F a) (tree-rank codes w))
          (Woset.IsWoset.is-set (Woset.WosetStr.isWoset (Cubical.snd α)))
          (λ a → segment codes (F a) (below a)))
      where
        bound : Cubical.Σ Code (λ j → Cubical.fst α Embedding.↪ Decode j)
          → ((a : Cubical.fst α) → Cubical.Σ (Trees codes) λ w →
              Woset.WosetEquiv (F a) (tree-rank codes w))
          → ∥ Cubical.Σ (Woset.Woset ℓ ℓ) (λ γ →
              Simulation._≺_ γ (reflection-rank R)
              Sigma.× ((a : Cubical.fst α) → Simulation._≺_ (F a) γ)) ∥₁
        bound (Cubical._,_ j e) chosen =
          ∣ tree-rank codes (sup j v) Cubical.,
            (tree-below codes (sup j v) Cubical., above) ∣₁
          where
            pick : (t : Decode j) → Dec (Equiv.fiber (Cubical.fst e) t)
              → Trees codes
            pick t (yes found) = Cubical.fst (chosen (Cubical.fst found))
            pick t (no _) =
              sup (Mahlo.Formers.empty formers)
                (λ z → ⊥-elim (empty-absurd formers laws z))

            decision : (t : Decode j) → Dec (Equiv.fiber (Cubical.fst e) t)
            decision t =
              lem (Equiv.fiber (Cubical.fst e) t)
                (Embedding.isEmbedding→hasPropFibers (Cubical.snd e) t)

            v : Decode j → Trees codes
            v t = pick t (decision t)

            pick-at : (a : Cubical.fst α)
              (d : Dec (Equiv.fiber (Cubical.fst e) (Cubical.fst e a)))
              → pick (Cubical.fst e a) d Cubical.≡ Cubical.fst (chosen a)
            pick-at a (yes found) =
              Cubical.cong (λ b → Cubical.fst (chosen b))
                (Embedding.isEmbedding→Inj (Cubical.snd e)
                  (Cubical.fst found) a (Cubical.snd found))
            pick-at a (no outside) =
              Empty.rec (outside (a Cubical., Cubical.refl))

            above : (a : Cubical.fst α)
              → Simulation._≺_ (F a) (tree-rank codes (sup j v))
            above a =
              Simulation.≺RespectsEquivL (tree-rank codes (sup j v))
                (Woset.invWosetEquiv
                  (Woset.compWosetEquiv (Cubical.snd (chosen a))
                    (Equiv.invEq (Woset.WosetPath _ _)
                      (Cubical.cong (tree-rank codes)
                        (Cubical.sym
                          (pick-at a (decision (Cubical.fst e a))))))))
                (child (Decode j)
                  (λ t → Reflection.embed (Ambient.laws ℓ) codes (v t))
                  (Cubical.fst e a))

    ----------------------------------------------------------------------
    -- Inaccessibility

    inaccessible : Choice ℓ → Inaccessible (reflection-rank R)
    inaccessible choice = record
      { cardinal = Cardinal.cardinal Decode (reflection-rank R) cut
      ; uncountable =
          Cardinal.uncountable formers laws (reflection-rank R) cut
      ; regular = regular choice
      ; strong-limit =
          Cardinal.strong-limit formers laws (reflection-rank R) cut lem
      }
