{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.Hartogs.PowerSet where

-- Embeddings into Boolean power sets, under excluded middle.  For an
-- embedding e : A ↪ B, extending by false outside the image embeds
-- (A → 𝟐) into (B → 𝟐) (extend).  For a set Q whose points are, merely,
-- values of a map π : X → Q,
--
--   q ↦ (x ↦ [π x = q])
--
-- embeds Q into (X → 𝟐) (classes).  Excluded middle decides the
-- propositions b ∈ image e and π x = q.

open import Agda.Primitive using (Level)

import Cubical.Data.Bool as Bool
open Bool using (Bool; true; false)
import Cubical.Data.Empty as Empty
import Cubical.Foundations.Equiv as Equiv
import Cubical.Foundations.HLevels as HLevels
import Cubical.Foundations.Prelude as Cubical
import Cubical.Functions.Embedding as Embedding
import Cubical.HITs.PropositionalTruncation as Truncation
open Truncation using (∥_∥₁)
import Cubical.Relation.Nullary as Nullary
open Nullary using (Dec; yes; no)

open import SPT.Cubical.OrdinalGeometry.Cubical.Hartogs.Countability using
  (ExcludedMiddle)

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- Decisions as Booleans

decide : {P : Set ℓ} → Dec P → Bool
decide (yes _) = true
decide (no _) = false

decide-holds : {P : Set ℓ} (d : Dec P) → decide d Cubical.≡ true → P
decide-holds (yes p) _ = p
decide-holds (no _) q = Empty.rec (Bool.false≢true q)

holds-decide : {P : Set ℓ} (d : Dec P) → P → decide d Cubical.≡ true
holds-decide (yes _) _ = Cubical.refl
holds-decide (no ¬p) p = Empty.rec (¬p p)

------------------------------------------------------------------------
-- Extension along an embedding

module _ (lem : ExcludedMiddle ℓ) {A B : Set ℓ} (e : A Embedding.↪ B) where

  private
    pick : (p : A → Bool) (b : B) → Dec (Equiv.fiber (Cubical.fst e) b)
      → Bool
    pick p b (yes found) = p (Cubical.fst found)
    pick p b (no _) = false

    pick-at : (p : A → Bool) (a : A)
      (d : Dec (Equiv.fiber (Cubical.fst e) (Cubical.fst e a)))
      → pick p (Cubical.fst e a) d Cubical.≡ p a
    pick-at p a (yes found) =
      Cubical.cong p
        (Embedding.isEmbedding→Inj (Cubical.snd e) (Cubical.fst found) a
          (Cubical.snd found))
    pick-at p a (no outside) = Empty.rec (outside (a Cubical., Cubical.refl))

  -- extension p (e a) = p a, and extension p b = false off the image.
  extension : (A → Bool) → B → Bool
  extension p b =
    pick p b
      (lem (Equiv.fiber (Cubical.fst e) b)
        (Embedding.isEmbedding→hasPropFibers (Cubical.snd e) b))

  extension-at : (p : A → Bool) (a : A)
    → extension p (Cubical.fst e a) Cubical.≡ p a
  extension-at p a =
    pick-at p a
      (lem (Equiv.fiber (Cubical.fst e) (Cubical.fst e a))
        (Embedding.isEmbedding→hasPropFibers (Cubical.snd e)
          (Cubical.fst e a)))

  -- Mathematical shape: (A ↪ B) → (A → 𝟐) ↪ (B → 𝟐).
  extend : (A → Bool) Embedding.↪ (B → Bool)
  extend =
    extension Cubical.,
    Embedding.injEmbedding (HLevels.isSetΠ λ _ → Bool.isSetBool)
      λ {p} {q} same →
        Cubical.funExt λ a →
          Cubical.sym (extension-at p a)
          Cubical.∙ Cubical.cong (λ g → g (Cubical.fst e a)) same
          Cubical.∙ extension-at q a

------------------------------------------------------------------------
-- A set covered by a map

module _ (lem : ExcludedMiddle ℓ) {X Q : Set ℓ} (Q-set : Cubical.isSet Q)
  (π : X → Q) (onto : (q : Q) → ∥ Equiv.fiber π q ∥₁) where

  -- class q x = [π x = q].
  class : Q → X → Bool
  class q x = decide (lem (π x Cubical.≡ q) (Q-set (π x) q))

  -- Mathematical shape: Q ↪ (X → 𝟐).  Two classes that agree at a point
  -- x over q contain x, so π x is both points.
  classes : Q Embedding.↪ (X → Bool)
  classes =
    class Cubical.,
    Embedding.injEmbedding (HLevels.isSetΠ λ _ → Bool.isSetBool)
      λ {q} {q′} same →
        Truncation.rec (Q-set q q′)
          (λ found →
            let x = Cubical.fst found
                at-q = holds-decide (lem (π x Cubical.≡ q) (Q-set (π x) q))
                  (Cubical.snd found)
                at-q′ =
                  Cubical.sym (Cubical.cong (λ g → g x) same) Cubical.∙ at-q
            in Cubical.sym (Cubical.snd found)
               Cubical.∙ decide-holds
                 (lem (π x Cubical.≡ q′) (Q-set (π x) q′)) at-q′)
          (onto q)
