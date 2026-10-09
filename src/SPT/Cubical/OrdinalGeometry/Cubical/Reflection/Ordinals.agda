{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Ordinals where

-- The ordinal of ordinals.  Ord(ℓ) is the well-order of the well-orders
-- of level ℓ under ≺, being a principal segment: the cubical library's
-- isWoset≺, the ordinal of ordinals of the HoTT book (§10.3) and OO of
-- TypeTopology.  Every W in Ord(ℓ) is equivalent to its own principal
-- segment Ord(ℓ) ↓ W (lowerset).  Also raise, which moves a well-order to
-- higher universes, and its equivalence with the original; the successor
-- W + 1 with its principal segments (successor-top, successor-below); and
-- simulations from principal segments, across universe levels
-- (segments→simulation), by which W + 1 is least above W
-- (successor-least).

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Level using (Lift; lift; lower)

import Cubical.Data.Empty as Empty
import Cubical.Data.Sigma.Properties as SigmaProperties
import Cubical.Data.Sum as Sum
open Sum using (_⊎_; inl; inr)
import Cubical.Data.Unit as Unit
open Unit using (Unit*; tt*)
import Cubical.Foundations.Equiv as Equiv
import Cubical.Foundations.HLevels as HLevels
import Cubical.Foundations.Isomorphism as Iso
import Cubical.Foundations.Prelude as Cubical
import Cubical.Functions.Embedding as Embedding
import Cubical.Induction.WellFounded as WellFounded
import Cubical.Relation.Binary.Extensionality as Extensionality
import Cubical.Relation.Binary.Order.Woset.Base as Woset
import Cubical.Relation.Binary.Order.Woset.Simulation as Simulation

private
  variable
    a b c d ℓ : Level

  Carrier : Woset.Woset a b → Set a
  Carrier W = Cubical.fst W

  Strict : (W : Woset.Woset a b) → Carrier W → Carrier W → Set b
  Strict W = Woset.WosetStr._≺_ (Cubical.snd W)

  laws : (W : Woset.Woset a b) → Woset.IsWoset (Strict W)
  laws W = Woset.WosetStr.isWoset (Cubical.snd W)

------------------------------------------------------------------------
-- Raising a well-order

-- Mathematical shape: raise c d W = (Lift_c |W| , Lift_d ∘ <_W).
raise : (c d : Level) → Woset.Woset a b → Woset.Woset (a ⊔ c) (b ⊔ d)
raise c d W =
  Woset.woset (Lift c (Carrier W)) lifted
    (Woset.iswoset set prop well-founded extensional transitive)
  where
    lifted : Lift c (Carrier W) → Lift c (Carrier W) → Set _
    lifted x y = Lift d (Strict W (lower x) (lower y))

    set : Cubical.isSet (Lift c (Carrier W))
    set = HLevels.isOfHLevelRetract 2 lower lift (λ _ → Cubical.refl)
      (Woset.IsWoset.is-set (laws W))

    prop : (x y : Lift c (Carrier W)) → Cubical.isProp (lifted x y)
    prop x y = HLevels.isOfHLevelRetract 1 lower lift (λ _ → Cubical.refl)
      (Woset.IsWoset.is-prop-valued (laws W) (lower x) (lower y))

    accessible : (x : Carrier W) → WellFounded.Acc (Strict W) x
      → WellFounded.Acc lifted (lift x)
    accessible x (WellFounded.acc smaller) =
      WellFounded.acc λ y p →
        accessible (lower y) (smaller (lower y) (lower p))

    well-founded : WellFounded.WellFounded lifted
    well-founded x =
      accessible (lower x)
        (Woset.IsWoset.is-well-founded (laws W) (lower x))

    extensional : Extensionality.isWeaklyExtensional lifted
    extensional =
      Extensionality.≺×→≡→isWeaklyExtensional lifted set prop
        λ x y same → Cubical.cong lift
          (Extensionality.isWeaklyExtensional→≺Equiv→≡ (Strict W)
            (Woset.IsWoset.is-weakly-extensional (laws W))
            (lower x) (lower y)
            λ z → Equiv.propBiimpl→Equiv
              (Woset.IsWoset.is-prop-valued (laws W) z (lower x))
              (Woset.IsWoset.is-prop-valued (laws W) z (lower y))
              (λ p → lower (Cubical.fst (same (lift z)) (lift p)))
              (λ p → lower (Cubical.snd (same (lift z)) (lift p))))

    transitive : (x y z : Lift c (Carrier W))
      → lifted x y → lifted y z → lifted x z
    transitive x y z p q = lift
      (Woset.IsWoset.is-trans (laws W) (lower x) (lower y) (lower z)
        (lower p) (lower q))

raise-equivalence : (c d : Level) (W : Woset.Woset a b)
  → Woset.WosetEquiv W (raise c d W)
raise-equivalence c d W =
  Cubical._,_ carrier
    (Woset.makeIsWosetEquiv carrier (λ x y p → lift p) (λ x y p → lower p))
  where
    carrier : Carrier W Equiv.≃ Lift c (Carrier W)
    carrier = Iso.isoToEquiv
      (Iso.iso lift lower (λ _ → Cubical.refl) (λ _ → Cubical.refl))

------------------------------------------------------------------------
-- The ordinal of ordinals

-- Mathematical shape: Ord(ℓ) = (Woset ℓ ℓ , ≺) : Woset(ℓ + 1, ℓ).
Ord : (ℓ : Level) → Woset.Woset (lsuc ℓ) ℓ
Ord ℓ = Woset.woset (Woset.Woset ℓ ℓ) Simulation._≺_ Simulation.isWoset≺

-- Mathematical shape: W ≃ Ord(ℓ) ↓ W, by w ↦ W ↓ w.  A point α ≺ W of
-- the segment is the segment of W at the bound of α, by univalence for
-- well-orders.
lowerset : (W : Woset.Woset ℓ ℓ)
  → Woset.WosetEquiv W (Simulation._↓_ (Ord ℓ) W)
lowerset {ℓ} W =
  Cubical._,_ carrier (Woset.makeIsWosetEquiv carrier forward backward)
  where
    Below : Set (lsuc ℓ)
    Below = Cubical.fst (Simulation._↓_ (Ord ℓ) W)

    segment : Carrier W → Below
    segment w =
      Cubical._,_ (Simulation._↓_ W w) (Simulation.↓Decreasing W w)

    bound : Below → Carrier W
    bound s = Cubical.fst (Cubical.snd s)

    recovered : (s : Below) → segment (bound s) Cubical.≡ s
    recovered s =
      SigmaProperties.Σ≡Prop
        (λ α → Simulation.isPropValued≺ α W)
        (Equiv.equivFun
          (Woset.WosetPath
            (Simulation._↓_ W (bound s))
            (Cubical.fst s))
          (Cubical.snd (Cubical.snd s)))

    carrier : Carrier W Equiv.≃ Below
    carrier = Iso.isoToEquiv
      (Iso.iso segment bound recovered (λ _ → Cubical.refl))

    forward : (x y : Carrier W) → Strict W x y
      → Simulation._≺_ (Simulation._↓_ W x) (Simulation._↓_ W y)
    forward = Simulation.↓Respects≺ W

    backward : (s t : Below)
      → Simulation._≺_ (Cubical.fst s) (Cubical.fst t)
      → Strict W (bound s) (bound t)
    backward s t s≺t =
      Simulation.↓Respects≺⁻ W (bound s) (bound t)
        (Simulation.≺RespectsEquivR
          (Simulation._↓_ W (bound s))
          (Woset.invWosetEquiv (Cubical.snd (Cubical.snd t)))
          (Simulation.≺RespectsEquivL (Cubical.fst t)
            (Woset.invWosetEquiv (Cubical.snd (Cubical.snd s)))
            s≺t))

------------------------------------------------------------------------
-- Successors

private
  -- The order of W + 1: inl x below inl y as x below y, every inl x below
  -- the top, and nothing above the top.
  successor-order : (W : Woset.Woset a b)
    → Carrier W ⊎ Unit* {a} → Carrier W ⊎ Unit* {a} → Set b
  successor-order W (inl x) (inl y) = Strict W x y
  successor-order W (inl x) (inr _) = Unit*
  successor-order W (inr _) _ = Empty.⊥*

  successor-prop : (W : Woset.Woset a b) (x y : Carrier W ⊎ Unit* {a})
    → Cubical.isProp (successor-order W x y)
  successor-prop W (inl x) (inl y) =
    Woset.IsWoset.is-prop-valued (laws W) x y
  successor-prop W (inl x) (inr _) = Unit.isPropUnit*
  successor-prop W (inr _) _ = Empty.isProp⊥*

  irreflexive : (W : Woset.Woset a b) (x : Carrier W)
    → WellFounded.Acc (Strict W) x → Strict W x x → Empty.⊥
  irreflexive W x (WellFounded.acc smaller) p = irreflexive W x (smaller x p) p

  successor-accessible : (W : Woset.Woset a b) (x : Carrier W)
    → WellFounded.Acc (Strict W) x
    → WellFounded.Acc (successor-order W) (inl x)
  successor-accessible W x (WellFounded.acc smaller) =
    WellFounded.acc λ
      { (inl y) p → successor-accessible W y (smaller y p)
      ; (inr _) (Cubical.lift ())
      }

  successor-extensional : (W : Woset.Woset a b) (x y : Carrier W ⊎ Unit* {a})
    → ((z : Carrier W ⊎ Unit* {a})
       → Cubical.Σ (successor-order W z x → successor-order W z y)
           (λ _ → successor-order W z y → successor-order W z x))
    → x Cubical.≡ y
  successor-extensional W (inl x) (inl y) same =
    Cubical.cong inl
      (Extensionality.isWeaklyExtensional→≺Equiv→≡ (Strict W)
        (Woset.IsWoset.is-weakly-extensional (laws W)) x y
        λ z → Equiv.propBiimpl→Equiv
          (Woset.IsWoset.is-prop-valued (laws W) z x)
          (Woset.IsWoset.is-prop-valued (laws W) z y)
          (Cubical.fst (same (inl z)))
          (Cubical.snd (same (inl z))))
  successor-extensional W (inl x) (inr _) same =
    Empty.rec
      (irreflexive W x (Woset.IsWoset.is-well-founded (laws W) x)
        (Cubical.snd (same (inl x)) tt*))
  successor-extensional W (inr _) (inl y) same =
    Empty.rec
      (irreflexive W y (Woset.IsWoset.is-well-founded (laws W) y)
        (Cubical.fst (same (inl y)) tt*))
  successor-extensional W (inr _) (inr _) same = Cubical.refl

  successor-transitive : (W : Woset.Woset a b) (x y z : Carrier W ⊎ Unit* {a})
    → successor-order W x y → successor-order W y z → successor-order W x z
  successor-transitive W (inl x) (inl y) (inl z) p q =
    Woset.IsWoset.is-trans (laws W) x y z p q
  successor-transitive W (inl x) (inl y) (inr _) p q = tt*
  successor-transitive W (inl x) (inr _) z p (Cubical.lift ())
  successor-transitive W (inr _) y z (Cubical.lift ()) q

-- Mathematical shape: W + 1 = (|W| ⊎ 1, <⁺), with a new point on top.
successor : Woset.Woset a b → Woset.Woset a b
successor W =
  Woset.woset (Carrier W ⊎ Unit*) (successor-order W)
    (Woset.iswoset set (successor-prop W) well-founded
      (Extensionality.≺×→≡→isWeaklyExtensional (successor-order W) set
        (successor-prop W) (successor-extensional W))
      (successor-transitive W))
  where
    set : Cubical.isSet (Carrier W ⊎ Unit*)
    set = Sum.isSet⊎ (Woset.IsWoset.is-set (laws W)) Unit.isSetUnit*

    well-founded : WellFounded.WellFounded (successor-order W)
    well-founded (inl x) =
      successor-accessible W x (Woset.IsWoset.is-well-founded (laws W) x)
    well-founded (inr _) =
      WellFounded.acc λ
        { (inl y) _ →
            successor-accessible W y
              (Woset.IsWoset.is-well-founded (laws W) y)
        ; (inr _) (Cubical.lift ())
        }

-- The new point of W + 1.
top : (W : Woset.Woset a b) → Carrier (successor W)
top W = inr tt*

-- Mathematical shape: (W + 1) ↓ top ≃ W.
successor-top : (W : Woset.Woset a b)
  → Woset.WosetEquiv (Simulation._↓_ (successor W) (top W)) W
successor-top W =
  Cubical._,_ carrier (Woset.makeIsWosetEquiv carrier forward backward)
  where
    Below : Set _
    Below = Carrier (Simulation._↓_ (successor W) (top W))

    forth : Below → Carrier W
    forth (Cubical._,_ (inl x) _) = x
    forth (Cubical._,_ (inr _) (Cubical.lift ()))

    back : Carrier W → Below
    back x = Cubical._,_ (inl x) tt*

    back-forth : (u : Below) → back (forth u) Cubical.≡ u
    back-forth (Cubical._,_ (inl x) _) = Cubical.refl
    back-forth (Cubical._,_ (inr _) (Cubical.lift ()))

    carrier : Below Equiv.≃ Carrier W
    carrier =
      Iso.isoToEquiv (Iso.iso forth back (λ _ → Cubical.refl) back-forth)

    forward : (u v : Below) → Strict (Simulation._↓_ (successor W) (top W)) u v
      → Strict W (forth u) (forth v)
    forward (Cubical._,_ (inl x) _) (Cubical._,_ (inl y) _) p = p
    forward (Cubical._,_ (inl x) _) (Cubical._,_ (inr _) (Cubical.lift ()))
    forward (Cubical._,_ (inr _) (Cubical.lift ())) v

    backward : (x y : Carrier W) → Strict W x y
      → Strict (Simulation._↓_ (successor W) (top W)) (back x) (back y)
    backward x y p = p

-- Mathematical shape: (W + 1) ↓ x ≃ W ↓ x, for x in W.
successor-below : (W : Woset.Woset a b) (x : Carrier W)
  → Woset.WosetEquiv (Simulation._↓_ (successor W) (inl x))
      (Simulation._↓_ W x)
successor-below W x =
  Cubical._,_ carrier (Woset.makeIsWosetEquiv carrier forward backward)
  where
    Below : Set _
    Below = Carrier (Simulation._↓_ (successor W) (inl x))

    forth : Below → Carrier (Simulation._↓_ W x)
    forth (Cubical._,_ (inl y) p) = Cubical._,_ y p
    forth (Cubical._,_ (inr _) (Cubical.lift ()))

    back : Carrier (Simulation._↓_ W x) → Below
    back (Cubical._,_ y p) = Cubical._,_ (inl y) p

    back-forth : (u : Below) → back (forth u) Cubical.≡ u
    back-forth (Cubical._,_ (inl y) p) = Cubical.refl
    back-forth (Cubical._,_ (inr _) (Cubical.lift ()))

    carrier : Below Equiv.≃ Carrier (Simulation._↓_ W x)
    carrier =
      Iso.isoToEquiv (Iso.iso forth back (λ _ → Cubical.refl) back-forth)

    forward : (u v : Below)
      → Strict (Simulation._↓_ (successor W) (inl x)) u v
      → Strict (Simulation._↓_ W x) (forth u) (forth v)
    forward (Cubical._,_ (inl y) _) (Cubical._,_ (inl z) _) p = p
    forward (Cubical._,_ (inl y) _) (Cubical._,_ (inr _) (Cubical.lift ()))
    forward (Cubical._,_ (inr _) (Cubical.lift ())) v

    backward : (u v : Carrier (Simulation._↓_ W x))
      → Strict (Simulation._↓_ W x) u v
      → Strict (Simulation._↓_ (successor W) (inl x)) (back u) (back v)
    backward u v p = p

-- Mathematical shape: W ≺ W + 1, at the top.
successor-strict : (W : Woset.Woset a b) → Simulation._≺_ W (successor W)
successor-strict W = Cubical._,_ (top W) (successor-top W)

-- Every principal segment of W + 1 is W or a principal segment of W.
successor-segments : (W : Woset.Woset a b) (z : Carrier (successor W))
  → Woset.WosetEquiv (Simulation._↓_ (successor W) z) W
    ⊎ Cubical.Σ (Carrier W) λ x →
        Woset.WosetEquiv (Simulation._↓_ (successor W) z)
          (Simulation._↓_ W x)
successor-segments W (inl x) = inr (Cubical._,_ x (successor-below W x))
successor-segments W (inr _) = inl (successor-top W)

------------------------------------------------------------------------
-- Simulations from principal segments

-- (Π h. (H ↓ h) ≺ K) → H ≼ K: send h to the point of K bounding H ↓ h.
-- H and K may have different carrier and relation levels.

segments→simulation :
    {H : Woset.Woset a b}
    {K : Woset.Woset c d}
  → ((point : Cubical.fst H) →
      Simulation._≺_ (Simulation._↓_ H point) K)
  → Simulation._≼_ H K
segments→simulation {H = H} {K = K} strict =
  point-map Cubical., (point-map-monotone Cubical., point-map-lifting)
  where
    point-map : Cubical.fst H → Cubical.fst K
    point-map point = Cubical.fst (strict point)

    principal-equivalence :
        (point : Cubical.fst H)
      → Woset.WosetEquiv
          (Simulation._↓_ K (point-map point))
          (Simulation._↓_ H point)
    principal-equivalence point = Cubical.snd (strict point)

    point-map-monotone :
        (left right : Cubical.fst H)
      → Woset.WosetStr._≺_ (Cubical.snd H) left right
      → Woset.WosetStr._≺_ (Cubical.snd K)
          (point-map left)
          (point-map right)
    point-map-monotone left right left<right =
      Simulation.↓Respects≺⁻ K
        (point-map left)
        (point-map right)
        (Simulation.≺RespectsEquiv
          (Woset.invWosetEquiv (principal-equivalence left))
          (Woset.invWosetEquiv (principal-equivalence right))
          (Simulation.↓Respects≺ H left right left<right))

    point-map-lifting :
        (point : Cubical.fst H)
        (below : Cubical.fst K)
      → Woset.WosetStr._≺_ (Cubical.snd K) below (point-map point)
      → Cubical.Σ
          (Cubical.Σ (Cubical.fst H) λ predecessor →
            Woset.WosetStr._≺_ (Cubical.snd H) predecessor point)
          (λ predecessor → point-map (Cubical.fst predecessor) Cubical.≡ below)
    point-map-lifting point below below<image =
      (predecessor Cubical., predecessor<point)
      Cubical., image-predecessor≡below
      where
        below-segment-strict-point-segment :
          Simulation._≺_
            (Simulation._↓_ K below)
            (Simulation._↓_ H point)
        below-segment-strict-point-segment =
          Simulation.≺RespectsEquivR
            (Simulation._↓_ K below)
            (principal-equivalence point)
            (Simulation.↓Respects≺ K below (point-map point) below<image)

        predecessor-with-strict-witness :
          Cubical.fst (Simulation._↓_ H point)
        predecessor-with-strict-witness =
          Cubical.fst below-segment-strict-point-segment

        predecessor : Cubical.fst H
        predecessor = Cubical.fst predecessor-with-strict-witness

        predecessor<point :
          Woset.WosetStr._≺_ (Cubical.snd H) predecessor point
        predecessor<point = Cubical.snd predecessor-with-strict-witness

        predecessor-segment-to-nested-segment :
          Woset.WosetEquiv
            (Simulation._↓_ H predecessor)
            (Simulation._↓_ (Simulation._↓_ H point)
              predecessor-with-strict-witness)
        predecessor-segment-to-nested-segment =
          Equiv.invEq
            (Woset.WosetPath
              (Simulation._↓_ H predecessor)
              (Simulation._↓_ (Simulation._↓_ H point)
                predecessor-with-strict-witness))
            (Cubical.sym
              (Simulation.↓Absorb H point predecessor predecessor<point))

        image-segment→below :
          Woset.WosetEquiv
            (Simulation._↓_ K (point-map predecessor))
            (Simulation._↓_ K below)
        image-segment→below =
          Woset.compWosetEquiv
            (principal-equivalence predecessor)
            (Woset.compWosetEquiv
              predecessor-segment-to-nested-segment
              (Cubical.snd below-segment-strict-point-segment))

        image-predecessor≡below : point-map predecessor Cubical.≡ below
        image-predecessor≡below =
          Embedding.isEmbedding→Inj
            (Simulation.isEmbedding↓ K)
            (point-map predecessor)
            below
            (Equiv.equivFun
              (Woset.WosetPath
                (Simulation._↓_ K (point-map predecessor))
                (Simulation._↓_ K below))
              image-segment→below)

------------------------------------------------------------------------
-- Successors are least

-- Mathematical shape: W ≺ B → W + 1 ≼ B, for B of any level.  Every
-- principal segment of W + 1 is W or a principal segment of W, and both
-- lie below B.
successor-least : (W : Woset.Woset a b) (B : Woset.Woset c d)
  → Simulation._≺_ W B → Simulation._≼_ (successor W) B
successor-least W B strict =
  segments→simulation {H = successor W} {K = B} λ z →
    below z (successor-segments W z)
  where
    below : (z : Carrier (successor W))
      → Woset.WosetEquiv (Simulation._↓_ (successor W) z) W
        ⊎ Cubical.Σ (Carrier W) (λ x →
            Woset.WosetEquiv (Simulation._↓_ (successor W) z)
              (Simulation._↓_ W x))
      → Simulation._≺_ (Simulation._↓_ (successor W) z) B
    below z (inl e) =
      Simulation.≺RespectsEquivL B (Woset.invWosetEquiv e) strict
    below z (inr (Cubical._,_ x e)) =
      Simulation.≺RespectsEquivL B (Woset.invWosetEquiv e)
        (Simulation.isTrans≺ (Simulation._↓_ W x) W B
          (Simulation.↓Decreasing W x) strict)
