{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.TypeTopology.Arithmetic where

-- The reflection commutes with the arithmetic of TypeTopology's ordinals,
-- with function extensionality from Cubical:
--
--   (P + Q)′ ≃ P′ +ₒ Q′,   (P + 1)′ ≃ P′ +ₒ 𝟙ₒ,   (P · Q)′ ≃ P′ ×ₒ Q′,
--
-- as equivalences of well-ordered sets, the right sides read through the
-- reverse bridge woset, which keeps carrier and relation. A summand point
-- goes to the class in its summand. For the product, P · Q is unfolded to
-- its normalized blocks: the normalized point a of P in the copy at the
-- normalized point q of Q goes to ([a], [q]), and both sides order the
-- second component first. On TypeTopology's side each equivalence gives
-- simulations in both directions (simulations).
--
-- +ₒ, ×ₒ and 𝟙ₒ are TypeTopology's, built as in Ordinals.Arithmetic from
-- Ordinals.WellOrderArithmetic (plus, times, prop). Ordinals.Arithmetic
-- itself cannot be imported next to the standard library or Cubical: its
-- dependency Naturals.Addition binds the NATPLUS builtin, which
-- Agda.Builtin.Nat already binds.

open import Agda.Primitive using (Level)
open import Data.Nat using (zero)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
import Data.Unit.Polymorphic as Polymorphic
open import Level using (lift)
open import Relation.Binary.PropositionalEquality using (sym; trans; subst)
import Relation.Binary.PropositionalEquality as Inductive

import SPT.Cubical.TypeTopology.MLTT.Identity-Type as TypeTopologyIdentity
import SPT.Cubical.TypeTopology.MLTT.Plus as TypeTopologyPlus
import SPT.Cubical.TypeTopology.MLTT.Sigma-Type as TypeTopologySigma
import SPT.Cubical.TypeTopology.MLTT.Sigma as TypeTopologyProduct
import SPT.Cubical.TypeTopology.MLTT.Unit as TypeTopologyUnit
open import SPT.Cubical.TypeTopology.Ordinals.Type using (Ordinal)
import SPT.Cubical.TypeTopology.Ordinals.WellOrderArithmetic
  as WellOrderArithmetic
open import SPT.Cubical.TypeTopology.UF.Subsingletons using (𝟙-is-prop)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
import SPT.Cubical.OrdinalGeometry.Presentation.Map as Maps
import SPT.Cubical.OrdinalGeometry.Presentation.Successor as Adjoin
open import SPT.Cubical.OrdinalGeometry.Presentation.Sum using (_+_)
import SPT.Cubical.OrdinalGeometry.ExactOrder.Base as Order
import SPT.Cubical.OrdinalGeometry.Presentation.Normalization as Normal
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Multiplication using (_·_)
open import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.OrderType using
  ( Class; Less; orderType
  ; Less-isProp
  ; Less-intro
  ; Less-witness
  )
open import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Representative
  using
  (effective)
open import SPT.Cubical.OrdinalGeometry.Cubical.TypeTopology.Bridge using
  (toOrdinal; ＝→path)
open import SPT.Cubical.OrdinalGeometry.Cubical.TypeTopology.Simulation
  using (_⊴_; woset; to)
open import SPT.Cubical.OrdinalGeometry.Cubical.TypeTopology.FunExt
  using
  (funext)

import Cubical.Data.Equality.Conversion as EqualityConversion
import Cubical.Foundations.Equiv as Equiv
import Cubical.Foundations.HLevels as HLevels
import Cubical.Foundations.Isomorphism as Isomorphism
import Cubical.Foundations.Prelude as Cubical
import Cubical.HITs.SetQuotients as Quotient
import Cubical.Relation.Binary.Order.Woset.Base as Woset
import Cubical.Relation.Binary.Order.Woset.Simulation as Simulation

open TypeTopologySigma.Σ using (pr₁; pr₂)

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- TypeTopology's sum, product and one

infixl 6 _+ₒ_
infixl 7 _×ₒ_

-- Mathematical shape: α +ₒ β on ⟨α⟩ + ⟨β⟩, every left point below every
-- right point.
_+ₒ_ : Ordinal ℓ → Ordinal ℓ → Ordinal ℓ
α +ₒ β =
  TypeTopologySigma._,_ (TypeTopologyPlus._+_ (pr₁ α) (pr₁ β))
    (TypeTopologySigma._,_
      (WellOrderArithmetic.plus.order (pr₁ (pr₂ α)) (pr₁ (pr₂ β)))
      (WellOrderArithmetic.plus.well-order (pr₁ (pr₂ α)) (pr₁ (pr₂ β))
        (pr₂ (pr₂ α)) (pr₂ (pr₂ β))))

-- Mathematical shape: α ×ₒ β on ⟨α⟩ × ⟨β⟩, the second component first.
_×ₒ_ : Ordinal ℓ → Ordinal ℓ → Ordinal ℓ
α ×ₒ β =
  TypeTopologySigma._,_ (TypeTopologyProduct._×_ (pr₁ α) (pr₁ β))
    (TypeTopologySigma._,_
      (WellOrderArithmetic.times.order (pr₁ (pr₂ α)) (pr₁ (pr₂ β)))
      (WellOrderArithmetic.times.well-order (pr₁ (pr₂ α)) (pr₁ (pr₂ β))
        funext (pr₂ (pr₂ α)) (pr₂ (pr₂ β))))

-- The ordinal with one point.
𝟙ₒ : Ordinal ℓ
𝟙ₒ =
  TypeTopologySigma._,_ TypeTopologyUnit.𝟙
    (TypeTopologySigma._,_ (WellOrderArithmetic.prop.order _ 𝟙-is-prop)
      (WellOrderArithmetic.prop.well-order _ 𝟙-is-prop))

------------------------------------------------------------------------
-- Comparison

-- The TypeTopology ordinal of a presentation.
ordinal : 𝒫 ℓ → Ordinal ℓ
ordinal P = toOrdinal (orderType P)

-- An equivalence with woset β gives TypeTopology simulations both ways.
simulations : (A : Woset.Woset ℓ ℓ) (β : Ordinal ℓ)
  → Woset.WosetEquiv A (woset β)
  → TypeTopologyProduct._×_ (toOrdinal A ⊴ β)
      (β ⊴ toOrdinal A)
simulations A β e =
  TypeTopologySigma._,_ (to A β (Simulation.WosetEquiv→≼ e))
    (to (woset β) (toOrdinal A)
      (Simulation.WosetEquiv→≼ (Woset.invWosetEquiv e)))

private
  set : (β : Ordinal ℓ) → Cubical.isSet (Cubical.fst (woset β))
  set β =
    Woset.IsWoset.is-set (Woset.WosetStr.isWoset (Cubical.snd (woset β)))

  prop : (β : Ordinal ℓ) (u v : Cubical.fst (woset β))
    → Cubical.isProp (Woset.WosetStr._≺_ (Cubical.snd (woset β)) u v)
  prop β =
    Woset.IsWoset.is-prop-valued
      (Woset.WosetStr.isWoset (Cubical.snd (woset β)))

------------------------------------------------------------------------
-- Sums

-- Mathematical shape: (P + Q)′ ≃ P′ +ₒ Q′, inj₁ x ↦ inl [x] and
-- inj₂ y ↦ inr [y].
sum : (P Q : 𝒫 ℓ)
  → Woset.WosetEquiv (orderType (P + Q))
      (woset (ordinal P +ₒ ordinal Q))
sum P Q =
  Cubical._,_ equivalence
    (Woset.iswosetequiv λ u v →
      Equiv.propBiimpl→Equiv
        (Less-isProp (P + Q) u v)
        (prop β (forth u) (forth v)) (forward u v) (backward u v))
  where
  β = ordinal P +ₒ ordinal Q

  _⊏_ = Woset.WosetStr._≺_ (Cubical.snd (woset β))

  image : 𝒫.X (P + Q) → Cubical.fst (woset β)
  image (inj₁ x) = TypeTopologyPlus.inl Quotient.[ x ]
  image (inj₂ y) = TypeTopologyPlus.inr Quotient.[ y ]

  respect : (u v : 𝒫.X (P + Q)) → 𝒫._≈_ (P + Q) u v
    → image u Cubical.≡ image v
  respect (inj₁ x) (inj₁ x′) p =
    Cubical.cong TypeTopologyPlus.inl (Quotient.eq/ x x′ p)
  respect (inj₂ y) (inj₂ y′) p =
    Cubical.cong TypeTopologyPlus.inr (Quotient.eq/ y y′ p)
  respect (inj₁ _) (inj₂ _) (lift ())
  respect (inj₂ _) (inj₁ _) (lift ())

  forth : Class (P + Q) → Cubical.fst (woset β)
  forth = Quotient.rec (set β) image respect

  back : Cubical.fst (woset β) → Class (P + Q)
  back (TypeTopologyPlus.inl a) =
    Quotient.rec Quotient.squash/ (λ x → Quotient.[ inj₁ x ])
      (λ x x′ p → Quotient.eq/ (inj₁ x) (inj₁ x′) p) a
  back (TypeTopologyPlus.inr b) =
    Quotient.rec Quotient.squash/ (λ y → Quotient.[ inj₂ y ])
      (λ y y′ p → Quotient.eq/ (inj₂ y) (inj₂ y′) p) b

  forth-back : (c : Cubical.fst (woset β)) → forth (back c) Cubical.≡ c
  forth-back (TypeTopologyPlus.inl a) =
    Quotient.elimProp
      {P = λ a → forth (back (TypeTopologyPlus.inl a))
        Cubical.≡ TypeTopologyPlus.inl a}
      (λ _ → set β _ _) (λ _ → Cubical.refl) a
  forth-back (TypeTopologyPlus.inr b) =
    Quotient.elimProp
      {P = λ b → forth (back (TypeTopologyPlus.inr b))
        Cubical.≡ TypeTopologyPlus.inr b}
      (λ _ → set β _ _) (λ _ → Cubical.refl) b

  back-forth : (u : Class (P + Q))
    → back (forth u) Cubical.≡ u
  back-forth =
    Quotient.elimProp (λ _ → Quotient.squash/ _ _)
      λ { (inj₁ x) → Cubical.refl ; (inj₂ y) → Cubical.refl }

  equivalence : Equiv._≃_ (Class (P + Q))
    (Cubical.fst (woset β))
  equivalence =
    Isomorphism.isoToEquiv
      (Isomorphism.iso forth back forth-back back-forth)

  forward′ : (u v : 𝒫.X (P + Q)) → 𝒫._<_ (P + Q) u v
    → image u ⊏ image v
  forward′ (inj₁ x) (inj₁ x′) p =
    Less-intro P p
  forward′ (inj₁ x) (inj₂ y) _ = TypeTopologyUnit.⋆
  forward′ (inj₂ y) (inj₁ x) (lift ())
  forward′ (inj₂ y) (inj₂ y′) p =
    Less-intro Q p

  backward′ : (u v : 𝒫.X (P + Q)) → image u ⊏ image v
    → 𝒫._<_ (P + Q) u v
  backward′ (inj₁ x) (inj₁ x′) t =
    Less-witness P t
  backward′ (inj₁ x) (inj₂ y) _ = Polymorphic.tt
  backward′ (inj₂ y) (inj₁ x) ()
  backward′ (inj₂ y) (inj₂ y′) t =
    Less-witness Q t

  forward : (u v : Class (P + Q))
    → Less (P + Q) u v → forth u ⊏ forth v
  forward =
    Quotient.elimProp2
      (λ u v → HLevels.isPropΠ λ _ → prop β (forth u) (forth v))
      λ u v s → forward′ u v
        (Less-witness (P + Q) s)

  backward : (u v : Class (P + Q))
    → forth u ⊏ forth v → Less (P + Q) u v
  backward =
    Quotient.elimProp2
      (λ u v → HLevels.isPropΠ λ _ →
        Less-isProp (P + Q) u v)
      λ u v t → Less-intro (P + Q)
        (backward′ u v t)

------------------------------------------------------------------------
-- Successors

-- Mathematical shape: (P + 1)′ ≃ P′ +ₒ 𝟙ₒ, the top to the point of 𝟙ₒ.
successor : (P : 𝒫 ℓ)
  → Woset.WosetEquiv (orderType (Maps.Successor.next P))
      (woset (ordinal P +ₒ 𝟙ₒ))
successor {ℓ} P =
  Cubical._,_ equivalence
    (Woset.iswosetequiv λ u v →
      Equiv.propBiimpl→Equiv
        (Less-isProp N u v)
        (prop β (forth u) (forth v)) (forward u v) (backward u v))
  where
  N = Maps.Successor.next P
  β = ordinal P +ₒ 𝟙ₒ

  module E = Presented.Diagonal.Successor
    (Adjoin.constant P) zero

  _⊏_ = Woset.WosetStr._≺_ (Cubical.snd (woset β))

  image : E.Entry → Cubical.fst (woset β)
  image (E.point x) = TypeTopologyPlus.inl Quotient.[ x ]
  image E.top = TypeTopologyPlus.inr TypeTopologyUnit.⋆

  respect : (u v : E.Entry) → u E.≈ v → image u Cubical.≡ image v
  respect (E.point x) (E.point x′) (E.point≈ p) =
    Cubical.cong TypeTopologyPlus.inl (Quotient.eq/ x x′ p)
  respect E.top E.top E.top≈ = Cubical.refl

  forth : Class N → Cubical.fst (woset β)
  forth = Quotient.rec (set β) image respect

  back : Cubical.fst (woset β) → Class N
  back (TypeTopologyPlus.inl a) =
    Quotient.rec Quotient.squash/ (λ x → Quotient.[ E.point x ])
      (λ x x′ p → Quotient.eq/ (E.point x) (E.point x′) (E.point≈ p)) a
  back (TypeTopologyPlus.inr TypeTopologyUnit.⋆) = Quotient.[ E.top ]

  forth-back : (c : Cubical.fst (woset β)) → forth (back c) Cubical.≡ c
  forth-back (TypeTopologyPlus.inl a) =
    Quotient.elimProp
      {P = λ a → forth (back (TypeTopologyPlus.inl a))
        Cubical.≡ TypeTopologyPlus.inl a}
      (λ _ → set β _ _) (λ _ → Cubical.refl) a
  forth-back (TypeTopologyPlus.inr TypeTopologyUnit.⋆) = Cubical.refl

  back-forth : (u : Class N) → back (forth u) Cubical.≡ u
  back-forth =
    Quotient.elimProp (λ _ → Quotient.squash/ _ _)
      λ { (E.point x) → Cubical.refl ; E.top → Cubical.refl }

  equivalence : Equiv._≃_ (Class N) (Cubical.fst (woset β))
  equivalence =
    Isomorphism.isoToEquiv
      (Isomorphism.iso forth back forth-back back-forth)

  forward′ : (u v : E.Entry) → u E.< v → image u ⊏ image v
  forward′ (E.point x) (E.point x′) (E.point< p) =
    Less-intro P p
  forward′ (E.point x) E.top E.point<top = TypeTopologyUnit.⋆

  backward′ : (u v : E.Entry) → image u ⊏ image v → u E.< v
  backward′ (E.point x) (E.point x′) t =
    E.point< (Less-witness P t)
  backward′ (E.point x) E.top _ = E.point<top
  backward′ E.top (E.point x) ()
  backward′ E.top E.top ()

  forward : (u v : Class N)
    → Less N u v → forth u ⊏ forth v
  forward =
    Quotient.elimProp2
      (λ u v → HLevels.isPropΠ λ _ → prop β (forth u) (forth v))
      λ u v s →
        forward′ u v (Less-witness N s)

  backward : (u v : Class N)
    → forth u ⊏ forth v → Less N u v
  backward =
    Quotient.elimProp2
      (λ u v → HLevels.isPropΠ λ _ →
        Less-isProp N u v)
      λ u v t →
        Less-intro N (backward′ u v t)

------------------------------------------------------------------------
-- Products

opaque
  unfolding _·_

  -- Mathematical shape: (P · Q)′ ≃ P′ ×ₒ Q′, the point a in the copy at
  -- q going to ([a], [q]).
  product : (P Q : 𝒫 ℓ)
    → Woset.WosetEquiv (orderType (P · Q))
        (woset (ordinal P ×ₒ ordinal Q))
  product {ℓ} P Q =
    Cubical._,_ equivalence
      (Woset.iswosetequiv λ u v →
        Equiv.propBiimpl→Equiv
          (Less-isProp (P · Q) u v)
          (prop β (forth u) (forth v)) (forward u v) (backward u v))
    where
    β : Ordinal ℓ
    β = ordinal P ×ₒ ordinal Q

    _⊏_ : Cubical.fst (woset β) → Cubical.fst (woset β) → Set ℓ
    _⊏_ = Woset.WosetStr._≺_ (Cubical.snd (woset β))

    module Blocks = Order.Sum (Normal.order Q) (λ _ → Normal.order P)

    image : 𝒫.X (P · Q) → Cubical.fst (woset β)
    image (lift (q , a)) =
      TypeTopologySigma._,_ Quotient.[ Normal.representative P a ]
        Quotient.[ Normal.representative Q q ]

    respect : (u v : 𝒫.X (P · Q)) → 𝒫._≈_ (P · Q) u v
      → image u Cubical.≡ image v
    respect (lift u) (lift v) (lift e) =
      Cubical.cong (λ z → image (lift z)) (EqualityConversion.eqToPath e)

    forth : Class (P · Q) → Cubical.fst (woset β)
    forth = Quotient.rec (set β) image respect

    back : Cubical.fst (woset β) → Class (P · Q)
    back (TypeTopologySigma._,_ c d) =
      Quotient.rec2 Quotient.squash/
        (λ x y → Quotient.[ lift (Normal.class Q y , Normal.class P x) ])
        (λ x x′ y p → Quotient.eq/ _ _
          (lift (Inductive.cong (λ z → Normal.class Q y , z)
            (Normal.class-resp P p))))
        (λ x y y′ p → Quotient.eq/ _ _
          (lift (Inductive.cong (λ z → z , Normal.class P x)
            (Normal.class-resp Q p))))
        c d

    forth-back : (c : Cubical.fst (woset β)) → forth (back c) Cubical.≡ c
    forth-back (TypeTopologySigma._,_ c d) =
      Quotient.elimProp2
        {P = λ c d → forth (back (TypeTopologySigma._,_ c d))
          Cubical.≡ TypeTopologySigma._,_ c d}
        (λ _ _ → set β _ _)
        (λ x y → Cubical.cong₂ TypeTopologySigma._,_
          (Quotient.eq/ _ _ (Normal.representative-class P x))
          (Quotient.eq/ _ _ (Normal.representative-class Q y)))
        c d

    back-forth : (u : Class (P · Q))
      → back (forth u) Cubical.≡ u
    back-forth =
      Quotient.elimProp (λ _ → Quotient.squash/ _ _)
        λ { (lift (q , a)) → Quotient.eq/ _ _
              (lift (Inductive.cong₂ _,_ (Normal.class-representative Q q)
                (Normal.class-representative P a))) }

    equivalence : Equiv._≃_ (Class (P · Q))
      (Cubical.fst (woset β))
    equivalence =
      Isomorphism.isoToEquiv
        (Isomorphism.iso forth back forth-back back-forth)

    class : 𝒫.X Q → Class Q
    class x = Quotient.[ x ]

    -- Equal classes of points of Q have equal normalized points.
    same : (q q′ : Normal.Point Q)
      → TypeTopologyIdentity._＝_ (class (Normal.representative Q q))
          (class (Normal.representative Q q′))
      → q Inductive.≡ q′
    same q q′ e =
      trans (sym (Normal.class-representative Q q))
        (trans (Normal.class-resp Q (effective Q
          (＝→path e)))
          (Normal.class-representative Q q′))

    forward′ : (u v : 𝒫.X (P · Q)) → 𝒫._<_ (P · Q) u v
      → image u ⊏ image v
    forward′ (lift (q , a)) (lift (q′ , a′))
      (lift (Order.Sum.earlier p)) =
      TypeTopologyPlus.inl
        (Less-intro Q
          (Normal.representative-strict Q {q} {q′} p))
    forward′ (lift (q , a)) (lift (q′ , a′))
      (lift (Order.Sum.within _ p)) =
      TypeTopologyPlus.inr
        (TypeTopologySigma._,_ TypeTopologyIdentity.refl
          (Less-intro P
            (Normal.representative-strict P {a} {a′} p)))

    backward′ : (u v : 𝒫.X (P · Q)) → image u ⊏ image v
      → 𝒫._<_ (P · Q) u v
    backward′ (lift (q , a)) (lift (q′ , a′)) (TypeTopologyPlus.inl r) =
      lift (Blocks.earlier
        (Normal.representative-reflect Q {q} {q′}
          (Less-witness Q r)))
    backward′ (lift (q , a)) (lift (q′ , a′))
      (TypeTopologyPlus.inr (TypeTopologySigma._,_ e r)) =
      subst (λ z → 𝒫._<_ (P · Q) (lift (q , a)) (lift (z , a′)))
        (same q q′ e)
        (lift (Blocks.within q
          (Normal.representative-reflect P {a} {a′}
            (Less-witness P r))))

    forward : (u v : Class (P · Q))
      → Less (P · Q) u v → forth u ⊏ forth v
    forward =
      Quotient.elimProp2
        (λ u v → HLevels.isPropΠ λ _ → prop β (forth u) (forth v))
        λ u v s → forward′ u v
          (Less-witness (P · Q) s)

    backward : (u v : Class (P · Q))
      → forth u ⊏ forth v → Less (P · Q) u v
    backward =
      Quotient.elimProp2
        (λ u v → HLevels.isPropΠ λ _ →
          Less-isProp (P · Q) u v)
        λ u v t → Less-intro (P · Q)
          (backward′ u v t)
