{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.TypeTopology.OrdinalOfOrdinals
  where

-- Cubical's ordinal of ordinals is TypeTopology's OO.  The bridge
-- toOrdinal : Woset(ℓ, ℓ) → Ordinal ℓ is an equivalence of types with
-- inverse woset (ordinals), and it takes principal segments to
-- TypeTopology's segments (segment), so ≺ to ⊲ in both directions
-- (preserves, reflects).  It is therefore an order equivalence from
-- Ord(ℓ), its relation lifted by smallToOrdinal, to OO ℓ of
-- Ordinals.OrdinalOfOrdinals, instantiated with the univalence of
-- TypeTopology.Univalence (equivalence); TypeTopology's eqtoidₒ makes the
-- two identical (identity).  Segments of Ord(ℓ) are segments of OO ℓ
-- (segment-OO), and γ ⊲ ⌜K⌝ is woset γ ≺ K (order).  Read in OO: ω₁(ℓ) is
-- the segment of OO ℓ below the ordinal of Ω (omega-one), so
-- ω₁(ℓ) ⊲ OO ℓ (principal), and the ordinals below that point are exactly
-- the merely presented ones (below).

open import Agda.Primitive using (Level; lsuc)
open import Level using (lift; lower)

import Cubical.Foundations.Equiv as Equiv
import Cubical.Foundations.Isomorphism as Isomorphism
import Cubical.Foundations.Prelude as Cubical
import Cubical.Relation.Binary.Order.Woset.Base as Woset
import Cubical.Relation.Binary.Order.Woset.Simulation as Simulation

import SPT.Cubical.TypeTopology.MLTT.Identity-Type as Identity
import SPT.Cubical.TypeTopology.MLTT.Sigma-Type as Sigma
open Sigma.Σ using (pr₁; pr₂)
open import SPT.Cubical.TypeTopology.UF.Equiv using (qinvs-are-equivs)
open import SPT.Cubical.TypeTopology.Ordinals.Type using (Ordinal)
import SPT.Cubical.TypeTopology.Ordinals.Notions as Notions
open import SPT.Cubical.TypeTopology.Ordinals.Equivalence using
  (_≃ₒ_; eqtoidₒ; order-equivs-are-simulations)

open import SPT.Cubical.OrdinalGeometry.Cubical.TypeTopology.Bridge using
  (toOrdinal; smallToOrdinal; path→＝; ＝→path)
open import SPT.Cubical.OrdinalGeometry.Cubical.TypeTopology.Simulation
  using (woset; section)
open import SPT.Cubical.OrdinalGeometry.Cubical.TypeTopology.FunExt using
  (funext)
open import SPT.Cubical.OrdinalGeometry.Cubical.TypeTopology.Univalence
  using (univalence)
open import SPT.Cubical.TypeTopology.Ordinals.OrdinalOfOrdinals univalence
  using (OO; _⊲_; _↓_; ⊲-is-prop-valued; simulations-preserve-↓)

open import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Ordinals using
  (Ord; raise; raise-equivalence; lowerset)
open import SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Base using (ω₁)
open import SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Cut using
  (MerelyPresented)
import SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Small as Small

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- The bridge is an equivalence of types

-- toOrdinal (woset β) has the carrier and the relation of β, and being a
-- well-order is a proposition.
retraction : (β : Ordinal ℓ) → toOrdinal (woset β) Cubical.≡ β
retraction β i =
  Sigma._,_ (pr₁ β)
    (Sigma._,_ (pr₁ (pr₂ β))
      (＝→path
        (Notions.being-well-order-is-prop (pr₁ (pr₂ β)) funext
          (pr₂ (pr₂ (toOrdinal (woset β)))) (pr₂ (pr₂ β)))
        i))

-- Mathematical shape: Woset(ℓ, ℓ) ≃ Ordinal ℓ.
ordinals : Woset.Woset ℓ ℓ Equiv.≃ Ordinal ℓ
ordinals = Isomorphism.isoToEquiv
  (Isomorphism.iso toOrdinal woset retraction section)

------------------------------------------------------------------------
-- Segments and the two orders

-- The principal segment of β at b is TypeTopology's segment of its
-- ordinal: the same points and order, as pairs of the other library.
segment : (β : Woset.Woset ℓ ℓ) (b : Cubical.fst β)
  → Identity._＝_ (toOrdinal (Simulation._↓_ β b)) (toOrdinal β ↓ b)
segment {ℓ} β b =
  eqtoidₒ (univalence ℓ) (λ {𝓤} {𝓥} → funext 𝓤 𝓥) _ _
    (Sigma._,_ forth
      (Sigma._,_ (λ x y r → r)
        (Sigma._,_
          (qinvs-are-equivs forth
            (Sigma._,_ back
              (Sigma._,_ (λ x → Identity.refl) (λ y → Identity.refl))))
          (λ x y r → r))))
  where
    forth : Cubical.fst (Simulation._↓_ β b) → pr₁ (toOrdinal β ↓ b)
    forth (Cubical._,_ x p) = Sigma._,_ x p

    back : pr₁ (toOrdinal β ↓ b) → Cubical.fst (Simulation._↓_ β b)
    back (Sigma._,_ x p) = Cubical._,_ x p

-- Mathematical shape: α ≺ β → ⌜α⌝ ⊲ ⌜β⌝, writing ⌜−⌝ for toOrdinal.
preserves : (α β : Woset.Woset ℓ ℓ)
  → α Simulation.≺ β → toOrdinal α ⊲ toOrdinal β
preserves α β (Cubical._,_ b e) =
  Sigma._,_ b
    (path→＝
      (Cubical.sym
        (Cubical.cong toOrdinal
          (Equiv.equivFun (Woset.WosetPath (Simulation._↓_ β b) α) e))
        Cubical.∙ ＝→path (segment β b)))

-- Mathematical shape: ⌜α⌝ ⊲ ⌜β⌝ → α ≺ β.
reflects : (α β : Woset.Woset ℓ ℓ)
  → toOrdinal α ⊲ toOrdinal β → α Simulation.≺ β
reflects α β (Sigma._,_ b p) =
  Cubical._,_ b
    (Equiv.invEq (Woset.WosetPath (Simulation._↓_ β b) α)
      (Cubical.sym (section (Simulation._↓_ β b))
        Cubical.∙ Cubical.cong woset
          (＝→path (segment β b) Cubical.∙ Cubical.sym (＝→path p))
        Cubical.∙ section α))

------------------------------------------------------------------------
-- Cubical's ordinal of ordinals is TypeTopology's OO

-- Mathematical shape: Ord(ℓ) ≃ₒ OO ℓ, by toOrdinal.
equivalence : smallToOrdinal (Ord ℓ) ≃ₒ OO ℓ
equivalence =
  Sigma._,_ toOrdinal
    (Sigma._,_ (λ α β r → preserves α β (lower r))
      (Sigma._,_
        (qinvs-are-equivs toOrdinal
          (Sigma._,_ woset
            (Sigma._,_ (λ α → path→＝ (section α))
              (λ β → path→＝ (retraction β)))))
        (λ γ δ r → lift
          (reflects (woset γ) (woset δ)
            (Cubical.subst2 _⊲_ (Cubical.sym (retraction γ))
              (Cubical.sym (retraction δ)) r)))))

-- Mathematical shape: Ord(ℓ) = OO ℓ, as TypeTopology ordinals.
identity : Identity._＝_ (smallToOrdinal (Ord ℓ)) (OO ℓ)
identity {ℓ} =
  eqtoidₒ (univalence (lsuc ℓ)) (λ {𝓤} {𝓥} → funext 𝓤 𝓥)
    (smallToOrdinal (Ord ℓ)) (OO ℓ) equivalence

------------------------------------------------------------------------
-- Segments of the ordinal of ordinals

-- Mathematical shape: Ord(ℓ) ↓ W = OO ℓ ↓ ⌜W⌝, since equivalence is a
-- simulation.
segment-OO : (W : Woset.Woset ℓ ℓ)
  → Identity._＝_ (smallToOrdinal (Ord ℓ) ↓ W) (OO ℓ ↓ toOrdinal W)
segment-OO {ℓ} W =
  simulations-preserve-↓ (smallToOrdinal (Ord ℓ)) (OO ℓ)
    (Sigma._,_ toOrdinal
      (order-equivs-are-simulations (smallToOrdinal (Ord ℓ)) (OO ℓ)
        toOrdinal (pr₂ equivalence)))
    W

-- Mathematical shape: γ ⊲ ⌜K⌝ ≃ woset γ ≺ K, for γ in OO ℓ and K in
-- Ord(ℓ).
order : (γ : Ordinal ℓ) (K : Woset.Woset ℓ ℓ)
  → (γ ⊲ toOrdinal K) Equiv.≃ (woset γ Simulation.≺ K)
order γ K =
  Equiv.propBiimpl→Equiv
    (λ x y → ＝→path (⊲-is-prop-valued γ (toOrdinal K) x y))
    (Simulation.isPropValued≺ (woset γ) K)
    (λ r → reflects (woset γ) K
      (Cubical.subst (_⊲ toOrdinal K) (Cubical.sym (retraction γ)) r))
    (λ s → Cubical.subst (_⊲ toOrdinal K) (retraction γ)
      (preserves (woset γ) K s))

------------------------------------------------------------------------
-- ω₁ in TypeTopology's OO

private
  -- segment for well-orders with a large carrier, whose relation
  -- smallToOrdinal lifts.
  large-segment : (B : Woset.Woset (lsuc ℓ) ℓ) (b : Cubical.fst B)
    → Identity._＝_ (smallToOrdinal (Simulation._↓_ B b))
        (smallToOrdinal B ↓ b)
  large-segment {ℓ} B b =
    eqtoidₒ (univalence (lsuc ℓ)) (λ {𝓤} {𝓥} → funext 𝓤 𝓥) _ _
      (Sigma._,_ forth
        (Sigma._,_ (λ x y r → r)
          (Sigma._,_
            (qinvs-are-equivs forth
              (Sigma._,_ back
                (Sigma._,_ (λ x → Identity.refl) (λ y → Identity.refl))))
            (λ x y r → r))))
    where
      forth : Cubical.fst (Simulation._↓_ B b) → pr₁ (smallToOrdinal B ↓ b)
      forth (Cubical._,_ x p) = Sigma._,_ x (lift p)

      back : pr₁ (smallToOrdinal B ↓ b) → Cubical.fst (Simulation._↓_ B b)
      back (Sigma._,_ x p) = Cubical._,_ x (lower p)

  -- Mathematical shape: B ↓ b ≃ A → ⌜A⌝ = ⌜B⌝ ↓ b, for well-orders with a
  -- large carrier.
  large-identity : (A B : Woset.Woset (lsuc ℓ) ℓ) (b : Cubical.fst B)
    → Woset.WosetEquiv (Simulation._↓_ B b) A
    → Identity._＝_ (smallToOrdinal A) (smallToOrdinal B ↓ b)
  large-identity A B b e =
    path→＝
      (Cubical.sym
        (Cubical.cong smallToOrdinal
          (Equiv.equivFun (Woset.WosetPath (Simulation._↓_ B b) A) e))
        Cubical.∙ ＝→path (large-segment B b))

  -- Mathematical shape: Ord(ℓ) ↓ Ω′ ≃ ω₁(ℓ), with Ω′ = raise ℓ ℓ Ω: the
  -- equivalence of Small.principal, from public equivalences.
  segment-Ω : (ℓ : Level)
    → Woset.WosetEquiv (Simulation._↓_ (Ord ℓ) (raise ℓ ℓ Small.Ω)) (ω₁ ℓ)
  segment-Ω ℓ =
    Woset.compWosetEquiv
      {M = Simulation._↓_ (Ord ℓ) (raise ℓ ℓ Small.Ω)}
      {N = raise ℓ ℓ Small.Ω} {O = ω₁ ℓ}
      (Woset.invWosetEquiv {M = raise ℓ ℓ Small.Ω}
        {N = Simulation._↓_ (Ord ℓ) (raise ℓ ℓ Small.Ω)}
        (lowerset (raise ℓ ℓ Small.Ω)))
      (Woset.compWosetEquiv {M = raise ℓ ℓ Small.Ω} {N = Small.Ω}
        {O = ω₁ ℓ}
        (Woset.invWosetEquiv {M = Small.Ω} {N = raise ℓ ℓ Small.Ω}
          (raise-equivalence ℓ ℓ Small.Ω))
        (Woset.invWosetEquiv {M = ω₁ ℓ} {N = Small.Ω} (Small.small ℓ)))

-- Mathematical shape: ω₁(ℓ) = OO ℓ ↓ ⌜Ω′⌝, where Ω′ is Ω raised to level
-- ℓ.  It composes two lemmas whose types match it syntactically, so that
-- checking it does not evaluate Ω.
omega-one : Identity._＝_ (smallToOrdinal (ω₁ ℓ))
  (OO ℓ ↓ toOrdinal (raise ℓ ℓ Small.Ω))
omega-one {ℓ} =
  path→＝
    (＝→path
      (large-identity (ω₁ ℓ) (Ord ℓ) (raise ℓ ℓ Small.Ω) (segment-Ω ℓ))
      Cubical.∙ ＝→path (segment-OO (raise ℓ ℓ Small.Ω)))

-- Mathematical shape: ω₁(ℓ) ⊲ OO ℓ, in OO(ℓ + 1).
principal : smallToOrdinal (ω₁ ℓ) ⊲ OO ℓ
principal {ℓ} = Sigma._,_ (toOrdinal (raise ℓ ℓ Small.Ω)) omega-one

-- Mathematical shape: γ ⊲ ⌜Ω′⌝ ≃ MerelyPresented(woset γ), for γ in OO ℓ.
below : (γ : Ordinal ℓ)
  → (γ ⊲ toOrdinal (raise ℓ ℓ Small.Ω)) Equiv.≃ MerelyPresented (woset γ)
below {ℓ} γ =
  Equiv.compEquiv (order γ (raise ℓ ℓ Small.Ω)) (Small.below (woset γ))
