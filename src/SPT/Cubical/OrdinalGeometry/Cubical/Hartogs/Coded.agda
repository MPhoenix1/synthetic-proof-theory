{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.Hartogs.Coded where

-- Well-orders coded by Booleans on subsets of a type T: a subset
-- s : T → 𝟐 and a relation r : T → T → 𝟐 that well-orders
-- Σ t. s t = true.  Coded T lies in the universe of T, so an operator on
-- families of types can range over it, while the well-orders of level ℓ
-- form a type one level up.  Under excluded middle every well-order whose
-- carrier embeds into T is equivalent to a coded one (encode).  The laws
-- of a well-order carry along an equivalence of carriers that matches the
-- relations (transport-laws).

open import Agda.Primitive using (Level)
open import Level using (Lift; lift; lower)

import Cubical.Data.Bool as Bool
open Bool using (Bool; true; false)
import Cubical.Data.Sigma.Properties as SigmaProperties
import Cubical.Foundations.Equiv as Equiv
import Cubical.Foundations.HLevels as HLevels
import Cubical.Foundations.Isomorphism as Isomorphism
import Cubical.Foundations.Prelude as Cubical
import Cubical.Foundations.Univalence as Univalence
import Cubical.Functions.Embedding as Embedding
import Cubical.Relation.Binary.Order.Woset.Base as Woset

open import SPT.Cubical.OrdinalGeometry.Cubical.Hartogs.Countability using
  (ExcludedMiddle)
open import SPT.Cubical.OrdinalGeometry.Cubical.Hartogs.PowerSet using
  (decide; decide-holds; holds-decide)

private
  variable
    ℓ ℓ′ : Level

------------------------------------------------------------------------
-- Transport of the laws

-- Mathematical shape: φ : A ≃ B, R a b ≃ R′ (φ a) (φ b), IsWoset R
-- ⊢ IsWoset R′, along the path of relations over ua φ.
transport-laws : {A B : Set ℓ} (φ : A Equiv.≃ B)
  (R : A → A → Set ℓ′) (R′ : B → B → Set ℓ′)
  → ((a b : A) → R a b Equiv.≃ R′ (Equiv.equivFun φ a) (Equiv.equivFun φ b))
  → Woset.IsWoset R → Woset.IsWoset R′
transport-laws {ℓ′ = ℓ′} φ R R′ e =
  Cubical.transport (λ i → Woset.IsWoset (relation i))
  where
    relation : Cubical.PathP
      (λ i → Univalence.ua φ i → Univalence.ua φ i → Set ℓ′) R R′
    relation =
      Univalence.ua→ {e = φ}
        {B = λ i → Univalence.ua φ i → Set ℓ′}
        λ a →
          Univalence.ua→ {e = φ} {B = λ _ → Set ℓ′}
            λ b → Univalence.ua (e a b)

------------------------------------------------------------------------
-- Coded well-orders

-- The points of a decided subset.
Support : {T : Set ℓ} → (T → Bool) → Set ℓ
Support {T = T} s = Cubical.Σ T (λ t → s t Cubical.≡ true)

-- The relation coded by r on that subset.
Coded-order : {T : Set ℓ} (s : T → Bool) (r : T → T → Bool)
  → Support s → Support s → Set ℓ
Coded-order {ℓ} s r x y =
  Lift ℓ (r (Cubical.fst x) (Cubical.fst y) Cubical.≡ true)

-- Mathematical shape: Coded T = Σ s r. IsWoset (coded order on s).
Coded : Set ℓ → Set ℓ
Coded T =
  Cubical.Σ (T → Bool) λ s →
    Cubical.Σ (T → T → Bool) λ r → Woset.IsWoset (Coded-order s r)

woset-of : {T : Set ℓ} → Coded T → Woset.Woset ℓ ℓ
woset-of (Cubical._,_ s (Cubical._,_ r laws)) =
  Support s Cubical., Woset.wosetstr (Coded-order s r) laws

------------------------------------------------------------------------
-- Encoding, under excluded middle

module _ (lem : ExcludedMiddle ℓ) (α : Woset.Woset ℓ ℓ) {T : Set ℓ}
  (e : Cubical.fst α Embedding.↪ T) where

  private
    _<_ = Woset.WosetStr._≺_ (Cubical.snd α)
    order-laws = Woset.WosetStr.isWoset (Cubical.snd α)
    f = Cubical.fst e

    fiber-prop : (t : T) → Cubical.isProp (Equiv.fiber f t)
    fiber-prop = Embedding.isEmbedding→hasPropFibers (Cubical.snd e)

    injective : {a b : Cubical.fst α} → f a Cubical.≡ f b → a Cubical.≡ b
    injective {a} {b} = Embedding.isEmbedding→Inj (Cubical.snd e) a b

    Below : T → T → Set ℓ
    Below t t′ =
      Cubical.Σ (Equiv.fiber f t) λ u →
        Cubical.Σ (Equiv.fiber f t′) λ v → Cubical.fst u < Cubical.fst v

    below-prop : (t t′ : T) → Cubical.isProp (Below t t′)
    below-prop t t′ =
      HLevels.isPropΣ (fiber-prop t) λ u →
        HLevels.isPropΣ (fiber-prop t′) λ v →
          Woset.IsWoset.is-prop-valued order-laws
            (Cubical.fst u) (Cubical.fst v)

    -- The image of e and the order on it, decided.
    s : T → Bool
    s t = decide (lem (Equiv.fiber f t) (fiber-prop t))

    r : T → T → Bool
    r t t′ = decide (lem (Below t t′) (below-prop t t′))

    into : Cubical.fst α → Support s
    into a =
      f a Cubical.,
      holds-decide (lem (Equiv.fiber f (f a)) (fiber-prop (f a)))
        (a Cubical., Cubical.refl)

    back : Support s → Cubical.fst α
    back x =
      Cubical.fst
        (decide-holds
          (lem (Equiv.fiber f (Cubical.fst x)) (fiber-prop (Cubical.fst x)))
          (Cubical.snd x))

    back-into : (a : Cubical.fst α) → back (into a) Cubical.≡ a
    back-into a =
      injective
        (Cubical.snd
          (decide-holds (lem (Equiv.fiber f (f a)) (fiber-prop (f a)))
            (Cubical.snd (into a))))

    into-back : (x : Support s) → into (back x) Cubical.≡ x
    into-back x =
      SigmaProperties.Σ≡Prop (λ _ → Bool.isSetBool _ _)
        (Cubical.snd
          (decide-holds
            (lem (Equiv.fiber f (Cubical.fst x)) (fiber-prop (Cubical.fst x)))
            (Cubical.snd x)))

    carrier : Cubical.fst α Equiv.≃ Support s
    carrier =
      Isomorphism.isoToEquiv
        (Isomorphism.iso into back into-back back-into)

    relation : (a b : Cubical.fst α)
      → (a < b) Equiv.≃ Coded-order s r (into a) (into b)
    relation a b =
      Equiv.propBiimpl→Equiv
        (Woset.IsWoset.is-prop-valued order-laws a b)
        (λ (lift p) (lift q) → Cubical.cong lift (Bool.isSetBool _ _ p q))
        (λ a<b →
          lift
            (holds-decide (lem (Below (f a) (f b)) (below-prop (f a) (f b)))
              ((a Cubical., Cubical.refl) Cubical.,
                ((b Cubical., Cubical.refl) Cubical., a<b))))
        (λ (lift coded) →
          let found =
                decide-holds
                  (lem (Below (f a) (f b)) (below-prop (f a) (f b))) coded
              u = Cubical.fst found
              v = Cubical.fst (Cubical.snd found)
          in Cubical.subst2 _<_
               (injective (Cubical.snd u)) (injective (Cubical.snd v))
               (Cubical.snd (Cubical.snd found)))

  -- Mathematical shape: Σ (W : Coded T). α ≃ woset-of W.
  encode : Cubical.Σ (Coded T) (λ W → Woset.WosetEquiv α (woset-of W))
  encode =
    (s Cubical., (r Cubical.,
      transport-laws carrier _<_ (Coded-order s r) relation order-laws))
    Cubical., (carrier Cubical., Woset.iswosetequiv relation)
