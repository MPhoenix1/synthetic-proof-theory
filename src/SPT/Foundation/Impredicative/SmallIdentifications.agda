{-# OPTIONS --safe --without-K #-}

module SPT.Foundation.Impredicative.SmallIdentifications where

-- Small identifications: every identification of two types of level ℓ + 1
-- is small at ℓ (`Small-Identifications`). No impredicativity at ℓ is
-- assumed, yet under univalence at ℓ + 1 it gives propositional resizing, a
-- proposition P being equivalent to P ＝ 1
-- (`small-identifications-give-resizing`), and a type represented
-- faithfully by automorphisms of a set of level ℓ + 1 is small
-- (`faithfully-represented-types-are-small`). With function extensionality
-- at ℓ and ℓ + 1 and propositional extensionality at ℓ, every ¬¬-separated
-- set of level ℓ + 1 is so represented, so small
-- (`separated-sets-are-small`): toggling the ¬¬-stable proposition beside
-- each x by x ＝ a is an automorphism of A × Ω¬¬ that determines a. So a
-- large ¬¬-separated set refutes small identifications; that they give one
-- is the specification `Separated-Largeness`, inhabited in
-- Impredicative.BuraliForti.

open import SPT.Base
open import SPT.Foundation.Embeddings using
  (is-embedding; left-cancellable-maps-into-sets-are-embeddings)
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.Fibers using (fiber)
open import SPT.Foundation.Fibers.Structure using (domain-fiber-isomorphism)
open import SPT.Foundation.Impredicative.PropositionalResizing using
  (Propositional-Resizing; weakly-presented-propositions-are-small)
open import SPT.Foundation.Isomorphisms using
  (_≅_; forward; backward; forward-backward; ≅-sym; ≅-trans; Σ-cong)
open import SPT.Foundation.Isomorphisms.Sets using (isomorphic-to-a-set)
open import SPT.Foundation.Modalities using
  (Stable-Proposition; double-negation-modality)
open import SPT.Foundation.Modalities.Biconditional using
  ( truth; biconditional; toggled-truth; truth-toggled
  ; toggling-is-an-involution; stable-propositions-form-a-set)
open import SPT.Foundation.Propositions using (is-proposition; is-set)
open import SPT.Foundation.Propositions.Closure using
  (isomorphic-to-a-proposition)
open import SPT.Foundation.Propositions.Extensionality using
  (Propositional-Extensionality)
open import SPT.Foundation.Sets using (sums-of-sets-are-sets)
open import SPT.Foundation.Size using (is-small)
open import SPT.Foundation.Univalence using
  ( is-univalent; is-univalent-at; isotoid; transport-isotoid
  ; equivalence-to-isomorphism; isomorphism-to-equivalence)
open import SPT.Foundation.Univalence.Sets using
  (identifications-with-a-set-form-a-set)

------------------------------------------------------------------------
-- Small identifications

-- Mathematical shape: Π (X Y : Set (ℓ + 1)). is-small ℓ (X ＝ Y).
Small-Identifications : (ℓ : Level) → Set (lsuc (lsuc ℓ))
Small-Identifications ℓ = (X Y : Set (lsuc ℓ)) → is-small ℓ (X ＝ Y)

------------------------------------------------------------------------
-- Propositional resizing

-- An inhabited proposition is identified with the unit type, and a type
-- identified with the unit type has a point. So a proposition has maps both
-- ways with the small presentation of its identifications with the unit
-- type, which makes it small.

module _ {ℓ : Level} (P : Set (lsuc ℓ)) where

  point-from-identification-with-unit : P ＝ Lift (lsuc ℓ) 𝟙 → P
  point-from-identification-with-unit e =
    transport (λ X → X) (e ⁻¹) (lift ⋆)

  identification-with-unit : is-univalent-at P (Lift (lsuc ℓ) 𝟙) →
    is-proposition P → P → P ＝ Lift (lsuc ℓ) 𝟙
  identification-with-unit u h p = isotoid u (record
    { forward = λ x → lift ⋆
    ; backward = λ y → p
    ; backward-forward = λ x → h p x
    ; forward-backward = λ y → refl
    })

module _ {ℓ : Level} where

  -- Mathematical shape: P ⇔ (P ＝ 1) for a proposition P.
  small-identifications-give-resizing : is-univalent (lsuc ℓ) →
    Small-Identifications ℓ → Propositional-Resizing ℓ
  small-identifications-give-resizing u s P h =
    let E = equivalence-to-isomorphism (pr₂ (s P (Lift (lsuc ℓ) 𝟙)))
    in weakly-presented-propositions-are-small h
         ( pr₁ (s P (Lift (lsuc ℓ) 𝟙))
         , (λ k → point-from-identification-with-unit P (forward E k))
         , (λ p → backward E
             (identification-with-unit P (u P (Lift (lsuc ℓ) 𝟙)) h p)))

------------------------------------------------------------------------
-- Faithful representations by automorphisms

-- A map from A to the automorphisms of a set B of level ℓ + 1 is faithful
-- when automorphisms that agree at every point come from one point. Read
-- through univalence in the small presentation of B ＝ B, which is a set
-- since B is, it is left-cancellable, hence an embedding, and A is the sum
-- of its fibers, propositions of level ℓ + 1 that resizing makes small.

module _ {ℓ : Level}
  (extensionality₁ : (X : Set (lsuc ℓ)) (Y : X → Set (lsuc ℓ)) → FunExt X Y)
  (u₁ : is-univalent (lsuc ℓ)) (s : Small-Identifications ℓ)
  (B : Set (lsuc ℓ)) (B-is-a-set : is-set B) {A : Set (lsuc ℓ)}
  (τ : A → B ≅ B)
  (faithful : (a b : A) →
    ((y : B) → forward (τ a) y ＝ forward (τ b) y) → a ＝ b)
  where

  small-representation : A → pr₁ (s B B)
  small-representation a =
    backward (equivalence-to-isomorphism (pr₂ (s B B)))
      (isotoid (u₁ B B) (τ a))

  small-representation-is-left-cancellable : (a b : A) →
    small-representation a ＝ small-representation b → a ＝ b
  small-representation-is-left-cancellable a b q =
    let E = equivalence-to-isomorphism (pr₂ (s B B))
        p = forward-backward E (isotoid (u₁ B B) (τ a)) ⁻¹
            ∙ ap (forward E) q
            ∙ forward-backward E (isotoid (u₁ B B) (τ b))
    in faithful a b
         (λ y →
           transport-isotoid (u₁ B B) (τ a) y ⁻¹
           ∙ ap (λ e → transport (λ X → X) e y) p
           ∙ transport-isotoid (u₁ B B) (τ b) y)

  small-identifications-of-a-set-form-a-set : is-set (pr₁ (s B B))
  small-identifications-of-a-set-form-a-set =
    isomorphic-to-a-set (≅-sym (equivalence-to-isomorphism (pr₂ (s B B))))
      (identifications-with-a-set-form-a-set extensionality₁ B B B-is-a-set
        (u₁ B B))

  small-representation-is-an-embedding : is-embedding small-representation
  small-representation-is-an-embedding =
    left-cancellable-maps-into-sets-are-embeddings
      small-identifications-of-a-set-form-a-set small-representation
      small-representation-is-left-cancellable

  -- Mathematical shape: A ≅ Σ (k : K). fiber t k, each fiber resized.
  faithfully-represented-types-are-small : is-small ℓ A
  faithfully-represented-types-are-small =
    let R = small-identifications-give-resizing u₁ s
    in Σ (pr₁ (s B B))
         (λ k → pr₁
           (R (fiber small-representation k)
             (small-representation-is-an-embedding k)))
       , isomorphism-to-equivalence
           (≅-trans
             (Σ-cong (λ k →
               equivalence-to-isomorphism
                 (pr₂ (R (fiber small-representation k)
                   (small-representation-is-an-embedding k)))))
             (≅-sym (domain-fiber-isomorphism small-representation)))

------------------------------------------------------------------------
-- Separated sets

-- A set whose identifications are ¬¬-stable, and one of level ℓ + 1 that is
-- not small at ℓ.

record Separated-Set (ℓ : Level) : Set (lsuc ℓ) where
  field
    points : Set ℓ
    points-form-a-set : is-set points
    points-are-separated : (x y : points) → ¬ ¬ (x ＝ y) → x ＝ y

record Large-Separated-Set (ℓ : Level) : Set (lsuc (lsuc ℓ)) where
  field
    separated-set : Separated-Set (lsuc ℓ)
    not-small : is-small ℓ (Separated-Set.points separated-set) → 𝟘

------------------------------------------------------------------------
-- Identifications as ¬¬-stable propositions

-- Under resizing, x ＝ a has a small presentation, ¬¬-stable since the set
-- is separated. Later definitions use it only through its maps both ways
-- with x ＝ a, so it is sealed.

module _ {ℓ : Level} (dn : (X : Set ℓ) → FunExt (¬ X) (λ _ → 𝟘))
  (resize : Propositional-Resizing ℓ) (S : Separated-Set (lsuc ℓ)) where

  open Separated-Set S

  opaque
    identity-proposition : points → points →
      Stable-Proposition (double-negation-modality dn)
    identity-proposition x a =
      let E = equivalence-to-isomorphism
                (pr₂ (resize (x ＝ a) (points-form-a-set x a)))
      in record
        { carrier = pr₁ (resize (x ＝ a) (points-form-a-set x a))
        ; carrier-is-proposition =
            isomorphic-to-a-proposition (≅-sym E) (points-form-a-set x a)
        ; carrier-is-stable = λ k →
            backward E
              (points-are-separated x a (λ n → k (λ c → n (forward E c))))
        }

    identity-proposition-identifies : (x a : points) →
      Stable-Proposition.carrier (identity-proposition x a) → x ＝ a
    identity-proposition-identifies x a =
      forward
        (equivalence-to-isomorphism
          (pr₂ (resize (x ＝ a) (points-form-a-set x a))))

    identity-proposition-holds : (x a : points) → x ＝ a →
      Stable-Proposition.carrier (identity-proposition x a)
    identity-proposition-holds x a =
      backward
        (equivalence-to-isomorphism
          (pr₂ (resize (x ＝ a) (points-form-a-set x a))))

------------------------------------------------------------------------
-- Toggling at a point

-- A point a of the set toggles the stable proposition beside each x by
-- x ＝ a. Toggling twice is the identity, so each toggle is an automorphism
-- of the pairs.

module _ {ℓ : Level} (dn : (X : Set ℓ) → FunExt (¬ X) (λ _ → 𝟘))
  (extensionality : (X : Set ℓ) (Y : X → Set ℓ) → FunExt X Y)
  (pe : Propositional-Extensionality ℓ) (resize : Propositional-Resizing ℓ)
  (S : Separated-Set (lsuc ℓ)) where

  open Separated-Set S

  -- Mathematical shape: (x , P) ↦ (x , (x ＝ a) ⇔ P).
  toggle-at : points →
    points × Stable-Proposition (double-negation-modality dn) →
    points × Stable-Proposition (double-negation-modality dn)
  toggle-at a w =
    pr₁ w ,
    biconditional dn extensionality
      (identity-proposition dn resize S (pr₁ w) a) (pr₂ w)

  toggling-at-twice : (a : points)
    (w : points × Stable-Proposition (double-negation-modality dn)) →
    toggle-at a (toggle-at a w) ＝ w
  toggling-at-twice a w =
    ap (λ P → pr₁ w , P)
      (toggling-is-an-involution dn extensionality pe
        (identity-proposition dn resize S (pr₁ w) a) (pr₂ w))

  toggle : points →
    (points × Stable-Proposition (double-negation-modality dn)) ≅
    (points × Stable-Proposition (double-negation-modality dn))
  toggle a = record
    { forward = toggle-at a
    ; backward = toggle-at a
    ; backward-forward = toggling-at-twice a
    ; forward-backward = toggling-at-twice a
    }

------------------------------------------------------------------------
-- Separated sets are small

-- The toggles represent a separated set faithfully: at (a , ⊤) the toggle at
-- a gives (a , (a ＝ a) ⇔ ⊤), so when the toggles at a and b agree there,
-- (a ＝ b) ⇔ ⊤ holds, and a ＝ b.

module _ {ℓ : Level} (dn : (X : Set ℓ) → FunExt (¬ X) (λ _ → 𝟘))
  (extensionality₀ : (X : Set ℓ) (Y : X → Set ℓ) → FunExt X Y)
  (extensionality₁ : (X : Set (lsuc ℓ)) (Y : X → Set (lsuc ℓ)) → FunExt X Y)
  (pe₀ : Propositional-Extensionality ℓ) (u₁ : is-univalent (lsuc ℓ))
  (s : Small-Identifications ℓ) (S : Separated-Set (lsuc ℓ)) where

  open Separated-Set S

  toggles-determine-their-point : (a b : points) →
    ((w : points × Stable-Proposition (double-negation-modality dn)) →
      toggle-at dn extensionality₀ pe₀
        (small-identifications-give-resizing u₁ s) S a w
      ＝ toggle-at dn extensionality₀ pe₀
          (small-identifications-give-resizing u₁ s) S b w) →
    a ＝ b
  toggles-determine-their-point a b agree =
    let R = small-identifications-give-resizing u₁ s
    in identity-proposition-identifies dn R S a b
         (toggled-truth dn extensionality₀ (identity-proposition dn R S a b)
           (transport (λ X → X)
             (ap (λ w → Stable-Proposition.carrier (pr₂ w))
               (agree (a , truth dn)))
             (truth-toggled dn extensionality₀ (identity-proposition dn R S a a)
               (identity-proposition-holds dn R S a a refl))))

  separated-sets-are-small : is-small ℓ points
  separated-sets-are-small =
    faithfully-represented-types-are-small extensionality₁ u₁ s
      (points × Stable-Proposition (double-negation-modality dn))
      (sums-of-sets-are-sets points-form-a-set
        (λ _ → stable-propositions-form-a-set dn extensionality₀ pe₀))
      (toggle dn extensionality₀ pe₀
        (small-identifications-give-resizing u₁ s) S)
      toggles-determine-their-point

------------------------------------------------------------------------
-- Large separated sets

-- A large separated set refutes small identifications. That small
-- identifications give one, which refutes them outright, is the
-- specification `Separated-Largeness`. Excluded middle gives one, the
-- univalent iterative sets (SPT.Universes.IterativeSet.Univalent); with no
-- excluded middle, the order types of stably well-founded orders are one
-- (`separated-largeness` of SPT.Foundation.Impredicative.BuraliForti).

-- Specification: under propositional extensionality at ℓ and univalence at
-- ℓ + 1, small identifications give a large separated set.
Separated-Largeness : (ℓ : Level) → Set (lsuc (lsuc ℓ))
Separated-Largeness ℓ =
  Propositional-Extensionality ℓ → is-univalent (lsuc ℓ) →
  Small-Identifications ℓ → Large-Separated-Set ℓ

module _ {ℓ : Level} (dn : (X : Set ℓ) → FunExt (¬ X) (λ _ → 𝟘))
  (extensionality₀ : (X : Set ℓ) (Y : X → Set ℓ) → FunExt X Y)
  (extensionality₁ : (X : Set (lsuc ℓ)) (Y : X → Set (lsuc ℓ)) → FunExt X Y)
  (pe₀ : Propositional-Extensionality ℓ) (u₁ : is-univalent (lsuc ℓ)) where

  large-separated-sets-refute-small-identifications :
    Large-Separated-Set ℓ → Small-Identifications ℓ → 𝟘
  large-separated-sets-refute-small-identifications L s =
    Large-Separated-Set.not-small L
      (separated-sets-are-small dn extensionality₀ extensionality₁ pe₀ u₁ s
        (Large-Separated-Set.separated-set L))

  separated-largeness-refutes-small-identifications :
    Separated-Largeness ℓ → Small-Identifications ℓ → 𝟘
  separated-largeness-refutes-small-identifications largeness s =
    large-separated-sets-refute-small-identifications (largeness pe₀ u₁ s) s
