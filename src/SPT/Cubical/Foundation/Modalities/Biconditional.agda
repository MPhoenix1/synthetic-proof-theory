{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.Modalities.Biconditional where

-- The ¬¬-stable propositions of one level under the biconditional. The
-- biconditional of two of them is one (`biconditional`), and toggling by Q,
-- P ↦ (Q ⇔ P), undoes itself: Q ⇔ (Q ⇔ P) has maps both ways with P
-- (`toggled-twice`, `untoggled`), and Q ⇔ ⊤ with Q (`toggled-truth`,
-- `truth-toggled`). Under propositional extensionality at the level,
-- ¬¬-stable propositions with maps both ways are identified
-- (`stable-propositions-are-identified`),
-- so toggling is an involution (`toggling-is-an-involution`) and the
-- ¬¬-stable propositions form a set (`stable-propositions-form-a-set`).

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Extensionality
  using (FunExt; Π-is-proposition)
open import SPT.Cubical.Foundation.Modalities using
  (Stable-Proposition; double-negation-modality)
open import SPT.Cubical.Foundation.Propositions using
  (is-proposition; is-set; Σ-is-proposition)
open import SPT.Cubical.Foundation.Sets
  using (being-a-proposition-is-a-proposition)
open import SPT.Cubical.Foundation.Propositions.Extensionality using
  (Propositional-Extensionality)
open import SPT.Cubical.Foundation.Sets.Uniqueness using (identifications-from)

------------------------------------------------------------------------
-- The true proposition

module _ {ℓ : Level} (dn : (X : Set ℓ) → FunExt (¬ X) (λ _ → 𝟘)) where

  -- The unit type of the level.
  truth : Stable-Proposition (double-negation-modality dn)
  truth = record
    { carrier = Lift ℓ 𝟙
    ; carrier-is-proposition = λ x y → refl
    ; carrier-is-stable = λ k → lift ⋆
    }

------------------------------------------------------------------------
-- The biconditional and toggling

-- Q ⇔ P is a proposition under extensionality at the level, and stable,
-- each direction being a function into a stable proposition. From
-- Q ⇔ (Q ⇔ P), a refutation of P refutes Q, so Q ⇔ P holds, hence Q, a
-- contradiction; P is stable, so P holds.

module _ {ℓ : Level} (dn : (X : Set ℓ) → FunExt (¬ X) (λ _ → 𝟘))
  (extensionality : (X : Set ℓ) (Y : X → Set ℓ) → FunExt X Y) where

  biconditional : Stable-Proposition (double-negation-modality dn) →
    Stable-Proposition (double-negation-modality dn) →
    Stable-Proposition (double-negation-modality dn)
  biconditional Q P = record
    { carrier =
        (Stable-Proposition.carrier Q → Stable-Proposition.carrier P) ×
        (Stable-Proposition.carrier P → Stable-Proposition.carrier Q)
    ; carrier-is-proposition = Σ-is-proposition
        (Π-is-proposition
          (extensionality (Stable-Proposition.carrier Q)
            (λ _ → Stable-Proposition.carrier P))
          (λ _ → Stable-Proposition.carrier-is-proposition P))
        (λ _ → Π-is-proposition
          (extensionality (Stable-Proposition.carrier P)
            (λ _ → Stable-Proposition.carrier Q))
          (λ _ → Stable-Proposition.carrier-is-proposition Q))
    ; carrier-is-stable = λ k →
        (λ q → Stable-Proposition.carrier-is-stable P
          (λ n → k (λ w → n (pr₁ w q)))) ,
        (λ p → Stable-Proposition.carrier-is-stable Q
          (λ n → k (λ w → n (pr₂ w p))))
    }

  toggled-twice : (Q P : Stable-Proposition (double-negation-modality dn)) →
    Stable-Proposition.carrier (biconditional Q (biconditional Q P)) →
    Stable-Proposition.carrier P
  toggled-twice Q P w = Stable-Proposition.carrier-is-stable P
    (λ n →
      let refuted : ¬ Stable-Proposition.carrier Q
          refuted q = n (pr₁ (pr₁ w q) q)
      in refuted
           (pr₂ w ((λ q → 𝟘-elim (refuted q)) , (λ p → 𝟘-elim (n p)))))

  untoggled : (Q P : Stable-Proposition (double-negation-modality dn)) →
    Stable-Proposition.carrier P →
    Stable-Proposition.carrier (biconditional Q (biconditional Q P))
  untoggled Q P p = (λ q → (λ _ → p) , (λ _ → q)) , (λ v → pr₂ v p)

  toggled-truth : (Q : Stable-Proposition (double-negation-modality dn)) →
    Stable-Proposition.carrier (biconditional Q (truth dn)) →
    Stable-Proposition.carrier Q
  toggled-truth Q w = pr₂ w (lift ⋆)

  truth-toggled : (Q : Stable-Proposition (double-negation-modality dn)) →
    Stable-Proposition.carrier Q →
    Stable-Proposition.carrier (biconditional Q (truth dn))
  truth-toggled Q q = (λ _ → lift ⋆) , (λ _ → q)

  -- Being a proposition and being stable are propositions, so a stable
  -- proposition is determined by its carrier.
  identified-by-carriers :
    (P Q : Stable-Proposition (double-negation-modality dn)) →
    Stable-Proposition.carrier P ＝ Stable-Proposition.carrier Q → P ＝ Q
  identified-by-carriers
    record
      { carrier = X ; carrier-is-proposition = h ; carrier-is-stable = s }
    record
      { carrier = .X ; carrier-is-proposition = h′ ; carrier-is-stable = s′ }
    refl =
    ap₂
      (λ k t → record
        { carrier = X ; carrier-is-proposition = k ; carrier-is-stable = t })
      (being-a-proposition-is-a-proposition extensionality X h h′)
      (Π-is-proposition (extensionality (¬ ¬ X) (λ _ → X)) (λ _ → h) s s′)

------------------------------------------------------------------------
-- Under propositional extensionality

-- Maps both ways between the carriers, two propositions, identify them.

module _ {ℓ : Level} (dn : (X : Set ℓ) → FunExt (¬ X) (λ _ → 𝟘))
  (extensionality : (X : Set ℓ) (Y : X → Set ℓ) → FunExt X Y)
  (propositional-extensionality : Propositional-Extensionality ℓ) where

  stable-propositions-are-identified :
    (P Q : Stable-Proposition (double-negation-modality dn)) →
    (Stable-Proposition.carrier P → Stable-Proposition.carrier Q) →
    (Stable-Proposition.carrier Q → Stable-Proposition.carrier P) → P ＝ Q
  stable-propositions-are-identified P Q to from =
    identified-by-carriers dn extensionality P Q
      (propositional-extensionality (Stable-Proposition.carrier P)
        (Stable-Proposition.carrier Q)
        (Stable-Proposition.carrier-is-proposition P)
        (Stable-Proposition.carrier-is-proposition Q) to from)

  -- Mathematical shape: Q ⇔ (Q ⇔ P) ＝ P.
  toggling-is-an-involution :
    (Q P : Stable-Proposition (double-negation-modality dn)) →
    biconditional dn extensionality Q (biconditional dn extensionality Q P)
      ＝ P
  toggling-is-an-involution Q P = stable-propositions-are-identified
    (biconditional dn extensionality Q (biconditional dn extensionality Q P))
    P (toggled-twice dn extensionality Q P) (untoggled dn extensionality Q P)

  stable-propositions-form-a-set :
    is-set (Stable-Proposition (double-negation-modality dn))
  stable-propositions-form-a-set P = identifications-from
    (λ Q →
      (Stable-Proposition.carrier P → Stable-Proposition.carrier Q) ×
      (Stable-Proposition.carrier Q → Stable-Proposition.carrier P))
    ((λ p → p) , (λ p → p))
    (λ Q e → stable-propositions-are-identified P Q (pr₁ e) (pr₂ e))
    (λ Q → Stable-Proposition.carrier-is-proposition
      (biconditional dn extensionality P Q))
