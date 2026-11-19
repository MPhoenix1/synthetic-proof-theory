{-# OPTIONS --safe --without-K #-}

module SPT.Foundation.Propositions.Extensionality where

-- Propositional extensionality at one level: propositions with maps both
-- ways are identified (`Propositional-Extensionality`). It is the part of
-- univalence about propositions, and univalence at the level gives it
-- (`univalence-gives-propositional-extensionality`), maps both ways between
-- propositions being inverse to each other.

open import SPT.Base
open import SPT.Foundation.Propositions using (is-proposition)
open import SPT.Foundation.Univalence using (is-univalent; isotoid)

-- Mathematical shape: Π (P Q : Set ℓ). P, Q propositions → (P ⇔ Q) → P ＝ Q.
Propositional-Extensionality : (ℓ : Level) → Set (lsuc ℓ)
Propositional-Extensionality ℓ =
  (P Q : Set ℓ) → is-proposition P → is-proposition Q →
  (P → Q) → (Q → P) → P ＝ Q

univalence-gives-propositional-extensionality : {ℓ : Level} →
  is-univalent ℓ → Propositional-Extensionality ℓ
univalence-gives-propositional-extensionality u P Q h k to from =
  isotoid (u P Q) (record
    { forward = to
    ; backward = from
    ; backward-forward = λ p → h (from (to p)) p
    ; forward-backward = λ q → k (to (from q)) q
    })
