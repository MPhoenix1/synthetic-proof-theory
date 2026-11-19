{-# OPTIONS --safe --without-K #-}

module SPT.Foundation.Size where

-- A type is small at a level when it is equivalent to a type of that level
-- (`is-small`, after TypeTopology's UF.Size):
--
--   is-small ℓ X = Σ (K : Set ℓ). Equivalence K X.
--
-- Under univalence at that level and function extensionality this is a
-- proposition (`being-small-is-proposition`): two small presentations are
-- identified along the identification of their carriers that univalence
-- gives.

open import SPT.Base
open import SPT.Foundation.Equivalences using (equivalences-with-one-map)
open import SPT.Foundation.Contractible using (is-contractible)
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.Extensionality.Levels using (funext-below)
open import SPT.Foundation.Fibers using (fiber)
open import SPT.Foundation.Isomorphisms using
  (forward-backward; ≅-sym; ≅-trans)
open import SPT.Foundation.Propositions using (is-proposition)
open import SPT.Foundation.Univalence using
  ( Equivalence; is-univalent; equivalence-to-isomorphism; isotoid
  ; transport-isotoid-⁻¹)

------------------------------------------------------------------------
-- Small types

is-small : {κ : Level} (ℓ : Level) → Set κ → Set (lsuc ℓ ⊔ κ)
is-small ℓ X = Σ (Set ℓ) (λ K → Equivalence K X)

-- The map of an equivalence transported along an identification of its
-- domain is the map after transport back.
map-after-transport : {ℓ κ : Level} {K K′ : Set ℓ} {X : Set κ} (p : K ＝ K′)
  (e : Equivalence K X) (k : K′) →
  pr₁ (transport (λ Z → Equivalence Z X) p e) k
    ＝ pr₁ e (transport (λ Z → Z) (p ⁻¹) k)
map-after-transport refl e k = refl

------------------------------------------------------------------------
-- Being small is a proposition

module _ {ℓ κ : Level}
  (funext : (A : Set (ℓ ⊔ κ)) (B : A → Set (ℓ ⊔ κ)) → FunExt A B) where

  being-small-is-proposition : is-univalent ℓ → (X : Set κ) →
    is-proposition (is-small ℓ X)
  being-small-is-proposition u X (K , e) (K′ , e′) =
    let E = equivalence-to-isomorphism e
        E′ = equivalence-to-isomorphism e′
        F = ≅-trans E (≅-sym E′)
        p = isotoid (u K K′) F
        d = transport (λ Z → Equivalence Z X) p e
    in to-Σ-＝ p
         ( equivalences-with-one-map d e′
             ( funext-below (ℓ ⊔ κ) funext X
                 (λ b → is-contractible (fiber (pr₁ d) b)))
             (λ b c → funext (fiber (pr₁ d) b) (λ x → c ＝ x))
             ( funext-below (ℓ ⊔ κ) funext K′ (λ _ → X) (pr₁ d) (pr₁ e′)
                 ( λ k →
                     map-after-transport p e k
                     ∙ ( ap (pr₁ e) (transport-isotoid-⁻¹ (u K K′) F k)
                       ∙ forward-backward E (pr₁ e′ k)))))
