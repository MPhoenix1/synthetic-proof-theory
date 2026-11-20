{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Paradox where

-- The paradox of trees. A tree is a member of another when it is one of its
-- subtrees, and no tree is a member of itself (`not-own-member`). If a family
-- r over a type X of a universe has a section s of all the types of that
-- universe, then W X r has a name s (W X r), and the tree over that name
-- whose subtrees are its branches is one of its own subtrees. So no type of
-- a universe has that universe as a retract (`no-retraction`), and none is
-- isomorphic to it, lifted or not (`no-isomorphism-onto-universe`,
-- `no-lifted-isomorphism-onto-universe`).

open import SPT.Base
open import SPT.Foundation.Isomorphisms using
  (_≅_; forward; backward; forward-backward; ≅-trans)
open import SPT.Foundation.Lifting using (lifting-is-isomorphism)
open import SPT.Foundation.Tree.W using (W; sup; induction)

------------------------------------------------------------------------
-- Membership among trees

module _ {ℓ : Level} {X : Set ℓ} {r : X → Set ℓ} where

  Member : W X r → W X r → Set ℓ
  Member x (sup a f) = Σ (r a) (λ b → f b ＝ x)

  not-own-member : (w : W X r) → Member w w → 𝟘
  not-own-member =
    induction (λ w → Member w w → 𝟘)
      ( λ a f below m →
          below (pr₁ m) (transport (λ z → Member z z) (pr₂ m ⁻¹) m))

------------------------------------------------------------------------
-- No universe is a retract of one of its types

no-retraction : {ℓ : Level} (X : Set ℓ) (r : X → Set ℓ) (s : Set ℓ → X) →
  ((A : Set ℓ) → r (s A) ＝ A) → 𝟘
no-retraction X r s law =
  let e = law (W X r)
      ω = sup (s (W X r)) (transport (λ Y → Y) e)
  in not-own-member ω
       ( transport (λ Y → Y) (e ⁻¹) ω
       , back-and-forth-transport (λ Y → Y) e ω)

no-isomorphism-onto-universe : {ℓ : Level} (X : Set ℓ) → X ≅ Set ℓ → 𝟘
no-isomorphism-onto-universe X e =
  no-retraction X (forward e) (backward e) (forward-backward e)

-- Mathematical shape: no Lift X, for X in Set ℓ, is isomorphic to Set ℓ.
no-lifted-isomorphism-onto-universe : {ℓ : Level} (ℓ′ : Level)
  (X : Set ℓ) → Lift ℓ′ X ≅ Set ℓ → 𝟘
no-lifted-isomorphism-onto-universe ℓ′ X e =
  no-isomorphism-onto-universe X (≅-trans (lifting-is-isomorphism ℓ′ X) e)
