{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.SelfNaming where

-- A family of types closed under W has no type with its own index as a retract
-- (`no-retract-of-the-names`), so it names no type isomorphic to its index
-- (`no-name-of-the-names`). A retraction makes some tree over the family one of
-- its own subtrees, which the paradox of trees refutes. `Has-Trees` is closure
-- under W, up to isomorphism. For the same reason no W-type is isomorphic to
-- one of its own branchings (`no-branching-is-the-trees`).

open import SPT.Base
open import SPT.Foundation.Isomorphisms using
  (_≅_; forward; backward; forward-backward)
open import SPT.Foundation.Tree.W using (W; sup)
open import SPT.Mahlo.Paradox using (not-own-member)

module _ {ℓ : Level} (c : Set ℓ) (b : c → Set ℓ) where

  -- Mathematical shape: every W over a family of the codes has a code.
  Has-Trees : Set ℓ
  Has-Trees = (a : c) (f : b a → c) →
    Σ c (λ t → b t ≅ W (b a) (λ x → b (f x)))

  -- Mathematical shape: c is no retract of any b a.
  no-retract-of-the-names : Has-Trees → (a : c) (r : b a → c) (s : c → b a) →
    ((x : c) → r (s x) ＝ x) → 𝟘
  no-retract-of-the-names trees a r s rs =
    let t = pr₁ (trees a r)
        T = pr₂ (trees a r)
        x₀ = s t
        e = rs t
        g = λ (z : b (r x₀)) → forward T (transport b e z)
        ω = sup x₀ g
    in not-own-member ω
         ( transport b (e ⁻¹) (backward T ω) ,
           ( ap (forward T) (back-and-forth-transport b e (backward T ω))
           ∙ forward-backward T ω))

  -- Mathematical shape: no b a is isomorphic to c.
  no-name-of-the-names : Has-Trees → (a : c) → b a ≅ c → 𝟘
  no-name-of-the-names trees a E =
    no-retract-of-the-names trees a (forward E) (backward E)
      (forward-backward E)

------------------------------------------------------------------------
-- No branching is the tree type

module _ {ℓ : Level} (X : Set ℓ) (r : X → Set ℓ) where

  -- Mathematical shape: no r a is isomorphic to W X r.
  no-branching-is-the-trees : (a : X) → r a ≅ W X r → 𝟘
  no-branching-is-the-trees a E =
    not-own-member (sup a (forward E))
      (backward E (sup a (forward E)) , forward-backward E (sup a (forward E)))
