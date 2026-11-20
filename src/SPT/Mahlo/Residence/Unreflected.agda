{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Residence.Unreflected where

-- A least closure is not Mahlo. Let L be a least closure of a Tarski family
-- under the formers and an operator, on a small carrier A, so its own codes
-- form a family (`child-formers L`) with L's inner operator. A reflection
-- of that family for its own operator is a closure K on the decoding of one
-- of its codes; since L is least, K names every code of L (`covering`,
-- `covers`, by the names of formed codes). So the codes are a retract of
-- one of their decodings. When trees decode to trees up to similarity this
-- is impossible: the tree code over the retraction has a tree of all its
-- trees, similar to one of its own branches (`no-retract`, by `unfounded`).
-- Hence no least closure reflects its own operator (`unreflected`), none is
-- Mahlo (`not-mahlo`), and no absorbed reflection is
-- (`absorbed-not-mahlo`). Function extensionality at the level of the codes
-- joins the branches.

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Mahlo.Specification using
  (Operator; Formers; Name; Closure; Reflection; Mahlo)
open import SPT.Foundation.Tree.W using (W; sup; top; branch)
open import SPT.Mahlo.Decoding using (child-formers)
open import SPT.Mahlo.Retraction using
  (Similar; Unfolding; Retracts; inherited-retracts)
open import SPT.Mahlo.Residence.Absorption using
  (Methods; Induction; Absorbed)
open import SPT.Mahlo.Residence.Names using
  (realized-family; former-name; result-name; branch-name; identity-name)

------------------------------------------------------------------------
-- Well-founded trees

module _ {α β : Level} {A : Set α} {B : A → Set β} where

  -- A branch v of sup x f similar to sup x f has a branch similar to v.
  descend : (x : A) (f : B x → W A B) (i : B x) (v : W A B) → f i ＝ v →
    Similar v (sup x f) →
    ((j : B (top v)) → Similar (branch v j) v → 𝟘) → 𝟘
  descend x f i (sup x′ f′) e s below =
    below (transport B (pr₁ s ⁻¹) i)
      ( transport (Similar (f′ (transport B (pr₁ s ⁻¹) i))) e
          ( transport (λ k → Similar (f′ (transport B (pr₁ s ⁻¹) i)) (f k))
              (back-and-forth-transport B (pr₁ s) i)
              (pr₂ s (transport B (pr₁ s ⁻¹) i))))

  -- No tree is similar to one of its branches.
  unfounded : (w : W A B) (i : B (top w)) → Similar (branch w i) w → 𝟘
  unfounded (sup x f) i s = descend x f i (f i) refl s (unfounded (f i))

------------------------------------------------------------------------
-- The paradox of trees, up to similarity

-- Mathematical shape: no code c has D c retracting onto the codes, when trees
-- decode to trees up to similarity.

module _ {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} where

  no-retract : (Q : Formers C D) → Retracts Q → (c : C) (r : D c → C)
    (s : C → D c) → ((a : C) → r (s a) ＝ a) → 𝟘
  no-retract Q R c r s rs =
    let u = Retracts.tree R c r
        rt = rs (Formers.tree Q (c , r))
        -- The tree whose branches are all trees over (D c , D ∘ r).
        whole : W (D c) (λ x → D (r x))
        whole = sup (s (Formers.tree Q (c , r)))
          (λ e → Unfolding.out u (transport D rt e))
    in unfounded whole (transport D (rt ⁻¹) (Unfolding.into u whole))
         ( transport (λ v → Similar (Unfolding.out u v) whole)
             (back-and-forth-transport D rt (Unfolding.into u whole) ⁻¹)
             (Unfolding.out-into u whole))

------------------------------------------------------------------------
-- A least closure does not reflect its own operator

module _ {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} {Q : Formers C D}
  {Ψ : Operator D} {A : Set ℓ} where

  -- A closure K of L's own family names every code of L, by L's induction:
  -- each method is the name of a formed code in K.
  covering : (funext : (X : Set ℓ) (B : X → Set ℓ) → FunExt X B)
    (L : Closure Q Ψ A) {X : Set ℓ}
    (K : Closure (child-formers L) (Closure.inner L) X) →
    Methods L (λ a → Name (Closure.interpret K) a)
  covering funext L K = record
    { on-empty = Closure.empty K
    ; on-unit = Closure.unit K
    ; on-two = Closure.two K
    ; on-natural = Closure.natural K
    ; on-product = λ φ head branches →
        former-name (child-formers L) (Closure.inner L) K
          (Formers.product (child-formers L)) (Closure.product K)
          ( realized-family (child-formers L) (Closure.inner L)
              (λ Y → funext Y (λ _ → A)) K (pr₂ φ) head branches)
    ; on-sum = λ φ head branches →
        former-name (child-formers L) (Closure.inner L) K
          (Formers.sum (child-formers L)) (Closure.sum K)
          ( realized-family (child-formers L) (Closure.inner L)
              (λ Y → funext Y (λ _ → A)) K (pr₂ φ) head branches)
    ; on-tree = λ φ head branches →
        former-name (child-formers L) (Closure.inner L) K
          (Formers.tree (child-formers L)) (Closure.tree K)
          ( realized-family (child-formers L) (Closure.inner L)
              (λ Y → funext Y (λ _ → A)) K (pr₂ φ) head branches)
    ; on-identity = λ a x y head →
        identity-name (child-formers L) (Closure.inner L) K head x y
    ; on-result = λ φ head branches →
        result-name (child-formers L) (Closure.inner L) K
          ( realized-family (child-formers L) (Closure.inner L)
              (λ Y → funext Y (λ _ → A)) K (pr₂ φ) head branches)
    ; on-branch = λ φ y head branches →
        branch-name (child-formers L) (Closure.inner L) K
          ( realized-family (child-formers L) (Closure.inner L)
              (λ Y → funext Y (λ _ → A)) K (pr₂ φ) head branches)
          y
    }

  covers : (funext : (X : Set ℓ) (B : X → Set ℓ) → FunExt X B)
    (L : Closure Q Ψ A) → Induction L ℓ → {X : Set ℓ}
    (K : Closure (child-formers L) (Closure.inner L) X) (a : A) →
    Name (Closure.interpret K) a
  covers funext L induction K =
    Induction.induction induction (λ a → Name (Closure.interpret K) a)
      (covering funext L K)

  unreflected : Retracts Q →
    (funext : (X : Set ℓ) (B : X → Set ℓ) → FunExt X B)
    (L : Closure Q Ψ A) → Induction L ℓ →
    Reflection (child-formers L) (Closure.inner L) → 𝟘
  unreflected R funext L induction reflection =
    no-retract (child-formers L) (inherited-retracts R L)
      (Reflection.carrier reflection)
      (Closure.interpret (Reflection.closure reflection))
      (λ a → pr₁ (covers funext L induction (Reflection.closure reflection) a))
      (λ a → pr₂ (covers funext L induction (Reflection.closure reflection) a))

  not-mahlo : Retracts Q →
    (funext : (X : Set ℓ) (B : X → Set ℓ) → FunExt X B)
    (L : Closure Q Ψ A) → Induction L ℓ → Mahlo (child-formers L) → 𝟘
  not-mahlo R funext L induction mahlo =
    unreflected R funext L induction (Mahlo.reflect mahlo (Closure.inner L))

------------------------------------------------------------------------
-- Absorbed reflections

module _ {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} {Q : Formers C D}
  {Ψ : Operator D} where

  -- The child of an absorbed reflection is not Mahlo.
  absorbed-not-mahlo : Retracts Q →
    (funext : (X : Set ℓ) (B : X → Set ℓ) → FunExt X B)
    (absorbed : Absorbed Q Ψ ℓ) →
    Mahlo (child-formers (Reflection.closure (Absorbed.reflection absorbed))) →
    𝟘
  absorbed-not-mahlo R funext absorbed =
    not-mahlo R funext (Reflection.closure (Absorbed.reflection absorbed))
      (Absorbed.induction absorbed)
