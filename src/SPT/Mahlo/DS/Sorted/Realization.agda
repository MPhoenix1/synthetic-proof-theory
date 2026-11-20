{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.DS.Sorted.Realization where

-- Small algebras of descriptions with outputs in Sort ℓ O from closures of
-- the two-sorted family. The frontier operator of γ (`operator`) returns,
-- at a family of names, the type of shapes of the frontier description
-- over it as a name, with the value of each. A closure of it names every
-- path's value (`available`); readiness passes through σ, and through δ
-- by extending families with the actual assignment (`sigma`, `delta`).
-- `compile` then sends every shape over the whole carrier to a code, with
-- its law (`compile-β`), so every such closure is a small algebra of γ
-- (`algebra`, `law`), and a Mahlo reflection of the two-sorted family gives
-- one (`reflected-algebra`, `reflected-law`). No extensionality. A copy of
-- Realization for the two-sorted family.

open import SPT.Base
import SPT.Mahlo.Specification as Specification

open import SPT.IR.Algebra using (Algebra; Law)
open import SPT.IR.Description using
  (Desc; ι; σ; δ; indexed; index; Shape; Mark)
open import SPT.Mahlo.DS.Sorted using (Sort; decode; formers)
import SPT.Mahlo.DS.Sorted.Family as Families
import SPT.Mahlo.DS.Sorted.Frontier as Frontier

------------------------------------------------------------------------
-- The frontier operator

operator :
  {ℓ κ : Level} {O : Set κ} → Desc {s = ℓ} (Sort ℓ O)
  → Specification.Operator (decode ℓ O)
operator {ℓ} {κ} {O} γ F =
  inl
    (Shape (Frontier.description γ)
      (indexed (decode ℓ O (pr₁ F)) (pr₂ F))) ,
  Mark (Frontier.description γ) (indexed (decode ℓ O (pr₁ F)) (pr₂ F))

------------------------------------------------------------------------
-- Readiness

Available :
  {ℓ κ : Level} {O : Set κ} {Ψ : Specification.Operator (decode ℓ O)}
  {K : Set ℓ} (L : Specification.Closure (formers ℓ O) Ψ K)
  → Desc {s = ℓ} (Sort ℓ O) → Set (lsuc ℓ ⊔ κ)
Available {ℓ} {κ} {O} L S =
  (F : Specification.Family
    (Specification.Decode (decode ℓ O) (Specification.Closure.interpret L)))
  (p : Frontier.Path S (Families.view L F))
  → Specification.Name (Specification.Closure.interpret L)
      (Frontier.value S (Families.view L F) p)

available :
  {ℓ κ : Level} {O : Set κ} (γ : Desc {s = ℓ} (Sort ℓ O)) {K : Set ℓ}
  (L : Specification.Closure (formers ℓ O) (operator γ) K)
  → Available L γ
available γ L F p =
  pr₁
    ( Families.action L F
        (lift ₀ , Frontier.argument γ (Families.view L F) p)) ,
  ( pr₂
      ( Families.action L F
          (lift ₀ , Frontier.argument γ (Families.view L F) p))
  ∙ Frontier.argument-β γ (Families.view L F) p)

sigma :
  {ℓ κ : Level} {O : Set κ} {Ψ : Specification.Operator (decode ℓ O)}
  {K : Set ℓ} (L : Specification.Closure (formers ℓ O) Ψ K) {A : Set ℓ}
  (H : A → Desc {s = ℓ} (Sort ℓ O))
  → Available L (σ A H) → (a : A) → Available L (H a)
sigma L H ready a F p = ready F (inr (a , p))

-- The arity of δ is named at the root path over the unit family; its
-- decoded name identity gives the extension by the assignment q.

delta :
  {ℓ κ : Level} {O : Set κ} {Ψ : Specification.Operator (decode ℓ O)}
  {K : Set ℓ} (L : Specification.Closure (formers ℓ O) Ψ K) {A : Set ℓ}
  (H : (A → Sort ℓ O) → Desc {s = ℓ} (Sort ℓ O))
  → Available L (δ A H) → (q : A → K)
  → Available L (H (λ x → Specification.Closure.interpret L (q x)))
delta {ℓ} {κ} {O} L H ready q F p =
  let arity = ready (Families.unit L) (inl (lift ⋆))
      extension =
        Families.extend L (pr₁ arity) (ap (decode ℓ O) (pr₂ arity)) q F
      enlarged = Families.view L (Families.Extension.family extension)
      changed =
        Frontier.change
          (H (λ x → Specification.Closure.interpret L (q x)))
          (Families.Extension.right-β extension ⁻¹) p
      mapped =
        Frontier.map (H (λ x → Specification.Closure.interpret L (q x)))
          (index enlarged) (Families.Extension.right extension) changed
      moved = ap H (Families.Extension.left-β extension ⁻¹)
      named =
        ready (Families.Extension.family extension)
          ( inr
              ( Families.Extension.left extension ,
                Frontier.shift enlarged moved mapped))
  in
  pr₁ named ,
  ( pr₂ named
  ∙ ( Frontier.shift-β enlarged moved mapped
    ∙ ( Frontier.map-β (H (λ x → Specification.Closure.interpret L (q x)))
          (index enlarged) (Families.Extension.right extension) changed
      ∙ Frontier.change-β
          (H (λ x → Specification.Closure.interpret L (q x)))
          (Families.Extension.right-β extension ⁻¹) p)))

------------------------------------------------------------------------
-- Compilation

compile :
  {ℓ κ : Level} {O : Set κ} {Ψ : Specification.Operator (decode ℓ O)}
  {K : Set ℓ} (L : Specification.Closure (formers ℓ O) Ψ K)
  (S : Desc {s = ℓ} (Sort ℓ O)) → Available L S
  → Shape S (indexed K (Specification.Closure.interpret L)) → K
compile L (ι e) ready _ = pr₁ (ready (Families.unit L) (lift ⋆))
compile L (σ A H) ready (a , z) = compile L (H a) (sigma L H ready a) z
compile L (δ A H) ready (q , z) =
  compile L (H (λ x → Specification.Closure.interpret L (q x)))
    (delta L H ready q) z

compile-β :
  {ℓ κ : Level} {O : Set κ} {Ψ : Specification.Operator (decode ℓ O)}
  {K : Set ℓ} (L : Specification.Closure (formers ℓ O) Ψ K)
  (S : Desc {s = ℓ} (Sort ℓ O)) (ready : Available L S)
  (z : Shape S (indexed K (Specification.Closure.interpret L)))
  → Specification.Closure.interpret L (compile L S ready z)
    ＝ Mark S (indexed K (Specification.Closure.interpret L)) z
compile-β L (ι e) ready _ = pr₂ (ready (Families.unit L) (lift ⋆))
compile-β L (σ A H) ready (a , z) =
  compile-β L (H a) (sigma L H ready a) z
compile-β L (δ A H) ready (q , z) =
  compile-β L (H (λ x → Specification.Closure.interpret L (q x)))
    (delta L H ready q) z

------------------------------------------------------------------------
-- Small algebras

algebra :
  {ℓ κ : Level} {O : Set κ} (γ : Desc {s = ℓ} (Sort ℓ O)) {K : Set ℓ}
  (L : Specification.Closure (formers ℓ O) (operator γ) K)
  → Algebra ℓ γ
algebra γ {K} L = record
  { K = K
  ; value = Specification.Closure.interpret L
  ; operation = compile L γ (available γ L)
  }

law :
  {ℓ κ : Level} {O : Set κ} (γ : Desc {s = ℓ} (Sort ℓ O)) {K : Set ℓ}
  (L : Specification.Closure (formers ℓ O) (operator γ) K)
  → Law (algebra γ L)
law γ L = compile-β L γ (available γ L)

reflected-algebra :
  {ℓ κ : Level} {O : Set κ} → Specification.Mahlo (formers ℓ O)
  → (γ : Desc {s = ℓ} (Sort ℓ O)) → Algebra ℓ γ
reflected-algebra reflections γ =
  algebra γ
    ( Specification.Reflection.closure
        (Specification.Mahlo.reflect reflections (operator γ)))

reflected-law :
  {ℓ κ : Level} {O : Set κ} (reflections : Specification.Mahlo (formers ℓ O))
  (γ : Desc {s = ℓ} (Sort ℓ O)) → Law (reflected-algebra reflections γ)
reflected-law reflections γ =
  law γ
    ( Specification.Reflection.closure
        (Specification.Mahlo.reflect reflections (operator γ)))
